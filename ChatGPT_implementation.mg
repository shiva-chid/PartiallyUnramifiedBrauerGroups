// ChatGPT_implementation_v4.mg
//
// Prototype Magma implementation for partially ramified Brauer pairs over Q.
// Coefficients for the geometric part are F_2 = Z/2Z.
//
// Main entry point:
//     R := PartiallyRamifiedBrauerPairs(G, Creps);
// where G is a finite Magma group and Creps is a sequence of representatives
// for the conjugacy classes C_i.
//
// Output R is a record.  Important fields:
//   R`GeometricBasisH2          basis for the residue-kernel inside H^2(G,F_2)
//   R`GeometricExtensions       explicit central extensions F_2 -> E -> G
//   R`GeometricMarkings         marking conjugacy classes D_i in E
//   R`AlgebraicBasis            quotient basis for algebraic residues
//   R`GeometricResidueMatrix    step 4 residues
//   R`AlgebraicResidueMatrix    step 5 residues
//   R`MatchBasis                F_2-basis for all matching pairs
//   R`MatchingPairs             enumerated pairs, if small enough
//
// This version fixes the missing power-transition rows and avoids the non-portable intrinsic ConjugacyClass(G,g) by using
// an explicit conjugation loop.  It also treats CohomologyGroup(CM,n) whether
// Magma returns it as an abelian group or as a vector space.
//
// v4 also corrects the algebraic side.  The previous versions used
// Hom(U_2, Ghat[2]) as if the U_2-action on Ghat[2^infty] were trivial.
// The correct algebraic residue data is obtained from 1-cocycles with values
// in Ghat[2^infty], modulo coboundaries.  On the F_2-valued residue level this
// means quotienting by coboundaries coming from 2*Ghat[4].

// -----------------------------------------------------------------------------
// Small utilities
// -----------------------------------------------------------------------------

function IsTwoPower(n)
    if n le 0 then
        return false;
    end if;
    while (n mod 2) eq 0 do
        n div:= 2;
    end while;
    return n eq 1;
end function;

function SeqSumInt(S)
    s := 0;
    for x in S do
        s +:= x;
    end for;
    return s;
end function;

function UnitMulMod(a,b,N)
    r := (a*b) mod N;
    if r eq 0 then
        r := N;
    end if;
    return r;
end function;

function UnitInvMod(a,N)
    aa := a mod N;
    for b in [1..N] do
        if GCD(b,N) eq 1 and ((aa*b - 1) mod N) eq 0 then
            return b;
        end if;
    end for;
    error "UnitInvMod: input is not a unit modulo N";
end function;

function UnitOrderMod(a,N)
    if GCD(a,N) ne 1 then
        error "UnitOrderMod: input is not a unit modulo N";
    end if;
    b := a mod N;
    if b eq 0 then
        b := N;
    end if;
    c := b;
    r := 1;
    while c ne 1 do
        c := (c*b) mod N;
        r +:= 1;
    end while;
    return r;
end function;

function ClassSet(G,g)
    // Version-safe replacement for the unavailable ConjugacyClass(G,g).
    // Magma supports group iteration for finite groups; x^-1*g*x is the
    // conjugate of g by x.
    return { x^-1*g*x : x in G };
end function;

function ClassPowerSet(G,C,k)
    return { x^k : x in C };
end function;

function ClassIndex(Csets, D)
    for j in [1..#Csets] do
        if D eq Csets[j] then
            return j;
        end if;
    end for;
    return 0;
end function;

function PowerTransitionRows(G, Csets, U2)
    // Rows for arithmetic residues.  A row <i,k,j> means C_i^k=C_j.
    // It is important to include transitions with i ne j: these enforce
    // Galois/invertible-power compatibility between different conjugacy
    // classes in the same orbit.
    rows := [];
    for i in [1..#Csets] do
        for k in U2 do
            j := ClassIndex(Csets, ClassPowerSet(G, Csets[i], k));
            if j eq 0 then
                error Sprintf("PowerTransitionRows: class %o powered by %o is not among the supplied classes.", i, k);
            end if;
            Append(~rows, <i,k,j>);
        end for;
    end for;
    return rows;
end function;

function CohomologyGroupGenerators(H)
    // Magma versions differ here: CohomologyGroup(CM,n) may be returned either
    // as an abstract abelian group or directly as a vector space over GF(2).
    // Avoid Order(H.i), since vector-space elements do not have group order.
    gens := [];
    for i in [1..Ngens(H)] do
        h := H.i;
        if h ne Parent(h)!0 then
            Append(~gens, h);
        end if;
    end for;
    return gens;
end function;

function BitOfModuleElt(v)
    // For the 1-dimensional GF(2)-module used below.
    return (Integers()!Eltseq(v)[1]) mod 2;
end function;

function BitSeq(v)
    return [ (Integers()!x) mod 2 : x in Eltseq(v) ];
end function;

function LinCombF2(basis, coeffs)
    s := Parent(basis[1])!0;
    for j in [1..#basis] do
        if ((Integers()!coeffs[j]) mod 2) eq 1 then
            s +:= basis[j];
        end if;
    end for;
    return s;
end function;

function ColumnKernel(A)
    // Magma vector spaces use row vectors; Nullspace(M) is {v : v*M=0}.
    // Hence this computes {x : A*x^t = 0} as a row-vector space.
    return Nullspace(Transpose(A));
end function;


function SpanBasisF2(vectors, dim)
    F := GF(2);
    B := [];
    for v0 in vectors do
        v := [ F!x : x in v0 ];
        if &and[ v[i] eq F!0 : i in [1..dim] ] then
            continue;
        end if;
        oldRank := (#B eq 0) select 0 else Rank(Matrix(F, #B, dim, &cat B));
        Btry := B cat [v];
        newRank := Rank(Matrix(F, #Btry, dim, &cat Btry));
        if newRank gt oldRank then
            Append(~B, v);
        end if;
    end for;
    return B;
end function;

function ComplementBasisF2(dim, subspaceBasis)
    F := GF(2);
    B := SpanBasisF2(subspaceBasis, dim);
    C := [];
    for i in [1..dim] do
        e := [ F!0 : j in [1..dim] ];
        e[i] := F!1;
        oldRank := (#B eq 0) select 0 else Rank(Matrix(F, #B, dim, &cat B));
        Btry := B cat [e];
        newRank := Rank(Matrix(F, #Btry, dim, &cat Btry));
        if newRank gt oldRank then
            Append(~B, e);
            Append(~C, e);
        end if;
    end for;
    return C;
end function;

function MatrixFromColumnVectorsF2(nrows, cols)
    F := GF(2);
    M := ZeroMatrix(F, nrows, #cols);
    for j in [1..#cols] do
        for i in [1..nrows] do
            M[i,j] := F!cols[j][i];
        end for;
    end for;
    return M;
end function;

function LinearCombinationOfColumns(M, coeffs)
    F := GF(2);
    v := ZeroMatrix(F, Nrows(M), 1);
    for j in [1..#coeffs] do
        if (F!coeffs[j]) eq F!1 then
            for i in [1..Nrows(M)] do
                v[i,1] +:= M[i,j];
            end for;
        end if;
    end for;
    return [ v[i,1] : i in [1..Nrows(M)] ];
end function;

function QuotientProjectionMatrixF2(n, relationValueBasis)
    // relationValueBasis is a list of row-vectors of length n spanning the
    // subspace by which the residue codomain should be quotiented.
    // The returned matrix P has rows spanning the annihilator, so P*r is a
    // coordinate vector for the image of r in the quotient.
    F := GF(2);
    Wbasis := SpanBasisF2(relationValueBasis, n);
    if #Wbasis eq 0 then
        return IdentityMatrix(F, n);
    end if;
    Wcols := MatrixFromColumnVectorsF2(n, Wbasis);
    Ann := Nullspace(Wcols);
    rows := [ BitSeq(v) : v in Basis(Ann) ];
    if #rows eq 0 then
        return ZeroMatrix(F, 0, n);
    end if;
    return Matrix(F, #rows, n, &cat rows);
end function;

function TwoCocycleBitFunction(CM, h2elt, G)
    t := TwoCocycle(CM, h2elt);
    e := Identity(G);
    c := BitOfModuleElt(t(<e,e>));

    // Normalize by subtracting the coboundary of the 1-cochain s with
    // s(e)=t(e,e), s(g)=0 otherwise.  In characteristic 2 this is addition.
    return function(g,h)
        sg := (g eq e) select c else 0;
        sh := (h eq e) select c else 0;
        sgh := (g*h eq e) select c else 0;
        return (BitOfModuleElt(t(<g,h>)) + sg + sh + sgh) mod 2;
    end function;
end function;

// -----------------------------------------------------------------------------
// Units modulo N and their maximal elementary quotient U_2/U_2^2
// -----------------------------------------------------------------------------

function U2Data(N)
    U := [ a : a in [1..N] | GCD(a,N) eq 1 ];
    U2 := [ a : a in U | IsTwoPower(UnitOrderMod(a,N)) ];
    Squares := { UnitMulMod(u,u,N) : u in U2 };

    function ProductMask(B, mask)
        p := 1;
        for j in [1..#B] do
            if ((mask div 2^(j-1)) mod 2) eq 1 then
                p := UnitMulMod(p, B[j], N);
            end if;
        end for;
        return p;
    end function;

    function InSpan(u,B)
        for mask in [0..2^#B-1] do
            p := ProductMask(B,mask);
            if UnitMulMod(u, UnitInvMod(p,N), N) in Squares then
                return true;
            end if;
        end for;
        return false;
    end function;

    B := [];
    for u in U2 do
        if not InSpan(u,B) then
            Append(~B,u);
        end if;
    end for;

    function Coordinates(u)
        for mask in [0..2^#B-1] do
            p := ProductMask(B,mask);
            if UnitMulMod(u, UnitInvMod(p,N), N) in Squares then
                return [ ((mask div 2^(j-1)) mod 2) : j in [1..#B] ];
            end if;
        end for;
        error "U2Data: coordinates not found";
    end function;

    RF := recformat< Modulus, U2, Squares, Basis, Coordinates >;
    return rec< RF | Modulus := N, U2 := U2, Squares := Squares,
                     Basis := B, Coordinates := Coordinates >;
end function;

// -----------------------------------------------------------------------------
// Input validation and N_i
// -----------------------------------------------------------------------------

function ValidateCAndComputeNi(G, Creps, U2, N)
    Csets := [ ClassSet(G,g) : g in Creps ];

    // Check that union C_i generates G.
    Ugens := {};
    for C in Csets do
        Ugens := Ugens join C;
    end for;
    UgensSeq := [ x : x in Ugens ];
    if sub< G | UgensSeq > ne G then
        return false, "The union of the supplied conjugacy classes does not generate G.", [], [];
    end if;

    // Check closure under invertible powers modulo |G|.
    unitsG := [ a : a in [1..#G] | GCD(a,#G) eq 1 ];
    for i in [1..#Csets] do
        for t in unitsG do
            D := ClassPowerSet(G, Csets[i], t);
            found := false;
            for j in [1..#Csets] do
                if D eq Csets[j] then
                    found := true;
                    break;
                end if;
            end for;
            if not found then
                return false,
                    Sprintf("The supplied classes are not closed under the invertible power t=%o on class %o.", t, i),
                    [], [];
            end if;
        end for;
    end for;

    // N_i = stabilizer of C_i in the 2-primary unit group modulo 2*#G.
    Nlist := [];
    for i in [1..#Csets] do
        Ni := [ k : k in U2 | ClassPowerSet(G, Csets[i], k) eq Csets[i] ];
        Append(~Nlist, Ni);
    end for;

    return true, "ok", Csets, Nlist;
end function;

// -----------------------------------------------------------------------------
// Cohomology setup and geometric residue kernel
// -----------------------------------------------------------------------------

function TrivialF2CohomologyModule(G)
    F := GF(2);
    mats := [ IdentityMatrix(F,1) : i in [1..Ngens(G)] ];
    M := GModule(G, mats);
    return CohomologyModule(G, M);
end function;

function GeometricResidueKernel(G, Creps, CM)
    F := GF(2);
    H2 := CohomologyGroup(CM,2);
    H2basis := CohomologyGroupGenerators(H2);
    twos := [ TwoCocycleBitFunction(CM, b, G) : b in H2basis ];

    nrows := SeqSumInt([ Ngens(Centralizer(G,g)) : g in Creps ]);
    A := ZeroMatrix(F, nrows, #H2basis);

    row := 0;
    for i in [1..#Creps] do
        gi := Creps[i];
        ZG := Centralizer(G, gi);
        for ell in [1..Ngens(ZG)] do
            h := ZG.ell;
            row +:= 1;
            for j in [1..#H2basis] do
                A[row,j] := F!((twos[j](gi,h) + twos[j](h,gi)) mod 2);
            end for;
        end for;
    end for;

    K := ColumnKernel(A);
    KbasisCoords := [ BitSeq(v) : v in Basis(K) ];
    KbasisH2 := [];
    for v in KbasisCoords do
        Append(~KbasisH2, LinCombF2(H2basis, v));
    end for;

    RF := recformat< H2, H2Basis, ResidueMatrix, Kernel, KernelBasisCoords, KernelBasisH2 >;
    return rec< RF | H2 := H2, H2Basis := H2basis, ResidueMatrix := A,
                     Kernel := K, KernelBasisCoords := KbasisCoords,
                     KernelBasisH2 := KbasisH2 >;
end function;

// -----------------------------------------------------------------------------
// Explicit central extension E_f = F_2 x_f G as a permutation group
// -----------------------------------------------------------------------------

function CentralExtensionFromH2(G, CM, h2elt)
    f := TwoCocycleBitFunction(CM, h2elt, G);
    Gelts := [ g : g in G ];
    idx := AssociativeArray();
    for i in [1..#Gelts] do
        idx[Gelts[i]] := i;
    end for;
    nG := #Gelts;
    eG := Identity(G);

    function PairIndex(a,g)
        return (a mod 2)*nG + idx[g];
    end function;

    function IndexPair(p)
        a := (p-1) div nG;
        i := ((p-1) mod nG) + 1;
        return a, Gelts[i];
    end function;

    S := Sym(2*nG);

    function LeftPerm(a,g)
        imgs := [];
        for p in [1..2*nG] do
            b,h := IndexPair(p);
            c := (a + b + f(g,h)) mod 2;
            Append(~imgs, PairIndex(c, g*h));
        end for;
        return S!imgs;
    end function;

    gens := [ LeftPerm(1,eG) ];
    gens cat:= [ LeftPerm(0,G.i) : i in [1..Ngens(G)] ];
    E := sub< S | gens >;
    z := E!LeftPerm(1,eG);

    function Lift(g)
        return E!LeftPerm(0,g);
    end function;

    function Projection(x)
        p0 := PairIndex(0,eG);
        q := p0^x;
        a,g := IndexPair(q);
        return g;
    end function;

    RF := recformat< E, z, Lift, Projection, CocycleBit, GElements >;
    return rec< RF | E := E, z := z, Lift := Lift, Projection := Projection,
                     CocycleBit := f, GElements := Gelts >;
end function;

// -----------------------------------------------------------------------------
// Marking and geometric arithmetic residue
// -----------------------------------------------------------------------------

function GeometricMarkingData(G, Creps, Ext)
    E := Ext`E;
    Lift := Ext`Lift;

    Dclasses := [];
    for gi in Creps do
        tg := Lift(gi);
        D := ClassSet(E, tg);
        Append(~Dclasses, D);
    end for;

    RF := recformat< Dclasses >;
    return rec< RF | Dclasses := Dclasses >;
end function;

function GeometricPowerResidueColumn(G, Creps, ResidueIndex, Ext)
    F := GF(2);
    E := Ext`E;
    z := Ext`z;
    Lift := Ext`Lift;
    vals := [];

    for row in ResidueIndex do
        i := row[1];
        k := row[2];
        j := row[3];
        lhs := Lift(Creps[i])^k;
        rhs := Lift(Creps[j]);
        if IsConjugate(E, lhs, rhs) then
            Append(~vals, F!0);
        elif IsConjugate(E, lhs, z*rhs) then
            Append(~vals, F!1);
        else
            error Sprintf("Geometric residue error on transition class %o --%o--> %o: powered lift lies in neither fibre conjugacy class.", i, k, j);
        end if;
    end for;
    return Vector(F, vals);
end function;

// -----------------------------------------------------------------------------
// Algebraic residue basis: H^1(U_2, Ghat[2^infty]) on the F_2 residue level
// -----------------------------------------------------------------------------

function HomZ4ReductionsInH1(G, CM, H1basis)
    // Return a basis, in H1basis-coordinates, for 2*Ghat[4] inside Ghat[2].
    // Concretely: enumerate homomorphisms G -> Z/4Z, reduce their values mod 2,
    // and express the resulting F_2-characters in the chosen H^1(G,F_2)-basis.
    F := GF(2);
    hdim := #H1basis;
    if hdim eq 0 then
        return [];
    end if;

    gens := [ G.i : i in [1..Ngens(G)] ];
    m := #gens;
    chars := [ OneCocycle(CM, b) : b in H1basis ];
    basisVals := [];
    for j in [1..hdim] do
        Append(~basisVals, [ BitOfModuleElt(chars[j](<gens[i]>)) : i in [1..m] ]);
    end for;

    function H1CoordinatesFromGeneratorValues(vals)
        for mask in [0..2^hdim-1] do
            test := [ 0 : i in [1..m] ];
            coords := [];
            for j in [1..hdim] do
                c := ((mask div 2^(j-1)) mod 2);
                Append(~coords, c);
                if c eq 1 then
                    for i in [1..m] do
                        test[i] := (test[i] + basisVals[j][i]) mod 2;
                    end for;
                end if;
            end for;
            if test eq vals then
                return coords;
            end if;
        end for;
        error "HomZ4ReductionsInH1: could not express a reduced Z/4-character in H1 coordinates";
    end function;

    function ExtendsToHomZ4(assign)
        e := Identity(G);
        A := AssociativeArray();
        A[e] := 0;

        for i in [1..m] do
            g := gens[i];
            v := assign[i] mod 4;
            if IsDefined(A, g) and A[g] ne v then
                return false, A;
            end if;
            A[g] := v;
        end for;

        stepGens := [];
        stepVals := [];
        for i in [1..m] do
            Append(~stepGens, gens[i]);
            Append(~stepVals, assign[i] mod 4);
            Append(~stepGens, gens[i]^-1);
            Append(~stepVals, (-assign[i]) mod 4);
        end for;

        queue := [ e ];
        for g in gens do
            if not (g in queue) then
                Append(~queue, g);
            end if;
        end for;

        head := 1;
        while head le #queue do
            x := queue[head];
            head +:= 1;
            vx := A[x];
            for t in [1..#stepGens] do
                y := x*stepGens[t];
                vy := (vx + stepVals[t]) mod 4;
                if IsDefined(A, y) then
                    if A[y] ne vy then
                        return false, A;
                    end if;
                else
                    A[y] := vy;
                    Append(~queue, y);
                end if;
            end for;
        end while;

        for x in G do
            if not IsDefined(A, x) then
                return false, A;
            end if;
        end for;
        return true, A;
    end function;

    possible := [];
    for i in [1..m] do
        Append(~possible, [ a : a in [0..3] | ((Order(gens[i])*a) mod 4) eq 0 ]);
    end for;

    reductions := [];
    procedure Recurse(pos, vals, ~reductions)
        if pos gt m then
            ok, A := ExtendsToHomZ4(vals);
            if ok then
                red := [ (A[gens[i]] mod 2) : i in [1..m] ];
                Append(~reductions, H1CoordinatesFromGeneratorValues(red));
            end if;
            return;
        end if;
        for a in possible[pos] do
            Recurse(pos+1, vals cat [a], ~reductions);
        end for;
    end procedure;

    Recurse(1, [], ~reductions);
    return SpanBasisF2(reductions, hdim);
end function;

function AlgebraicCoboundaryRelations(Udata, H1Image2Ghat4Basis, AlgBasis)
    // Coboundaries from an element psi in Ghat[4] have F_2-valued residue
    // k |-> ((k-1)/2 mod 2) * (2*psi).  Thus each eta=2*psi in 2*Ghat[4]
    // gives one relation in Hom(U_2,Ghat[2]).
    F := GF(2);
    Ubas := Udata`Basis;
    adim := #AlgBasis;
    rels := [];

    unitEpsilon := [ (((Ubas[a] - 1) div 2) mod 2) : a in [1..#Ubas] ];

    for eta in H1Image2Ghat4Basis do
        rel := [ F!0 : c in [1..adim] ];
        for col in [1..adim] do
            a := AlgBasis[col][1];
            j := AlgBasis[col][2];
            rel[col] := F!((unitEpsilon[a] * (Integers()!eta[j])) mod 2);
        end for;
        Append(~rels, rel);
    end for;

    return SpanBasisF2(rels, adim);
end function;

function AlgebraicResidueData(G, Creps, CM, Udata, ResidueIndex)
    F := GF(2);
    H1 := CohomologyGroup(CM,1);
    H1basis := CohomologyGroupGenerators(H1);
    chars := [ OneCocycle(CM, b) : b in H1basis ];

    chiVals := [];
    for j in [1..#H1basis] do
        Append(~chiVals, [ BitOfModuleElt(chars[j](<Creps[i]>)) : i in [1..#Creps] ]);
    end for;

    Ubas := Udata`Basis;
    RawAlgBasis := [ <a,j> : a in [1..#Ubas], j in [1..#H1basis] ];

    R := #ResidueIndex;
    RawA := ZeroMatrix(F, R, #RawAlgBasis);

    for rowno in [1..#ResidueIndex] do
        i := ResidueIndex[rowno][1];
        k := ResidueIndex[rowno][2];
        uk := Udata`Coordinates(k);
        for col in [1..#RawAlgBasis] do
            a := RawAlgBasis[col][1];
            j := RawAlgBasis[col][2];
            RawA[rowno,col] := F!((uk[a] * chiVals[j][i]) mod 2);
        end for;
    end for;

    H1Image2Ghat4Basis := HomZ4ReductionsInH1(G, CM, H1basis);
    AlgRelationBasis := AlgebraicCoboundaryRelations(Udata, H1Image2Ghat4Basis, RawAlgBasis);

    // Choose representatives for the quotient of the old algebraic coefficient
    // space by the coboundary relations.
    AlgQuotientBasisCoords := ComplementBasisF2(#RawAlgBasis, AlgRelationBasis);
    QuotA := ZeroMatrix(F, R, #AlgQuotientBasisCoords);
    for q in [1..#AlgQuotientBasisCoords] do
        col := LinearCombinationOfColumns(RawA, AlgQuotientBasisCoords[q]);
        for i in [1..R] do
            QuotA[i,q] := col[i];
        end for;
    end for;

    RelationResidueBasis := [];
    for rel in AlgRelationBasis do
        Append(~RelationResidueBasis, LinearCombinationOfColumns(RawA, rel));
    end for;
    RelationResidueBasis := SpanBasisF2(RelationResidueBasis, R);
    P := QuotientProjectionMatrixF2(R, RelationResidueBasis);
    QuotAProjected := P*QuotA;

    AlgQuotientBasis := [];
    for q in [1..#AlgQuotientBasisCoords] do
        Append(~AlgQuotientBasis, [ RawAlgBasis[c] : c in [1..#RawAlgBasis] | AlgQuotientBasisCoords[q][c] eq F!1 ]);
    end for;

    RF := recformat< H1, H1Basis, CharacterValuesOnC,
                     RawAlgebraicBasis, RawResidueMatrix,
                     H1Image2Ghat4BasisCoords, AlgebraicRelationBasisCoords,
                     AlgebraicRelationResidueBasis, ResidueQuotientProjection,
                     AlgebraicBasis, AlgebraicBasisCoords,
                     ResidueMatrix, ResidueMatrixBeforeProjection >;
    return rec< RF | H1 := H1, H1Basis := H1basis,
                     CharacterValuesOnC := chiVals,
                     RawAlgebraicBasis := RawAlgBasis,
                     RawResidueMatrix := RawA,
                     H1Image2Ghat4BasisCoords := H1Image2Ghat4Basis,
                     AlgebraicRelationBasisCoords := AlgRelationBasis,
                     AlgebraicRelationResidueBasis := RelationResidueBasis,
                     ResidueQuotientProjection := P,
                     AlgebraicBasis := AlgQuotientBasis,
                     AlgebraicBasisCoords := AlgQuotientBasisCoords,
                     ResidueMatrix := QuotAProjected,
                     ResidueMatrixBeforeProjection := QuotA >;
end function;

// -----------------------------------------------------------------------------
// Matching geometric and algebraic residues
// -----------------------------------------------------------------------------

function MatchResidues(GeoResidueMatrix, AlgResidueMatrix : MaxEnumerate := 4096)
    F := GF(2);
    R := Nrows(GeoResidueMatrix);
    gdim := Ncols(GeoResidueMatrix);
    adim := Ncols(AlgResidueMatrix);

    M := ZeroMatrix(F, R, gdim + adim);
    for i in [1..R] do
        for j in [1..gdim] do
            M[i,j] := GeoResidueMatrix[i,j];
        end for;
        for j in [1..adim] do
            M[i,gdim+j] := AlgResidueMatrix[i,j];
        end for;
    end for;

    K := ColumnKernel(M);
    Kbasis := Basis(K);
    KbasisSeq := [ BitSeq(v) : v in Kbasis ];

    pairs := [];
    enumerated := false;
    if 2^Dimension(K) le MaxEnumerate then
        enumerated := true;
        for mask in [0..2^Dimension(K)-1] do
            v := Vector(F, gdim+adim, [ F!0 : j in [1..gdim+adim] ]);
            for b in [1..Dimension(K)] do
                if ((mask div 2^(b-1)) mod 2) eq 1 then
                    v +:= Kbasis[b];
                end if;
            end for;
            s := BitSeq(v);
            Append(~pairs, < [ s[j] : j in [1..gdim] ],
                            [ s[gdim+j] : j in [1..adim] ] >);
        end for;
    end if;

    RF := recformat< CombinedResidueMatrix, MatchSpace, MatchBasis, MatchingPairs,
                     MatchingPairsEnumerated, GeometricDimension, AlgebraicDimension >;
    return rec< RF | CombinedResidueMatrix := M, MatchSpace := K,
                     MatchBasis := KbasisSeq, MatchingPairs := pairs,
                     MatchingPairsEnumerated := enumerated,
                     GeometricDimension := gdim, AlgebraicDimension := adim >;
end function;

// -----------------------------------------------------------------------------
// Main function
// -----------------------------------------------------------------------------

function PartiallyRamifiedBrauerPairs(G, Creps : MaxEnumerate := 4096, CheckInput := true)
    RF := recformat< Ok, Message, GOrder, Modulus, CRepresentatives, Csets,
                     U2Data, Ni, ResidueIndex, CM,
                     H2, H2Basis, GeometricResidueToH1Matrix,
                     GeometricKernelBasisCoords, GeometricBasisH2,
                     GeometricExtensions, GeometricMarkings, GeometricResidueMatrix,
                     H1, H1Basis, AlgebraicBasis, AlgebraicBasisCoords,
                     RawAlgebraicBasis, RawAlgebraicResidueMatrix,
                     H1Image2Ghat4BasisCoords, AlgebraicRelationBasisCoords,
                     AlgebraicRelationResidueBasis, ResidueQuotientProjection,
                     AlgebraicResidueMatrix, AlgebraicResidueMatrixBeforeProjection,
                     RawGeometricResidueMatrix, GeometricResidueMatrixBeforeProjection,
                     MatchBasis, MatchingPairs, MatchingPairsEnumerated,
                     MatchRecord >;

    if (#G mod 2) eq 1 then
        return rec< RF | Ok := true,
                         Message := "Odd order group: non-trivial 2-primary Brauer data is zero.",
                         GOrder := #G, Modulus := 2*#G,
                         CRepresentatives := Creps,
                         MatchingPairs := [ <[],[]> ],
                         MatchingPairsEnumerated := true,
                         MatchBasis := [] >;
    end if;

    N := 2*#G;
    Udata := U2Data(N);

    if CheckInput then
        ok, msg, Csets, Nlist := ValidateCAndComputeNi(G, Creps, Udata`U2, N);
        if not ok then
            return rec< RF | Ok := false, Message := msg, GOrder := #G,
                             Modulus := N, CRepresentatives := Creps >;
        end if;
    else
        Csets := [ ClassSet(G,g) : g in Creps ];
        Nlist := [];
        for i in [1..#Csets] do
            Append(~Nlist, [ k : k in Udata`U2 | ClassPowerSet(G, Csets[i], k) eq Csets[i] ]);
        end for;
    end if;

    // Residue rows must include all power transitions C_i^k=C_j, not just
    // stabilizers C_i^k=C_i.  Omitting i->j rows is the bug fixed in v3.
    ResidueIndex := PowerTransitionRows(G, Csets, Udata`U2);

    CM := TrivialF2CohomologyModule(G);

    // Step 2 and 3A: H^2 and geometric-residue kernel.
    GK := GeometricResidueKernel(G, Creps, CM);

    // Step 3B and 4: explicit central extensions, markings, and arithmetic residues.
    Exts := [];
    Marks := [];
    R := #ResidueIndex;
    GeoRes := ZeroMatrix(GF(2), R, #GK`KernelBasisH2);
    for j in [1..#GK`KernelBasisH2] do
        Ext := CentralExtensionFromH2(G, CM, GK`KernelBasisH2[j]);
        Append(~Exts, Ext);
        Append(~Marks, GeometricMarkingData(G, Creps, Ext));
        col := GeometricPowerResidueColumn(G, Creps, ResidueIndex, Ext);
        for r in [1..R] do
            GeoRes[r,j] := col[r];
        end for;
    end for;

    // Step 5: algebraic residue basis, with the coboundary quotient from 2*Ghat[4].
    Alg := AlgebraicResidueData(G, Creps, CM, Udata, ResidueIndex);

    // Project the geometric residue matrix to the same quotient residue codomain.
    GeoResProjected := Alg`ResidueQuotientProjection * GeoRes;

    // Step 6: matching pairs in the quotient codomain and quotient algebraic group.
    Match := MatchResidues(GeoResProjected, Alg`ResidueMatrix : MaxEnumerate := MaxEnumerate);

    return rec< RF | Ok := true, Message := "ok", GOrder := #G, Modulus := N,
                     CRepresentatives := Creps, Csets := Csets,
                     U2Data := Udata, Ni := Nlist, ResidueIndex := ResidueIndex,
                     CM := CM,
                     H2 := GK`H2, H2Basis := GK`H2Basis,
                     GeometricResidueToH1Matrix := GK`ResidueMatrix,
                     GeometricKernelBasisCoords := GK`KernelBasisCoords,
                     GeometricBasisH2 := GK`KernelBasisH2,
                     GeometricExtensions := Exts, GeometricMarkings := Marks,
                     RawGeometricResidueMatrix := GeoRes,
                     GeometricResidueMatrixBeforeProjection := GeoRes,
                     GeometricResidueMatrix := GeoResProjected,
                     H1 := Alg`H1, H1Basis := Alg`H1Basis,
                     AlgebraicBasis := Alg`AlgebraicBasis,
                     AlgebraicBasisCoords := Alg`AlgebraicBasisCoords,
                     RawAlgebraicBasis := Alg`RawAlgebraicBasis,
                     RawAlgebraicResidueMatrix := Alg`RawResidueMatrix,
                     H1Image2Ghat4BasisCoords := Alg`H1Image2Ghat4BasisCoords,
                     AlgebraicRelationBasisCoords := Alg`AlgebraicRelationBasisCoords,
                     AlgebraicRelationResidueBasis := Alg`AlgebraicRelationResidueBasis,
                     ResidueQuotientProjection := Alg`ResidueQuotientProjection,
                     AlgebraicResidueMatrix := Alg`ResidueMatrix,
                     AlgebraicResidueMatrixBeforeProjection := Alg`ResidueMatrixBeforeProjection,
                     MatchBasis := Match`MatchBasis,
                     MatchingPairs := Match`MatchingPairs,
                     MatchingPairsEnumerated := Match`MatchingPairsEnumerated,
                     MatchRecord := Match >;
end function;

procedure PrintBrauerPairSummary(R)
    if not R`Ok then
        printf "Input failed: %o\n", R`Message;
        return;
    end if;
    printf "Status: %o\n", R`Message;
    printf "|G| = %o, modulus 2|G| = %o\n", R`GOrder, R`Modulus;
    if assigned R`GeometricBasisH2 then
        printf "dim H^2(G,F_2) geometric residue kernel = %o\n", #R`GeometricBasisH2;
        printf "dim corrected algebraic quotient = %o\n", #R`AlgebraicBasis;
        printf "dim raw Hom(U_2,Ghat[2]) = %o, relations from 2*Ghat[4] = %o\n", #R`RawAlgebraicBasis, #R`AlgebraicRelationBasisCoords;
        printf "number of residue coordinates = %o\n", #R`ResidueIndex;
        printf "dimension of matching pair space = %o\n", #R`MatchBasis;
        if R`MatchingPairsEnumerated then
            printf "enumerated matching pairs = %o\n", #R`MatchingPairs;
        else
            printf "matching pairs not enumerated; increase MaxEnumerate if desired.\n";
        end if;
    else
        printf "trivial/early-return case; matching pairs = %o\n", R`MatchingPairs;
    end if;
end procedure;

// -----------------------------------------------------------------------------
// Example usage inside Magma:
//
// load "ChatGPT_implementation_v2.mg";
// G := Alt(4);
// R := PartiallyRamifiedBrauerPairs(G, [ G!(1,2,3), G!(1,3,2) ]);
// PrintBrauerPairSummary(R);
//
// G := Sym(3);
// R := PartiallyRamifiedBrauerPairs(G, [ G!(1,2), G!(1,2,3) ]);
// PrintBrauerPairSummary(R);
// -----------------------------------------------------------------------------
