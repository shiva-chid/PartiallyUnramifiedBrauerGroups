// ChatGPT_implementation_fixed.mg
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
//   R`AlgebraicBasis            basis for Hom(U_2,Ghat[2])
//   R`GeometricResidueMatrix    step 4 residues
//   R`AlgebraicResidueMatrix    step 5 residues
//   R`MatchBasis                F_2-basis for all matching pairs
//   R`MatchingPairs             enumerated pairs, if small enough
//
// This version avoids the non-portable intrinsic ConjugacyClass(G,g) by using
// an explicit conjugation loop.  That was the source of the loading error in
// the first draft.

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

function CohomologyGroupGenerators(H)
    // CohomologyGroup(CM,n) is an abelian group in the standard Magma package.
    // For our F_2-coefficients it is elementary abelian, and the standard
    // generators give an F_2-basis.
    return [ H.i : i in [1..Ngens(H)] | Order(H.i) ne 1 ];
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

function GeometricPowerResidueColumn(G, Creps, Nlist, Ext)
    F := GF(2);
    E := Ext`E;
    z := Ext`z;
    Lift := Ext`Lift;
    vals := [];

    for i in [1..#Creps] do
        tg := Lift(Creps[i]);
        for k in Nlist[i] do
            pk := tg^k;
            if IsConjugate(E, pk, tg) then
                Append(~vals, F!0);
            elif IsConjugate(E, pk, z*tg) then
                Append(~vals, F!1);
            else
                error Sprintf("Geometric residue error on class %o and unit %o: power lift lies in neither fibre conjugacy class.", i, k);
            end if;
        end for;
    end for;
    return Vector(F, vals);
end function;

// -----------------------------------------------------------------------------
// Algebraic residue basis Hom(U_2, Ghat[2])
// -----------------------------------------------------------------------------

function AlgebraicResidueData(G, Creps, CM, Udata, Nlist)
    F := GF(2);
    H1 := CohomologyGroup(CM,1);
    H1basis := CohomologyGroupGenerators(H1);
    chars := [ OneCocycle(CM, b) : b in H1basis ];

    chiVals := [];
    for j in [1..#H1basis] do
        Append(~chiVals, [ BitOfModuleElt(chars[j](<Creps[i]>)) : i in [1..#Creps] ]);
    end for;

    Ubas := Udata`Basis;
    AlgBasis := [ <a,j> : a in [1..#Ubas], j in [1..#H1basis] ];

    R := SeqSumInt([ #Nlist[i] : i in [1..#Nlist] ]);
    A := ZeroMatrix(F, R, #AlgBasis);

    row := 0;
    for i in [1..#Creps] do
        for k in Nlist[i] do
            row +:= 1;
            uk := Udata`Coordinates(k);
            for col in [1..#AlgBasis] do
                a := AlgBasis[col][1];
                j := AlgBasis[col][2];
                A[row,col] := F!((uk[a] * chiVals[j][i]) mod 2);
            end for;
        end for;
    end for;

    RF := recformat< H1, H1Basis, CharacterValuesOnC, AlgebraicBasis, ResidueMatrix >;
    return rec< RF | H1 := H1, H1Basis := H1basis,
                     CharacterValuesOnC := chiVals,
                     AlgebraicBasis := AlgBasis,
                     ResidueMatrix := A >;
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
                     H1, H1Basis, AlgebraicBasis, AlgebraicResidueMatrix,
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

    ResidueIndex := [];
    for i in [1..#Nlist] do
        for k in Nlist[i] do
            Append(~ResidueIndex, <i,k>);
        end for;
    end for;

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
        col := GeometricPowerResidueColumn(G, Creps, Nlist, Ext);
        for r in [1..R] do
            GeoRes[r,j] := col[r];
        end for;
    end for;

    // Step 5: algebraic residue basis.
    Alg := AlgebraicResidueData(G, Creps, CM, Udata, Nlist);

    // Step 6: matching pairs.
    Match := MatchResidues(GeoRes, Alg`ResidueMatrix : MaxEnumerate := MaxEnumerate);

    return rec< RF | Ok := true, Message := "ok", GOrder := #G, Modulus := N,
                     CRepresentatives := Creps, Csets := Csets,
                     U2Data := Udata, Ni := Nlist, ResidueIndex := ResidueIndex,
                     CM := CM,
                     H2 := GK`H2, H2Basis := GK`H2Basis,
                     GeometricResidueToH1Matrix := GK`ResidueMatrix,
                     GeometricKernelBasisCoords := GK`KernelBasisCoords,
                     GeometricBasisH2 := GK`KernelBasisH2,
                     GeometricExtensions := Exts, GeometricMarkings := Marks,
                     GeometricResidueMatrix := GeoRes,
                     H1 := Alg`H1, H1Basis := Alg`H1Basis,
                     AlgebraicBasis := Alg`AlgebraicBasis,
                     AlgebraicResidueMatrix := Alg`ResidueMatrix,
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
        printf "dim algebraic Hom(U_2,Ghat[2]) = %o\n", #R`AlgebraicBasis;
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
// load "ChatGPT_implementation_fixed.mg";
// G := Alt(4);
// R := PartiallyRamifiedBrauerPairs(G, [ G!(1,2,3), G!(1,3,2) ]);
// PrintBrauerPairSummary(R);
//
// G := Sym(3);
// R := PartiallyRamifiedBrauerPairs(G, [ G!(1,2), G!(1,2,3) ]);
// PrintBrauerPairSummary(R);
// -----------------------------------------------------------------------------
