///////////////////////////////////////////////////////////////////////
// brauer_bg_correct_algorithms.mg
//
// Magma implementation of the two algorithms in the prompt.
//
// Input convention:
//     G      : a finite permutation group.
//     CReps  : a sequence [g1,...,gk] of representatives of the chosen
//              conjugacy classes C_i in G.
//
// Output convention:
//     The main function BrauerCoveringData(G,CReps) returns a record with
//     enough linear algebra data to inspect every stage of Algorithm 1.
//
//     The function BrauerGroupData(cov) implements Algorithm 2.  It returns
//     the subgroup of the covering used as representatives for the quotient,
//     chosen as a coordinate-orthogonal complement of the kernel inside the
//     covering.
//
// Important mathematical conventions:
//   * All vector spaces are over F_2.
//   * H^2(G,Z/2Z) is computed by Magma's finite-group cohomology package.
//   * A 2-cocycle f represents the central extension with elements (a,g),
//       (a,g)(b,h) = (a+b+f(g,h), gh).
//   * For the geometric arithmetic residue of a marked lift \tilde g_i,
//     the value at u in N_i is 0 if \tilde g_i^u is conjugate to \tilde g_i
//     in the extension, and 1 otherwise.  This is the additive F_2 convention.
//   * The algebraic component is H^1(Q(zeta_{2|G|})/Q, Ghat[2]).  Since
//     Ghat[2] has trivial cyclotomic action, this is Hom((Z/2|G|Z)^*,Ghat[2]).
//
// This file prioritises readability.  It deliberately avoids constructing
// large abstract central-extension groups: for the 2-covering extensions it
// computes inside the explicit set {0,1} x G.
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
// Records
///////////////////////////////////////////////////////////////////////

CoveringFormat := recformat<
    G,
    CReps,
    ClassSets,
    N,
    UnitGroup,
    UnitMap,
    UnitEvenGeneratorIndices,
    U2Elements,
    NiElements,
    ResiduePositions,

    CM2,
    H2,
    H2Basis,
    H2BasisCoords,
    GeometricKernelBasis,
    GeometricKernelCoords,

    AbelianQuotient,
    AbelianMap,
    AbelianInvariants,
    Ghat2BasisIndices,
    Ghat2Dim,
    Ghat4DoubleBasisIndices,

    ArithmeticBasis,
    GeometricResidueMatrix,
    ArithmeticResidueMatrix,
    CoveringResidueMatrix,
    CoveringSpace,
    CoveringBasis,
    CoveringGeneratorPairs
>;

BrauerGroupFormat := recformat<
    Covering,
    BocksteinWBasis,
    BocksteinWCoords,
    VArithmeticBasisIndices,
    KernelInsideCovering,
    KernelInsideCoveringBasis,
    BrauerRepresentativeSpace,
    BrauerRepresentativeBasis,
    BrauerRepresentativePairs,
    QuotientDimension
>;

///////////////////////////////////////////////////////////////////////
// Small utilities
///////////////////////////////////////////////////////////////////////

function IsPowerOfTwoInteger(n)
    if n le 0 then
        return false;
    end if;
    return n eq 2^Valuation(n,2);
end function;

function F2VecFromSeq(seq)
    return Vector(GF(2), [ GF(2)!(Integers()!x mod 2) : x in seq ]);
end function;

function F2Value(x)
    // Magma cocycle values for a module with invariants [2] are vectors
    // over the integers, printed for example as (1).  Reduce the first
    // coordinate modulo 2.
    return Integers()!Eltseq(x)[1] mod 2;
end function;

function C2ModuleValue(a)
    // Value in the coefficient module Z/2Z used by CohomologyModule(...,[2],...).
    return RSpace(Integers(),1)![ Integers()!a mod 2 ];
end function;

function AddCohomologyElements(H, elems, coeffs)
    x := H!0;
    for i in [1..#elems] do
        if Integers()!coeffs[i] mod 2 eq 1 then
            x +:= elems[i];
        end if;
    end for;
    return x;
end function;

function ElementCoordsF2(x, d)
    // Coordinates of a quotient RSpace element, reduced modulo 2.
    s := Eltseq(x);
    return Vector(GF(2), [ GF(2)!(Integers()!s[i] mod 2) : i in [1..d] ]);
end function;

function RowMatrixFromVectors(Vs, ncols)
    if #Vs eq 0 then
        return Matrix(GF(2), 0, ncols, []);
    end if;
    return Matrix(GF(2), #Vs, ncols, &cat[ Eltseq(v) : v in Vs ]);
end function;

function ZeroMatrixF2(nrows,ncols)
    return Matrix(GF(2), nrows, ncols, [ GF(2)!0 : i in [1..nrows*ncols] ]);
end function;

function DotF2(v,w)
    return &+[ v[i]*w[i] : i in [1..Degree(Parent(v))] ];
end function;

function UnitToInteger(unitMap, u)
    return Integers()!unitMap(u);
end function;

///////////////////////////////////////////////////////////////////////
// Conjugacy-class utilities
///////////////////////////////////////////////////////////////////////

function ClassSet(G,g)
    return { x : x in ConjugacyClass(G,g) };
end function;

function ClassIndex(x, classSets)
    for i in [1..#classSets] do
        if x in classSets[i] then
            return i;
        end if;
    end for;
    return 0;
end function;

function ValidateCAndComputeN(G, CReps)
    require Order(G) mod 2 eq 0:
        "Order(G) is odd.  The 2-primary Brauer group computed here is zero.";

    N := 2*Order(G);
    classSets := [ ClassSet(G,g) : g in CReps ];

    // C should not include the identity class.
    require forall{ i : i in [1..#classSets] | not (Id(G) in classSets[i]) }:
        "The chosen ramification classes should not contain the identity.";

    // The union of the chosen conjugacy classes should generate G.
    allCElements := &cat[ SetToSequence(S) : S in classSets ];
    require sub< G | allCElements > eq G:
        "The union of the chosen conjugacy classes does not generate G.";

    // Unit group modulo 2|G|.  This also controls the powering action.
    U, unitMap := UnitGroup(Integers(N));

    // Check closure under invertible powers.  Using units modulo 2|G| is
    // slightly stronger than using units modulo |G| but is the same for the
    // powering action on G and is the group needed later for residues.
    for i in [1..#CReps] do
        for u in U do
            k := UnitToInteger(unitMap,u);
            require ClassIndex(CReps[i]^k, classSets) ne 0:
                "The chosen classes are not closed under invertible powers.";
        end for;
    end for;

    U2elts := [ u : u in U | IsPowerOfTwoInteger(Order(u)) ];

    Ni := [];
    for i in [1..#CReps] do
        Append(~Ni, [ u : u in U2elts |
            ClassIndex(CReps[i]^UnitToInteger(unitMap,u), classSets) eq i ]);
    end for;

    return N, U, unitMap, U2elts, Ni, classSets;
end function;

///////////////////////////////////////////////////////////////////////
// Abelianisation and Ghat[2]
///////////////////////////////////////////////////////////////////////

function AbelianData(G)
    // We use Magma's abelian quotient.  The codomain is an abelian group with
    // invariant-factor generators, so Eltseq(pi(g)) gives coordinates.
    A, pi := AbelianQuotient(G);
    invs := [ Order(A.i) : i in [1..Ngens(A)] ];
    even := [ i : i in [1..#invs] | invs[i] mod 2 eq 0 ];
    div4 := [ i : i in even | invs[i] mod 4 eq 0 ];
    return A, pi, invs, even, div4;
end function;

function Ghat2CharacterValue(pi, evenIndices, ell, g)
    // ell selects the ell-th basis vector of Ghat[2].
    // This character is the parity of the corresponding abelianisation
    // coordinate.
    q := pi(g);
    coords := Eltseq(q);
    idx := evenIndices[ell];
    return Integers()!coords[idx] mod 2;
end function;

///////////////////////////////////////////////////////////////////////
// H^2(G,Z/2Z) and geometric residues
///////////////////////////////////////////////////////////////////////

function H2Data(G)
    ZZ := Integers();
    mats := [ IdentityMatrix(ZZ,1) : i in [1..Ngens(G)] ];
    CM2 := CohomologyModule(G, [2], mats);
    H2 := CohomologyGroup(CM2, 2);
    basis := [ H2.i : i in [1..Ngens(H2)] ];
    coords := [ ElementCoordsF2(basis[i], #basis) : i in [1..#basis] ];
    return CM2, H2, basis, coords;
end function;

function GeometricResidueValue(CM2, h2elt, g, h)
    // h must centralise g.  The commutator of the canonical lifts is
    // f(g,h)+f(h,g) in F_2.
    f := TwoCocycle(CM2, h2elt);
    return (F2Value(f(<g,h>)) + F2Value(f(<h,g>))) mod 2;
end function;

function GeometricKernel(G, CReps, CM2, H2, H2Basis)
    tests := [];
    for i in [1..#CReps] do
        Zg := Centralizer(G, CReps[i]);
        for h in Generators(Zg) do
            Append(~tests, <i,h>);
        end for;
    end for;

    rows := [];
    for b in H2Basis do
        vals := [];
        for t in tests do
            Append(~vals, GeometricResidueValue(CM2, b, CReps[t[1]], t[2]));
        end for;
        Append(~rows, Vector(GF(2), vals));
    end for;

    A := RowMatrixFromVectors(rows, #tests);
    K := Nullspace(A);

    KbasisCoords := [ Vector(GF(2), Eltseq(v)) : v in Basis(K) ];
    Kbasis := [ AddCohomologyElements(H2, H2Basis, Eltseq(v)) : v in KbasisCoords ];

    return Kbasis, KbasisCoords;
end function;

///////////////////////////////////////////////////////////////////////
// Explicit central extension attached to a 2-cocycle
///////////////////////////////////////////////////////////////////////

function ExtMulF(f, x, y)
    return < (x[1] + y[1] + F2Value(f(<x[2],y[2]>))) mod 2, x[2]*y[2] >;
end function;

function ExtInvF(f, x)
    return < (x[1] + F2Value(f(<x[2],x[2]^-1>))) mod 2, x[2]^-1 >;
end function;

function ExtPowF(f, x, n)
    if n eq 0 then
        return <0, Id(Parent(x[2]))>;
    end if;
    if n lt 0 then
        return ExtPowF(f, ExtInvF(f,x), -n);
    end if;

    ans := <0, Id(Parent(x[2]))>;
    base := x;
    m := Integers()!n;
    while m gt 0 do
        if m mod 2 eq 1 then
            ans := ExtMulF(f,ans,base);
        end if;
        base := ExtMulF(f,base,base);
        m div:= 2;
    end while;
    return ans;
end function;

function ExtConjugateF(f, x, by)
    return ExtMulF(f, ExtMulF(f, ExtInvF(f,by), x), by);
end function;

function IsConjugateInExtensionF(G, f, x, y)
    Eelts := [ <a,g> : a in [0,1], g in G ];
    for t in Eelts do
        if ExtConjugateF(f,x,t) eq y then
            return true;
        end if;
    end for;
    return false;
end function;

function GeometricArithmeticResidue(CM2, h2elt, g, u, unitMap)
    f := TwoCocycle(CM2, h2elt);
    k := UnitToInteger(unitMap,u);
    lift := <0,g>;
    liftedPower := ExtPowF(f,lift,k);

    // Residue convention: 0 means the powered lift remains in the marked
    // conjugacy class, 1 means it has moved to the other lift above the same
    // base conjugacy class.
    if IsConjugateInExtensionF(Parent(g), f, liftedPower, lift) then
        return 0;
    else
        return 1;
    end if;
end function;

///////////////////////////////////////////////////////////////////////
// Arithmetic H^1 and residues
///////////////////////////////////////////////////////////////////////

function UnitEvenGeneratorIndices(U)
    return [ j : j in [1..Ngens(U)] | Order(U.j) mod 2 eq 0 ];
end function;

function ArithmeticBasis(U, ghat2dim)
    evenU := UnitEvenGeneratorIndices(U);
    return [ <j,ell> : j in evenU, ell in [1..ghat2dim] ];
end function;

function ArithmeticResidueValue(unit, arithBasisElt, pi, evenCharIndices, g)
    // A basis element is a homomorphism U -> Ghat[2]: the selected unit-group
    // generator maps to the selected character, all other unit generators map
    // to zero.
    j := arithBasisElt[1];
    ell := arithBasisElt[2];
    coeff := Integers()!Eltseq(unit)[j] mod 2;
    return (coeff * Ghat2CharacterValue(pi, evenCharIndices, ell, g)) mod 2;
end function;

///////////////////////////////////////////////////////////////////////
// Residue matrices and Algorithm 1
///////////////////////////////////////////////////////////////////////

function MakeResiduePositions(Ni)
    // We impose the residue equation for every u in every N_i.  This is
    // redundant but very transparent and avoids choosing generators for N_i.
    positions := [];
    for i in [1..#Ni] do
        for u in Ni[i] do
            Append(~positions, <i,u>);
        end for;
    end for;
    return positions;
end function;

function BuildGeometricResidueMatrix(CM2, geomBasis, CReps, unitMap, residuePositions)
    rows := [];
    for b in geomBasis do
        vals := [];
        for pos in residuePositions do
            i := pos[1];
            u := pos[2];
            Append(~vals, GeometricArithmeticResidue(CM2, b, CReps[i], u, unitMap));
        end for;
        Append(~rows, Vector(GF(2), vals));
    end for;
    return RowMatrixFromVectors(rows, #residuePositions);
end function;

function BuildArithmeticResidueMatrix(arithBasis, pi, evenCharIndices, CReps, residuePositions)
    rows := [];
    for b in arithBasis do
        vals := [];
        for pos in residuePositions do
            i := pos[1];
            u := pos[2];
            Append(~vals, ArithmeticResidueValue(u, b, pi, evenCharIndices, CReps[i]));
        end for;
        Append(~rows, Vector(GF(2), vals));
    end for;
    return RowMatrixFromVectors(rows, #residuePositions);
end function;

function StackResidueMatrices(A,B)
    // A and B have the same number of columns.  Return vertical concatenation.
    require Ncols(A) eq Ncols(B): "Residue matrices have incompatible widths.";
    rows := [];
    for i in [1..Nrows(A)] do Append(~rows, Vector(GF(2), Eltseq(A[i]))); end for;
    for i in [1..Nrows(B)] do Append(~rows, Vector(GF(2), Eltseq(B[i]))); end for;
    return RowMatrixFromVectors(rows, Ncols(A));
end function;

function PairFromAmbientVector(v, geomBasis, arithBasis)
    gdim := #geomBasis;
    adim := #arithBasis;
    geomCoeffs := [ Integers()!v[i] : i in [1..gdim] ];
    arithCoeffs := [ Integers()!v[gdim+j] : j in [1..adim] ];
    return <geomCoeffs, arithCoeffs>;
end function;

function BrauerCoveringData(G, CReps)
    N, U, unitMap, U2elts, Ni, classSets := ValidateCAndComputeN(G, CReps);

    CM2, H2, H2Basis, H2BasisCoords := H2Data(G);
    geomBasis, geomCoords := GeometricKernel(G, CReps, CM2, H2, H2Basis);

    A, pi, invs, evenCharIndices, div4CharIndices := AbelianData(G);
    ghat2dim := #evenCharIndices;
    arithBasis := ArithmeticBasis(U, ghat2dim);
    evenU := UnitEvenGeneratorIndices(U);

    residuePositions := MakeResiduePositions(Ni);
    geomResidueMat := BuildGeometricResidueMatrix(CM2, geomBasis, CReps, unitMap, residuePositions);
    arithResidueMat := BuildArithmeticResidueMatrix(arithBasis, pi, evenCharIndices, CReps, residuePositions);
    R := StackResidueMatrices(geomResidueMat, arithResidueMat);

    CoverSpace := Nullspace(R);
    coverBasis := [ Vector(GF(2), Eltseq(v)) : v in Basis(CoverSpace) ];
    coverPairs := [ PairFromAmbientVector(v, geomBasis, arithBasis) : v in coverBasis ];

    return rec< CoveringFormat |
        G := G,
        CReps := CReps,
        ClassSets := classSets,
        N := N,
        UnitGroup := U,
        UnitMap := unitMap,
        UnitEvenGeneratorIndices := evenU,
        U2Elements := U2elts,
        NiElements := Ni,
        ResiduePositions := residuePositions,

        CM2 := CM2,
        H2 := H2,
        H2Basis := H2Basis,
        H2BasisCoords := H2BasisCoords,
        GeometricKernelBasis := geomBasis,
        GeometricKernelCoords := geomCoords,

        AbelianQuotient := A,
        AbelianMap := pi,
        AbelianInvariants := invs,
        Ghat2BasisIndices := evenCharIndices,
        Ghat2Dim := ghat2dim,
        Ghat4DoubleBasisIndices := div4CharIndices,

        ArithmeticBasis := arithBasis,
        GeometricResidueMatrix := geomResidueMat,
        ArithmeticResidueMatrix := arithResidueMat,
        CoveringResidueMatrix := R,
        CoveringSpace := CoverSpace,
        CoveringBasis := coverBasis,
        CoveringGeneratorPairs := coverPairs
    >;
end function;

///////////////////////////////////////////////////////////////////////
// Algorithm 2: quotient by the V x W kernel, returned as complement
///////////////////////////////////////////////////////////////////////

function BocksteinCocycleForCharacter(pi, abIndex, modulus)
    // Character chi sends the abIndex-th abelian generator to 1/modulus in Q/Z.
    // The Bockstein for 0 -> C2 -> Q/Z --2--> Q/Z -> 0 is the carry cocycle:
    //     delta(g,h) = floor((a(g)+a(h))/modulus) mod 2.
    return func< pair |
        C2ModuleValue(((Integers()!Eltseq(pi(pair[1]))[abIndex]
                       + Integers()!Eltseq(pi(pair[2]))[abIndex]) div modulus) mod 2) >;
end function;

function BocksteinWBasis(cov)
    H2 := cov`H2;
    CM2 := cov`CM2;
    pi := cov`AbelianMap;
    invs := cov`AbelianInvariants;
    evenIdx := cov`Ghat2BasisIndices;
    h2dim := #cov`H2Basis;

    wElts := [];
    wCoords := [];

    for idx in evenIdx do
        n := invs[idx];
        coc := BocksteinCocycleForCharacter(pi, idx, n);
        h2elt := IdentifyTwoCocycle(CM2, coc);
        Append(~wElts, h2elt);
        Append(~wCoords, ElementCoordsF2(h2elt, h2dim));
    end for;

    // Return a basis, not merely the possibly dependent spanning set.
    Wmat := RowMatrixFromVectors(wCoords, h2dim);
    Wspace := RowSpace(Wmat);
    basisCoords := [ Vector(GF(2), Eltseq(v)) : v in Basis(Wspace) ];
    basisElts := [ AddCohomologyElements(H2, cov`H2Basis, Eltseq(v)) : v in basisCoords ];

    return basisElts, basisCoords;
end function;

function VArithmeticBasisIndices(cov)
    // Image of H^1(U,Ghat[4]) -> H^1(U,Ghat[2]) by doubling.
    // In invariant-factor coordinates this keeps exactly the Ghat[2] basis
    // characters coming from abelianisation factors whose order is divisible by 4.
    div4 := cov`Ghat4DoubleBasisIndices;
    idxs := [];
    for a in [1..#cov`ArithmeticBasis] do
        targetAbIndex := cov`Ghat2BasisIndices[cov`ArithmeticBasis[a][2]];
        if targetAbIndex in div4 then
            Append(~idxs, a);
        end if;
    end for;
    return idxs;
end function;

function OrthogonalColumnsToSubspace(rowBasis, ambientDim)
    // rowBasis spans a subspace S of F_2^ambientDim.  Return a matrix whose
    // columns give equations cutting out S: v is in S iff v*M = 0.
    S := RowMatrixFromVectors(rowBasis, ambientDim);
    Sperp := Nullspace(Transpose(S));
    perpbasis := [ Vector(GF(2), Eltseq(v)) : v in Basis(Sperp) ];
    if #perpbasis eq 0 then
        return Matrix(GF(2), ambientDim, 0, []);
    end if;
    // Columns are the perpendicular vectors.
    return Transpose(RowMatrixFromVectors(perpbasis, ambientDim));
end function;

function MatrixAppendColumns(A,B)
    require Nrows(A) eq Nrows(B): "Matrices must have the same number of rows.";
    entries := [];
    for i in [1..Nrows(A)] do
        for j in [1..Ncols(A)] do Append(~entries, A[i,j]); end for;
        for j in [1..Ncols(B)] do Append(~entries, B[i,j]); end for;
    end for;
    return Matrix(GF(2), Nrows(A), Ncols(A)+Ncols(B), entries);
end function;

function MembershipEquationMatrixForAlgorithm2(cov, Wcoords, Vidcs)
    gdim := #cov`GeometricKernelBasis;
    adim := #cov`ArithmeticBasis;
    h2dim := #cov`H2Basis;
    ambientDim := gdim + adim;

    // Map from ambient covering coordinates to full H^2 coordinates.
    KtoH2Rows := [];
    for v in cov`GeometricKernelCoords do
        Append(~KtoH2Rows, v);
    end for;
    KtoH2 := RowMatrixFromVectors(KtoH2Rows, h2dim);  // gdim x h2dim

    Ageom := ZeroMatrixF2(ambientDim, h2dim);
    for i in [1..gdim] do
        for j in [1..h2dim] do
            Ageom[i,j] := KtoH2[i,j];
        end for;
    end for;

    Wcols := OrthogonalColumnsToSubspace(Wcoords, h2dim); // h2dim x eW
    EqGeom := Ageom * Wcols;                              // ambientDim x eW

    // Arithmetic membership in V.
    Vrows := [];
    for idx in Vidcs do
        row := [ GF(2)!0 : i in [1..adim] ];
        row[idx] := GF(2)!1;
        Append(~Vrows, Vector(GF(2), row));
    end for;
    Vcols := OrthogonalColumnsToSubspace(Vrows, adim);     // adim x eV

    Aarith := ZeroMatrixF2(ambientDim, adim);
    for j in [1..adim] do
        Aarith[gdim+j,j] := GF(2)!1;
    end for;
    EqArith := Aarith * Vcols;                             // ambientDim x eV

    return MatrixAppendColumns(EqGeom, EqArith);
end function;

function AmbientVectorSpace(cov)
    return VectorSpace(GF(2), #cov`GeometricKernelBasis + #cov`ArithmeticBasis);
end function;

function SubspaceFromRows(V, rows)
    if #rows eq 0 then
        return sub< V | V!0 >;
    end if;
    return sub< V | [ V!Eltseq(r) : r in rows ] >;
end function;

function ExpressInBasisRows(v, basisRows)
    B := RowMatrixFromVectors(basisRows, Degree(Parent(v)));
    return Vector(GF(2), Eltseq(Solution(B, v)));
end function;

function LiftFromBasisCoords(coords, basisRows)
    if #basisRows eq 0 then
        return Vector(GF(2), []);
    end if;
    n := Degree(Parent(basisRows[1]));
    ans := Vector(GF(2), [ GF(2)!0 : i in [1..n] ]);
    for i in [1..#basisRows] do
        if coords[i] eq GF(2)!1 then
            ans +:= basisRows[i];
        end if;
    end for;
    return ans;
end function;

function CoordinateOrthogonalComplementInsideCover(coverBasis, kernelBasis)
    // Work in coordinates relative to coverBasis.  If K has rows k_i, return
    // all coordinate vectors x with x dot k_i = 0, then lift back to ambient.
    cdim := #coverBasis;
    if cdim eq 0 then
        return [];
    end if;

    kcoords := [];
    for k in kernelBasis do
        Append(~kcoords, ExpressInBasisRows(k, coverBasis));
    end for;

    Kmat := RowMatrixFromVectors(kcoords, cdim);
    perpCoordSpace := Nullspace(Transpose(Kmat));
    perpCoords := [ Vector(GF(2), Eltseq(v)) : v in Basis(perpCoordSpace) ];
    return [ LiftFromBasisCoords(v, coverBasis) : v in perpCoords ];
end function;

function BrauerGroupData(cov)
    Wbasis, Wcoords := BocksteinWBasis(cov);
    Vidcs := VArithmeticBasisIndices(cov);

    ambient := AmbientVectorSpace(cov);
    coverSub := SubspaceFromRows(ambient, cov`CoveringBasis);

    EqKW := MembershipEquationMatrixForAlgorithm2(cov, Wcoords, Vidcs);
    KWspace := Nullspace(EqKW);
    KWbasis := [ Vector(GF(2), Eltseq(v)) : v in Basis(KWspace) ];
    KWsub := SubspaceFromRows(ambient, KWbasis);

    kernelSub := coverSub meet KWsub;
    kernelBasis := [ Vector(GF(2), Eltseq(v)) : v in Basis(kernelSub) ];

    brBasis := CoordinateOrthogonalComplementInsideCover(cov`CoveringBasis, kernelBasis);
    brSub := SubspaceFromRows(ambient, brBasis);
    brPairs := [ PairFromAmbientVector(v, cov`GeometricKernelBasis, cov`ArithmeticBasis) : v in brBasis ];

    return rec< BrauerGroupFormat |
        Covering := cov,
        BocksteinWBasis := Wbasis,
        BocksteinWCoords := Wcoords,
        VArithmeticBasisIndices := Vidcs,
        KernelInsideCovering := kernelSub,
        KernelInsideCoveringBasis := kernelBasis,
        BrauerRepresentativeSpace := brSub,
        BrauerRepresentativeBasis := brBasis,
        BrauerRepresentativePairs := brPairs,
        QuotientDimension := Dimension(coverSub) - Dimension(kernelSub)
    >;
end function;

///////////////////////////////////////////////////////////////////////
// Printing helpers
///////////////////////////////////////////////////////////////////////

procedure PrintCoveringSummary(cov)
    print "===== Covering data =====";
    print "|G| =", Order(cov`G);
    print "Number of chosen conjugacy classes =", #cov`CReps;
    print "N = 2|G| =", cov`N;
    print "dim_F2 H^2(G,Z/2) =", #cov`H2Basis;
    print "dim_F2 geometric marked subgroup =", #cov`GeometricKernelBasis;
    print "dim_F2 Ghat[2] =", cov`Ghat2Dim;
    print "dim_F2 arithmetic H^1 =", #cov`ArithmeticBasis;
    print "Number of residue equations used =", #cov`ResiduePositions;
    print "dim_F2 covering =", Dimension(cov`CoveringSpace);
    print "Covering basis vectors are stored in cov`CoveringBasis.";
    print "Covering generator pairs are stored in cov`CoveringGeneratorPairs.";
end procedure;

procedure PrintBrauerSummary(br)
    print "===== Brauer group data =====";
    print "dim_F2 kernel inside covering =", Dimension(br`KernelInsideCovering);
    print "dim_F2 Brauer group quotient =", br`QuotientDimension;
    print "Brauer representative basis vectors are stored in br`BrauerRepresentativeBasis.";
    print "Brauer representative pairs are stored in br`BrauerRepresentativePairs.";
end procedure;

///////////////////////////////////////////////////////////////////////
// Minimal example template
///////////////////////////////////////////////////////////////////////
/*
load "brauer_bg_correct_algorithms.mg";

G := AlternatingGroup(4);
// For example, use the two non-identity power-stable pieces represented by
// a 3-cycle and a double transposition.  Adjust CReps to your actual C.
CReps := [ G!(1,2,3), G!((1,2)(3,4)) ];

cov := BrauerCoveringData(G, CReps);
PrintCoveringSummary(cov);

br := BrauerGroupData(cov);
PrintBrauerSummary(br);
*/
