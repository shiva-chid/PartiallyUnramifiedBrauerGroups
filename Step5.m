intrinsic AlgebraicResidueMap(G :: Grp, gis :: SeqEnum, His :: SeqEnum) -> AlgMatElt, GrpAb, GrpAb
{Given
- a group G
- a list gis of representatives of conjugacy classes of G
- a list His of subgroups of (Z/2|G|)^* stabilizing the conjugacy classes of gis
returns the algebraic Brauer residue map as a matrix over GF(2). Its action on rows represents
the map from H^1((Z/2|G|)^*, Gdual[2])=Hom(_,_) to the direct sum of Hom(H, Z/2) for H in His.}
    require #gis eq #His : "Number of conjugacy classes must match number of stabilizer subgroups.";
    n := 2*#G;
    Zn := Integers(n);
    U, i := UnitGroup(Zn);
    Umod2, pi2 := ElementaryAbelianQuotient(U,2); // enough to work with this quotient, because we only consider homomorphisms to a 2-torsion group.
    Hismod2 := [pi2(H) : H in His];

    // fixing the choice of an ordered basis for the codomain of the algebraic residue map
    // by fixing bases for the F_2-vector spaces H/2H as H runs over the given list of subgroups
    // This MUST exactly match the basis constructed in GeometricResidue
    gensH := &cat[[H.i : i in [1..Ngens(H)]] : H in Hismod2];

    Gabmod2, piabmod2 := ElementaryAbelianQuotient(G,2);
    A, phi := Dual(Gabmod2); // A is the dual of G^ab/2*G^ab, so A is Gdual[2]. phi is the pairing G^ab/2*G^ab x A --> Z/2
    dimA := #AbelianInvariants(A);

    H1, psi := Hom(Umod2,A); // this is the domain
    vals := [];
    for i := 1 to Ngens(H1) do
        val := &cat[[phi(piabmod2(gi),psi(H1.i)(x)) : x in gensH] : gi in gis];
        Append(~vals,val);
    end for;
    M := Matrix(GF(2), #vals, #vals[1], vals);

    return M, H1, A;
end intrinsic;


intrinsic GeometricResidueMap(G :: Grp, gis :: SeqEnum, His :: SeqEnum, CM :: ModCoho, H2 :: ModTupRng) -> AlgMatElt, ModTupRng
{Given
- a group G
- a list gis of representatives of conjugacy classes of G
- a list His of subgroups of (Z/2|G|)^* stabilizing the conjugacy classes of gis
- the cohomology module CM for the trivial G-module Z/2
- the second cohomology group H^2(G, Z/2)
returns the geometric Brauer residue map as a matrix over GF(2). Its action on rows represents
the map from H^2(G, Z/2) to the direct sum of Hom(H, Z/2) for H in His.}
    require #gis eq #His : "Number of conjugacy classes must match number of stabilizer subgroups.";
    n := 2*#G;
    Zn := Integers(n);
    U, i := UnitGroup(Zn);
    Umod2, pi2 := ElementaryAbelianQuotient(U,2); // enough to work with this quotient, because we only consider homomorphisms to Z/2.
    Hismod2 := [pi2(H) : H in His];

    // fixing the choice of an ordered basis for the codomain of the geometric residue map
    // by fixing bases for the F_2-vector spaces H/2H as H runs over the given list of subgroups
    // This MUST exactly match the basis constructed in AlgebraicResidue
    gensH := &cat[[H.i : i in [1..Ngens(H)]] : H in Hismod2];

    // fixing an ordered basis of H^2(G,Z/2)
    H2 := CohomologyGroup(CM, 2);
    H2basis := [H2.i : i in [1..Dimension(H2)]];
    vals := [];
    for chi in H2basis do
        // for each basis element of H^2(G,Z/2), first produce the corresponding central extension.
        extn, pi, iota := CentralExtensionFromClass(CM, chi);
        // if the lift of an element to the central extension, and a power of it, still remain conjugate, we record 0 and otherwise 1
        val := &cat[[IsConjugate(g, g^(i(x @@ pi2))) select 1 else 0 : x in gensH] where g is gi@@pi : gi in gis];
        Append(~vals, val);
    end for;
    M := Matrix(GF(2), #vals, #vals[1], vals);

    return M, H2;
end intrinsic;


intrinsic Btilde(G :: Grp, gis :: SeqEnum, His :: SeqEnum, CM :: ModCoho, H2 :: ModTupRng) -> GrpAb, ModTupRng, ModTupFld
{Given
- a group G
- a list gis of representatives of conjugacy classes of G
- a list His of subgroups of (Z/2|G|)^* stabilizing the conjugacy classes of gis
- the cohomology module CM for the trivial G-module Z/2
- the second cohomology group H^2(G, Z/2)
returns
- the abelian group H^1((Z/2|G|)^*, Gdual[2])=Hom(_,_)
- H^2(G, Z/2)
- a subspace of (F_2)^n where n is the sum of F_2-dimension of the first two return values.}

    M1, H1, _ := AlgebraicResidueMap(G,gis,His);
    M2, H2 := GeometricResidueMap(G,gis,His,CM,H2);
    M := VerticalJoin(M1,M2);
    K := Kernel(M);
    return H1, H2, M;
end intrinsic;

/*
// Example
G := CyclicGroup(4);
gis := [G.1, G.1^3];
n := 2*#G;
Zn := Integers(n);
U, i := UnitGroup(Zn);
H := sub<U|(Zn!5) @@ i>;
His := [H,H];
*/