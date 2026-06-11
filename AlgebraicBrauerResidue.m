intrinsic H1Gtors2(G :: Grp, gis :: SeqEnum, Hs :: SeqEnum) -> GrpAb, Map
{}
    require #gis eq #Hs : "Number of conjugacy classes must match number of stabilizer subgroups of Gamma.";
    n := 2*#G;
    Zn := Integers(n);
    U, i := UnitGroup(Zn);
    Umod2, pi2 := ElementaryAbelianQuotient(U,2);
    Hsmod2 := [pi2(H) : H in Hs];
    gensH := &cat[[H.i : i in [1..Ngens(H)]] : H in Hsmod2];

    Gab, piab := AbelianQuotient(G);
    Gabmod2, piabmod2 := ElementaryAbelianQuotient(Gab,2);
    A, phi := Dual(Gabmod2);
    dimA := #AbelianInvariants(A);

    H1, psi := Hom(Umod2,A);
    val := [&cat[[phi(piabmod2(piab(gi)),psi(H1.i)(x)) : x in gensH] : gi in gis] : i in [1..Ngens(H1)]];

    return H1, A, val;
end intrinsic;

// Example
G := CyclicGroup(4);
gis := [G.1, G.1^3];
n := 2*#G;
Zn := Integers(n);
U, i := UnitGroup(Zn);
H := sub<U|(Zn!5) @@ i>;
Hs := [H,H];
