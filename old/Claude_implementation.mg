/////////////////////////////////////////////////////////////////////////////
//  BrBG.m
//
//  Computation of the partially ramified Brauer group Br_C(BG) of the
//  classifying stack of a finite group G, ramified along a set
//  C = {C_1, ..., C_k} of conjugacy classes, following:
//
//    Algorithm 1:  the covering group ~Br_C(BG) of pairs (b1, b2) with
//        b1 in H^2(G, Z/2) admitting a (geometric) marking,
//        b2 in H^1(Gal(Q(zeta_{2|G|})/Q), \hat G[2])
//             = Hom((Z/2|G|Z)^*, \hat G[2]),
//        res_{C_i}(b1) + res_{C_i}(b2) = 0 for every i.
//
//    Algorithm 2:  Br_C(BG) = ~Br_C(BG) / (~Br_C(BG) meet (W x V)),
//        realised concretely as a vector space complement of the kernel
//        inside ~Br_C(BG)  (everything is 2-torsion).
//
//  USAGE
//    > load "BrBG.m";
//    > G    := PermutationGroup< ... >;   // any finite permutation group
//    > reps := [ g1, ..., gk ];           // one representative per class
//    > Br, data := BrauerGroupBG(G, reps);
//    > Dimension(Br);                     // Br_C(BG) = (Z/2)^Dimension(Br)
//    > for b in Basis(Br) do DescribeBrauerElement(data, b); end for;
//    > P, pi, z, lifts := MarkingData(data, Br.1);  // extension + marking
//
//  COORDINATE CONVENTIONS (used everywhere below)
//    * H2  := H^2(G, Z/2), an F_2 vector space in Magma's coordinates.
//    * K   := the subspace of H2 with vanishing geometric residues
//             (Step 3.A), with fixed basis KB; "geometric coordinates"
//             x in F_2^m mean b1 = sum_j x[j]*KB[j].
//    * A   := (Z/2|G|Z)^* = Gal(Q(zeta_{2|G|})/Q), generators A.t.
//    * Gab := G^{ab}, invariant factors m_1 | m_2 | ... ; \hat G[2] has
//             basis the characters chi_j, one for each even m_j, with
//             chi_j(g) = (j-th Gab-coordinate of g) mod 2.
//    * Hom(A, \hat G[2]) has basis E_{t,j} : A.t |-> chi_j (for the
//             even-order generators A.t; odd-order generators must map
//             to 0).  "Algebraic coordinates" y in F_2^{r2*d} are ordered
//             with t outermost and j innermost.
//    * An element of ~Br is a vector (x | y) in F_2^{m + r2*d}.
//
//  MATHEMATICAL CHOICES THAT WERE PINNED DOWN FROM THE NOTE
//    (1) H^1(Q(zeta_{2|G|})/Q, \hat G[2]) is read as Hom of the *unit
//        group* (Z/2|G|Z)^* (= the Galois group) into \hat G[2], with
//        trivial action (the action on \hat G[2] = Hom(G, mu_2) is
//        trivial since mu_2 is rational).
//    (2) W = image of \hat G / 2\hat G in H^2(G, Z/2) is taken to be the
//        connecting map of 0 -> Z/2 -> Q/Z -(x2)-> Q/Z -> 0, computed by
//        the classical "carry" 2-cocycle (see Algorithm 2 below).
//    (3) V = image of 2*\hat G[4] in Hom(A, \hat G[2]) is taken to be
//        the connecting map of 0 -> \hat G[2] -> \hat G[4] -> 2\hat G[4]
//        -> 0, where Galois acts on \hat G[4] = Hom(G, mu_4) through the
//        mod-4 cyclotomic character.  Concretely psi in 2\hat G[4] maps
//        to the homomorphism  a |-> eps(a)*psi,  with eps the order-2
//        character  eps(a) = ((a mod 4) - 1)/2 in Z/2.
//    If your conventions for (2)/(3) differ, only the two short blocks
//    in Algorithm 2 need changing.
/////////////////////////////////////////////////////////////////////////////

BrBGRF := recformat<
    G, reps, n,                  // the input
    A, amap, Selts, Nelts, Ns,   // Galois group, its 2-part, the groups N_i
    CM, H2, M,                   // cohomology machinery for H^2(G, Z/2)
    K, KB,                       // geometric classes admitting markings
    Gab, abmap, invGab, evenJ,   // the dual side  \hat G[2]
    evenT, d, r2,                // dimensions of the algebraic side
    Mgeo, Malg,                  // residue matrices (Steps 4 and 5)
    BrTilde, KerCover, Br,       // output of Algorithms 1 and 2
    Wspan, Vspan                 // the subgroups W and V of Algorithm 2
>;

//---------------------------------------------------------------------------
// The central extension attached to s in H^2(G, Z/2), returned as a faithful
// permutation group P (regular representation, degree 2|G|) together with
// the projection pi : P -> G and the generator z of its kernel.
//
// Magma's Extension(CM, s) returns an fp-group whose first Ngens(G)
// generators map onto the generators of G and whose last generator
// generates the central Z/2.
//---------------------------------------------------------------------------
function ExtensionData(CM, s)
    G := Group(CM);
    n := Ngens(G);
    E := Extension(CM, s);
    f, P := CosetAction(E, sub< E | >);     // regular, hence faithful
    pi := hom< P -> G | [ G.i : i in [1..n] ] cat [ Id(G) ] >;
    z := f(E.(n+1));
    assert Order(z) eq 2 and IsCentral(P, sub< P | z >);
    return P, pi, z;
end function;

//---------------------------------------------------------------------------
// Geometric residue (Step 3.A).  For the class with extension (P, pi, z),
// the residue at the class of g is the homomorphism
//     C_G(g) -> Z/2,   h |-> [g~, h~]      (a commutator of lifts, in {1,z};
//                                           independent of all lift choices,
//                                           since z is central).
// We return its values on the supplied generators hs of C_G(g); values on a
// generating set coordinatise Hom(C_G(g), Z/2) injectively, which is all we
// need to compute the kernel.
//---------------------------------------------------------------------------
function GeometricResidueValues(P, pi, z, g, hs)
    gt := g @@ pi;
    vals := [ GF(2) | ];
    for h in hs do
        ht := h @@ pi;
        Append(~vals, (gt, ht) eq z select 1 else 0);
    end for;
    return vals;
end function;

//---------------------------------------------------------------------------
// The main routine:  Algorithms 1 and 2.
//   G    : a finite group (a permutation group is recommended),
//   reps : a sequence of class representatives, one per ramified class.
// Returns Br (a subspace of F_2^{m + r2*d} of coset representatives, so
// Br_C(BG) = (Z/2)^Dimension(Br)) and a data record for decoding.
//---------------------------------------------------------------------------
function BrauerGroupBG(G, reps : CheckInput := true)
    F2 := GF(2);
    n  := #G;
    k  := #reps;

    //=======================================================================
    // Step 0.5: dump odd order groups
    //=======================================================================
    if IsOdd(n) then
        data := rec< BrBGRF | G := G, reps := reps, n := n >;
        return VectorSpace(F2, 0), data;
    end if;

    //=======================================================================
    // The Galois group A = Gal(Q(zeta_{2n})/Q) = (Z/2nZ)^*, its 2-primary
    // part A[2^infty], and integer representatives of its elements.
    //=======================================================================
    A, amap := UnitGroup(Integers(2*n));
    AInt    := func< a | Integers() ! amap(a) >;
    Selts   := [ A | A ! s : s in SylowSubgroup(A, 2) ];

    //=======================================================================
    // Step 1: validity of C, and the stabiliser groups N_i
    //=======================================================================
    cmap     := ClassMap(G);
    classidx := [ cmap(g) : g in reps ];
    error if #Seqset(classidx) ne k,
        "BrauerGroupBG: representatives lie in non-distinct conjugacy classes";

    if CheckInput then
        // (a) the union of the classes generates G (it is a normal subset,
        //     so this is the normal closure of the subgroup of the reps)
        error if NormalClosure(G, sub< G | reps >) ne G,
            "BrauerGroupBG: the chosen conjugacy classes do not generate G";
        // (b) closure under invertible powers: powering by units is an
        //     action of A on classes, so checking generators of A suffices
        for a in Generators(A) do
            t := AInt(a);
            error if exists{ g : g in reps | cmap(g^t) notin classidx },
                "BrauerGroupBG: classes not closed under invertible powers";
        end for;
    end if;

    // N_i = { a in A[2^infty] : C_i^a = C_i }, stored with full enumerations
    Nelts := [ [ A | a : a in Selts | cmap(reps[i]^AInt(a)) eq classidx[i] ]
               : i in [1..k] ];
    Ns    := [ sub< A | Nelts[i] > : i in [1..k] ];

    //=======================================================================
    // Step 2: H^2(G, Z/2) together with the extension machinery
    //=======================================================================
    M   := GModule(G, [ Matrix(F2, 1, 1, [1]) : i in [1..Ngens(G)] ]);
    CM  := CohomologyModule(G, M);
    H2  := CohomologyGroup(CM, 2);
    dH2 := Dimension(H2);

    //=======================================================================
    // Step 3.A: kernel of the combined geometric residue map
    //     H^2(G, Z/2) -> prod_i H^1(C_G(g_i), Z/2).
    // The residue map is a homomorphism, so it suffices to evaluate it on a
    // basis of H2 and take the nullspace of the resulting matrix.
    //=======================================================================
    centgens := [ Setseq(Generators(Centraliser(G, g))) : g in reps ];
    nrescols := &+[ Integers() | #gs : gs in centgens ];

    geomat := ZeroMatrix(F2, dH2, nrescols);
    for r in [1..dH2] do
        P, pi, z := ExtensionData(CM, H2.r);
        col := 0;
        for i in [1..k] do
            for v in GeometricResidueValues(P, pi, z, reps[i], centgens[i]) do
                col +:= 1;
                geomat[r, col] := v;
            end for;
        end for;
    end for;

    K  := Nullspace(geomat);     // subspace of F_2^dH2, in H2-coordinates
    KB := Basis(K);
    m  := #KB;

    //=======================================================================
    // Steps 3.B and 4: markings, and arithmetic residues of the geometric
    // basis elements.  For b1 with extension (P, pi, z), the marking at C_i
    // is D_i = (conjugacy class in P of) a lift g~ of g_i.  The residue at
    // a in N_i is
    //     0 if g~^a is conjugate to g~ in P,   1 otherwise;
    // g~^a always lies over g_i^a ~ g_i, hence is conjugate into the fibre
    // {g~, g~ z}, so this is well defined, and it is independent of the
    // choice of lift (replacing g~ by g~ z changes both sides by z, as the
    // exponents a are odd).  The full residue of a sum of basis elements is
    // the sum of the residues, so we only store the values on the basis KB.
    //=======================================================================
    narith := &+[ Integers() | #Nelts[i] : i in [1..k] ];

    Mgeo := ZeroMatrix(F2, m, narith);
    for r in [1..m] do
        b1 := H2 ! Eltseq(KB[r]);
        P, pi, z := ExtensionData(CM, b1);
        col := 0;
        for i in [1..k] do
            gt := reps[i] @@ pi;            // a lift; its class is D_i
            for a in Nelts[i] do
                col +:= 1;
                Mgeo[r, col] :=
                    IsConjugate(P, gt^AInt(a), gt) select F2!0 else F2!1;
            end for;
        end for;
    end for;

    //=======================================================================
    // Step 5: residues of the algebraic Brauer group Hom(A, \hat G[2]).
    // \hat G[2] = Hom(G^{ab}, Z/2) has basis chi_j over the even invariant
    // factors of Gab.  The residue of b2 at a in N_i is  b2(a)(g_i),
    // which for the basis element E_{t,j} equals
    //     (t-th exponent of a, mod 2) * chi_j(g_i).
    //=======================================================================
    Gab, abmap := AbelianQuotient(G);
    invGab := Invariants(Gab);
    evenJ  := [ j : j in [1..#invGab] | IsEven(invGab[j]) ];
    d      := #evenJ;
    evenT  := [ t : t in [1..Ngens(A)] | IsEven(Order(A.t)) ];
    r2     := #evenT;

    chivec := func< g | [ F2 | Eltseq(abmap(g))[j] : j in evenJ ] >;
    chis   := [ chivec(g) : g in reps ];                  // chi_j(g_i)
    expvec := func< a | [ F2 | Eltseq(a)[t] : t in evenT ] >;

    Malg := ZeroMatrix(F2, r2*d, narith);
    for ti in [1..r2], j in [1..d] do
        r := (ti - 1)*d + j;                              // row of E_{t,j}
        col := 0;
        for i in [1..k] do
            for a in Nelts[i] do
                col +:= 1;
                Malg[r, col] := expvec(a)[ti] * chis[i][j];
            end for;
        end for;
    end for;

    //=======================================================================
    // Step 6: match up the pairs.  The covering group is
    //     ~Br = { (x | y) in F_2^{m + r2*d} : x*Mgeo + y*Malg = 0 },
    // i.e. the nullspace of the vertically joined residue matrix.
    //=======================================================================
    BrTilde := Nullspace(VerticalJoin(Mgeo, Malg));
    U       := Generic(BrTilde);

    //=======================================================================
    // Algorithm 2: the kernel of the covering and the Brauer group.
    //
    //  W  (inside H^2(G, Z/2)):  image of \hat G/2\hat G under the
    //  connecting map of 0 -> Z/2 -> Q/Z -(x2)-> Q/Z -> 0.  For the basic
    //  character chi_j of order m_j (m_j even) this is represented by the
    //  "carry" 2-cocycle
    //      (g, h) |-> (c_j(g) + c_j(h)) div m_j   in Z/2,
    //  with c_j(g) in [0, m_j) the j-th Gab-coordinate of g.
    //=======================================================================
    Wgens := [ H2 | ];
    for j in [1..#invGab] do
        mj := invGab[j];
        if IsOdd(mj) then continue; end if;
        cj    := func< g  | Eltseq(abmap(g))[j] mod mj >;
        carry := func< gh | M ! [ F2 | (cj(gh[1]) + cj(gh[2])) div mj ] >;
        Append(~Wgens, IdentifyTwoCocycle(CM, carry));
    end for;
    H2amb := VectorSpace(F2, dH2);
    Wspan := sub< H2amb | [ H2amb ! Eltseq(w) : w in Wgens ] >;

    //=======================================================================
    //  V  (inside Hom(A, \hat G[2])):  image of 2*\hat G[4].  An element
    //  psi = 2*phi  (so psi = chi_j with 4 | m_j) maps to the homomorphism
    //      a |-> eps(a) * psi,
    //  where eps : A -> Z/2 is the mod-4 cyclotomic character,
    //      eps(a) = ((a mod 4) - 1)/2,
    //  i.e. eps(a) = 1 iff a = 3 mod 4.  (This is the connecting map of
    //  0 -> \hat G[2] -> \hat G[4] -> 2\hat G[4] -> 0 with Galois acting on
    //  \hat G[4] = Hom(G, mu_4) through the cyclotomic character; note that
    //  eps automatically kills the odd-order generators of A.)
    //=======================================================================
    eps   := [ F2 | (AInt(A.t) mod 4) div 2 : t in evenT ];
    Vamb  := VectorSpace(F2, r2*d);
    Vgens := [ Vamb | ];
    for j in [1..d] do
        if invGab[evenJ[j]] mod 4 ne 0 then continue; end if;   // need 4 | m_j
        v := Vamb ! 0;
        for ti in [1..r2] do
            v[(ti - 1)*d + j] := eps[ti];
        end for;
        Append(~Vgens, v);
    end for;
    Vspan := sub< Vamb | Vgens >;

    //=======================================================================
    //  Kernel of the covering:  ~Br meet (W x V).  We express W meet K in
    //  the geometric coordinates x (w.r.t. the basis KB of K); elements of
    //  W outside K cannot occur in elements of ~Br and may be discarded.
    //=======================================================================
    WinK := Wspan meet K;
    WV   := sub< U |
        [ U | U ! (Coordinates(K, K ! w) cat [ F2 | 0 : i in [1..r2*d] ])
            : w in Basis(WinK) ]
        cat
        [ U | U ! ([ F2 | 0 : i in [1..m] ] cat Eltseq(v))
            : v in Basis(Vspan) ] >;

    KerCover := BrTilde meet WV;

    // The note asks for an orthogonal complement of the kernel in ~Br;
    // over F_2 an orthogonal complement need not be a complement (isotropic
    // vectors), so we take a genuine vector space complement, whose
    // elements are honest coset representatives for
    //     Br_C(BG) = ~Br / KerCover  =  (Z/2)^Dimension(Br).
    Br := Complement(BrTilde, KerCover);

    data := rec< BrBGRF |
        G := G, reps := reps, n := n,
        A := A, amap := amap, Selts := Selts, Nelts := Nelts, Ns := Ns,
        CM := CM, H2 := H2, M := M,
        K := K, KB := KB,
        Gab := Gab, abmap := abmap, invGab := invGab, evenJ := evenJ,
        evenT := evenT, d := d, r2 := r2,
        Mgeo := Mgeo, Malg := Malg,
        BrTilde := BrTilde, KerCover := KerCover, Br := Br,
        Wspan := Wspan, Vspan := Vspan >;

    return Br, data;
end function;

//---------------------------------------------------------------------------
// Convenience: ramify at every nontrivial conjugacy class.
//---------------------------------------------------------------------------
function BrauerGroupBGFull(G)
    return BrauerGroupBG(G, [ c[3] : c in Classes(G) | c[1] ne 1 ]);
end function;

//---------------------------------------------------------------------------
// Split an element u of ~Br (a vector in F_2^{m + r2*d}) into its pair:
//   b1 in H^2(G, Z/2)   (an element of data`H2),
//   b2 as an r2 x d matrix over F_2: row ti = the values of b2(A.t) on the
//       basis characters chi_j of \hat G[2], for t = data`evenT[ti].
//---------------------------------------------------------------------------
function SplitBrauerElement(data, u)
    F2 := GF(2);
    m  := #data`KB;
    r2 := data`r2;
    d  := data`d;
    b1 := data`H2 ! 0;
    for i in [1..m] do
        if u[i] eq 1 then b1 +:= data`H2 ! Eltseq(data`KB[i]); end if;
    end for;
    b2 := Matrix(F2, r2, d, [ u[m + i] : i in [1..r2*d] ]);
    return b1, b2;
end function;

//---------------------------------------------------------------------------
// Human-readable description of an element of ~Br (in particular of Br).
//---------------------------------------------------------------------------
procedure DescribeBrauerElement(data, u)
    b1, b2 := SplitBrauerElement(data, u);
    printf "b1 in H^2(G, Z/2)            : %o\n", b1;
    printf "b2 in Hom(Gal, G^[2]), where G^[2] has one basis character per\n";
    printf "even invariant factor %o of G^ab:\n",
        [ data`invGab[j] : j in data`evenJ ];
    if data`r2 eq 0 then
        printf "   (the Galois group has no even-order generators: b2 = 0)\n";
    end if;
    for ti in [1..data`r2] do
        t := data`evenT[ti];
        printf "   sigma_%o = %o mod %o  |->  character with value vector %o\n",
            t, Integers() ! data`amap(data`A.t), 2*data`n, Eltseq(b2[ti]);
    end for;
end procedure;

//---------------------------------------------------------------------------
// Reconstruct the extension and the marking attached to (the b1-part of)
// an element u of ~Br.  Returns:
//   P     : the central extension, as a permutation group,
//   pi    : the projection P -> G,
//   z     : the generator of the central kernel,
//   lifts : a sequence of lifts g~_i of the reps; the marking is
//           D_i = Class(P, lifts[i]).
//---------------------------------------------------------------------------
function MarkingData(data, u)
    b1 := SplitBrauerElement(data, u);
    P, pi, z := ExtensionData(data`CM, b1);
    lifts := [ P | g @@ pi : g in data`reps ];
    return P, pi, z, lifts;
end function;

/////////////////////////////////////////////////////////////////////////////
//  EXAMPLE
//
//    > load "BrBG.m";
//    // the quaternion group Q8, ramified at every nontrivial class:
//    > G := PermutationGroup< 8 | (1,2,4,7)(3,6,8,5), (1,3,4,8)(2,5,7,6) >;
//    > Br, data := BrauerGroupBGFull(G);
//    > Dimension(Br);
//    > for b in Basis(Br) do DescribeBrauerElement(data, b); end for;
//    > Dimension(data`BrTilde), Dimension(data`KerCover);
//
//  or, ramifying only at selected classes:
//
//    > G := Sym(4);
//    > reps := [ G!(1,2), G!(1,2,3,4) ];        // transpositions + 4-cycles
//    > Br, data := BrauerGroupBG(G, reps);
/////////////////////////////////////////////////////////////////////////////
