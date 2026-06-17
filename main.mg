// GLOBAL OBJECTS
// C2:=AbelianGroup([2]);


/////////////////////////////////////////////////////////////////////
// Data Structure stuff
//
// G             is the group actually used by the cohomology code.
// n             is 2|G|
// C             is the list of elements representing the conjugacy classes
// CStabilisers  is a list of stabilisers of the elements of C in order from Z/nZ^\times
// U             is the unit group of Z/n
// i             is the map from U to Z/n
// Umod2         is U modulo squares
// pi2           is the map from the unit group of Z/n to Umod2.
// Gabmod2       is G^ab/2G^ab
// F2            is the one-dimensional trivial F_2[G]-module.
// H2            is the vector space H^2(G, M).
// CMH2          is MAGMA's cohomology-module object for H^2(G, M).
// H2Marked      is the set of marked elements in H2, which are all geometric markings.
// H1            is H^1(Q(\zeta_n)/Q, \hat{G}[2])
// gensH         is the list whose j-th entry contains generators for the
//               image modulo squares of the stabiliser of C[j].
// M1            is the matrix representing res_C: H1\to \oplus_{g\in C} H^1(Q(\zeta_n)/Q, \hat{<g>})
// M2            is the matrix representing res_C: H2\to \oplus_{g\in C} H^1(Q(\zeta_n)/Q, \hat{<g>})
/////////////////////////////////////////////////////////////////////

BrauerDataFormat := recformat< G, n, C, CStabilisers, U, i, Umod2, pi2,
    gensH, Gabmod2, F2, H2, CMH2, H2Marked, H1, M1, M2, Btilde, Btildegens>;


/////////////////////////////////////////////////////////////////////
// Initialises data structure, and tests that the conjugacy classes
// generate G.
function InitialiseBrauerDataStructure(G,C)
    assert ncl< G | C > eq G; // verify that the conjugacy classes generate G
    n:=2*#G;
    Zn := Integers(n);
    ZZ := Integers();
    U, i := UnitGroup(Zn);
    Umod2, pi2 := ElementaryAbelianQuotient(U,2); // enough to work with this quotient, because we only consider homomorphisms to a 2-torsion group.
    s := Time();
    // Computing C-stabilizers naively. // This is an expensive step for large abelian groups like C_{2^10} or C_{2^6} x C_{2^6}
    CStabilisers:=[];
    for g in C do
        ordg := Order(g);
        Zg := Integers(ordg);
        Ug, ig := UnitGroup(Zg);
        g_stab:=sub<Ug|>;
        for x in Ug do
            if x in g_stab then continue; end if;
            if IsConjugate(G,g^(ZZ!ig(x)),g) then g_stab := sub<Ug|g_stab,x>; end if;
        end for;
        h := hom<U->Ug|[(Zg!i(U.j))@@ig : j in [1..Ngens(U)]]>;
        Append(~CStabilisers,g_stab@@h);
    end for;
    printf "Computing CStabilisers took: %o\n", Time(s);

    s := Time();
    gensH:=[];
    for H in CStabilisers do
        Hmod2:=sub<Umod2|[pi2(h):h in Generators(H)]>;
        Append(~gensH,[Umod2!Hmod2.i:i in [1..Ngens(Hmod2)]]);
    end for;
    printf "Generators for CStabilisers mod 2 took: %o\n", Time(s);

    return rec< BrauerDataFormat | G := G, C := C,
        CStabilisers:=CStabilisers, gensH:=gensH, n := n,
        U:=U, i:=i, Umod2:=Umod2, pi2:=pi2>; // creating the record also seems to be an expensive step for bicyclic groups C_{2^6} x C_{2^6}
end function;


/////////////////////////////////////////////////////////////////////
// Functions for the Brauer algorithm
/////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////
// Given an element beta of R`H2, tests whether the element is
// geometrically unramified.  Deprecated now.
function IsGeometricallyMarked(beta,R)
    GbetaFP,phibetaFP,psibetaFP:=Extension(R`CMH2,beta);
    Gbeta,isoToPerm:=PermutationGroup(GbetaFP);
    phibeta:=hom<Gbeta->R`G|[phibetaFP(Gbeta.i@@isoToPerm):i in [1..Ngens(Gbeta)]]>;

    for g in R`C do // here is where we construct the residue map at g
        success,gtilde:=HasPreimage(g,phibeta);
        assert success;
        ZGg:=Centraliser(R`G,g);
        for h in Generators(ZGg) do // this is what we feed the residue map
            success,htilde:=HasPreimage(h,phibeta);
            assert success;
            if (gtilde,htilde) ne Gbeta!1 then
                return false;
            end if;
        end for;
    end for;
    return true;
end function;


/////////////////////////////////////////////////////////////////////
// Assuming that R has already had computed H^2(G,C_2),
// Computes the subset that are marked.
procedure GetMarkedGeometricElements(~R)
    F2:=GF(2);
    R`F2:=TrivialModule(R`G,F2);
    s := Time();
    R`CMH2:=CohomologyModule(R`G,R`F2);
    printf "Computed CohomologyModule: %o\n", Time(s);
    s := Time();
    R`H2:=CohomologyGroup(R`CMH2,2);
    printf "Computed H2: %o\n", Time(s);
    rows:=[];
    for beta in Basis(R`H2) do
        beta_cocycle:=TwoCocycle(R`CMH2,beta);
        row:=[];
        for g in R`C do
            for h in Generators(Centraliser(R`G,g)) do
                Append(~row,(beta_cocycle(<g,h>)[1]+beta_cocycle(<h,g>)[1]));
            end for;
        end for;
        Append(~rows, row);
    end for;
    M:=Matrix(F2, rows);
    R`H2Marked:=sub<R`H2|Kernel(M)>;
end procedure;


procedure GetGeometricPart(~R)
// {Given
// - a group G
// - a list gis of representatives of conjugacy classes of G
// - a list His of subgroups of (Z/2|G|)^* stabilizing the conjugacy classes of gis
// - the cohomology module CM for the trivial G-module Z/2
// - the second cohomology group H^2(G, Z/2)
// returns the geometric Brauer residue map as a matrix over GF(2). Its action on rows represents
// the map from H^2(G, Z/2) to the direct sum of Hom(H, Z/2) for H in His.}
    s := Time();
    GetMarkedGeometricElements(~R);
    printf "GetMarkedGeometricElements took: %o\n", Time(s);

    H2basis:=[R`H2!x:x in Basis(R`H2Marked)];
    Ncols:=&+[#R`gensH[j]:j in [1..#R`C]];
    vals:=[];

    s := Time();
    for chi in H2basis do
        // for each basis element of H^2(G,Z/2), first produce the corresponding central extension.
        time extnFP,piFP,iotaFP:=Extension(R`CMH2,chi);

        time extn,isoToPerm:=PermutationGroup(extnFP); // this is an expensive step for large groups like A_n, S_n
        pi:=hom<extn->R`G|
            [piFP(extn.i@@isoToPerm):i in [1..Ngens(extn)]]>;

        val:=[];
        for j in [1..#R`C] do
            gi:=R`C[j];
            success,g:=HasPreimage(gi,pi);
            assert success;

            for x in R`gensH[j] do
                u:=Integers()!R`i(x@@R`pi2);

                Append(~val,IsConjugate(extn,g,g^u) select 0 else 1);
            end for;
        end for;
        Append(~vals,val);
    end for;
    printf "Constructing central extensions and Geometric residue map took: %o\n", Time(s);

    if #vals eq 0 then
        M2:=ZeroMatrix(GF(2),0,Ncols);
    else
        M2:=Matrix(GF(2),#vals,Ncols,&cat vals);
    end if;
    R`M2:=M2;
end procedure;


procedure GetAlgebraicPart(~R)
    Gabmod2,piabmod2:=ElementaryAbelianQuotient(R`G,2);
    A,phi:=Dual(Gabmod2); // A is the dual of G^ab/2*G^ab, so A is Gdual[2]. phi is the pairing G^ab/2*G^ab x A --> Z/2
    H1,psi:=Hom(R`Umod2,A); // this is the domain
    Ncols:=&+[#R`gensH[j]:j in [1..#R`C]];
    vals:=[];

    for i:=1 to Ngens(H1) do
        val:=[];

        for j in [1..#R`C] do
            gi:=R`C[j];

            for x in R`gensH[j] do
                Append(~val,phi(piabmod2(gi),psi(H1.i)(x)));
            end for;
        end for;
        Append(~vals,val);
    end for;

    if #vals eq 0 then
        M1:=ZeroMatrix(GF(2),0,Ncols);
    else
        M1:=Matrix(GF(2),#vals,Ncols,&cat vals);
    end if;

    R`Gabmod2:=Gabmod2;
    R`H1:=H1;
    R`M1:=M1;
end procedure;

/////////////////////////////////////////////////////////////////////
// Returns the H1 component of an element of the abstract Btilde group.
function BtildeAlgebraicComponent(x,R)
    coeffs:=Eltseq(x);
    a:=R`H1!0;
    for i in [1..#coeffs] do
        if coeffs[i] ne 0 then
            a+:=R`Btildegens[i][1];
        end if;
    end for;
    return a;
end function;


/////////////////////////////////////////////////////////////////////
// Returns the H2 component of an element of the abstract Btilde group.
function BtildeGeometricComponent(x,R)
    coeffs:=Eltseq(x);
    b:=R`H2!0;
    for i in [1..#coeffs] do
        if coeffs[i] ne 0 then
            b+:=R`Btildegens[i][2];
        end if;
    end for;
    return b;
end function;



/////////////////////////////////////////////////////////////////////
function Btilde(G,C)
// {Given
// - a group G
// - a list gis of representatives of conjugacy classes of G
// - a list His of subgroups of (Z/2|G|)^* stabilizing the conjugacy classes of gis
// - the cohomology module CM for the trivial G-module Z/2
// - the second cohomology group H^2(G, Z/2)
// returns
// - the abelian group H^1((Z/2|G|)^*, Gdual[2])=Hom(_,_)
// - H^2(G, Z/2)
// - a subspace of (F_2)^n where n is the sum of F_2-dimension of the first two return values.}
    s := Time();
    R:=InitialiseBrauerDataStructure(G,C);
    printf "InitialiseBrauerDataStructure took: %o\n", Time(s);
    GetGeometricPart(~R);
    GetAlgebraicPart(~R);
    M:=VerticalJoin(R`M1,R`M2);
    K:=Kernel(M);
    d1:=NumberOfRows(R`M1);
    d2:=NumberOfRows(R`M2);

    H2basis:=[R`H2!x:x in Basis(R`H2Marked)];
    Btilde_gens:=[];

    for v in Basis(K) do
        a:=R`H1!0;
        for i in [1..d1] do
            if v[i] ne 0 then a+:=R`H1.i; end if;
        end for;

        b:=R`H2!0;
        for i in [1..d2] do
            if v[d1+i] ne 0 then b+:=H2basis[i]; end if;
        end for;

        Append(~Btilde_gens,<a,b>);
    end for;

    // FIX: H1 and H2 do not have a suitable common Product parent.
    // Return an abstract elementary abelian group and the corresponding pairs.
    Btilde_group:=AbelianGroup([2:i in [1..Dimension(K)]]);
    R`Btilde:=Btilde_group;
    R`Btildegens:=Btilde_gens;
    return R;
end function;

