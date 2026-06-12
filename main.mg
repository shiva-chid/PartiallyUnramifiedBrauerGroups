// GLOBAL OBJECTS
// C2:=AbelianGroup([2]);


/////////////////////////////////////////////////////////////////////
// Data Structure stuff
//
// G        is the group actually used by the cohomology code.
// C        is the list of elements representing the conjugacy classes
// n        is 2|G|
// M        is the one-dimensional trivial F_2[G]-module.
// H2       is the vector space H^2(G, M).
// CMH2     is MAGMA's cohomology-module object for H^2(G, M).
// H2Marked is the set of marked elements in H2, which are all geometric markings.
// H1       is H^1(Q(\zeta_n)/Q, \hat{G}[2])
/////////////////////////////////////////////////////////////////////
BrauerDataFormat := recformat< G, C, n, M, H2, CMH2, H2Marked, H1 >;


/////////////////////////////////////////////////////////////////////
// Initialises data structure, and tests that the conjugacy classes
// generate G.
function InitialiseBrauerDataStructure(G,C)
    assert ncl< G | C > eq G; // verify that the conjugacy classes generate G
    return rec< BrauerDataFormat | G := G, C := C, n := 2*#G>;
end function;


/////////////////////////////////////////////////////////////////////
// Functions for the Brauer algorithm
/////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////
// Computes H^2(G,C_2) and associated objects.
procedure GetH2G_C2(~R)
    F2 := GF(2);
    R`M  := TrivialModule(R`G, F2);
    R`CMH2 := CohomologyModule(R`G, R`M);
    R`H2 := CohomologyGroup(R`CMH2, 2);
end procedure;

/////////////////////////////////////////////////////////////////////
// Given an element beta of R`H2, tests whether the element is 
// geometrically unramified.
function IsGeometricallyMarked(beta, R)
    GbetaFP, phibetaFP, psibetaFP := Extension(R`CMH2, beta);
    Gbeta, isoToPerm := PermutationGroup(GbetaFP);
    phibeta := hom< Gbeta -> R`G | [ phibetaFP((Gbeta.i) @@ isoToPerm) : i in [1..Ngens(Gbeta)] ]>;
    success:=true;
    for g in R`C do // here is where we construct the residue map at g
        _,gtilde:=HasPreimage(phibeta,g);
        ZGg:=Centraliser(R`G,g);
        for h in Generators(ZGg) do // this is what we feed the residue map
            _,htilde:=HasPreimage(phibeta,h);
            if (gtilde, htilde) ne Id(Gbeta) then
                success:=false;
                break;
            end if;
        end for;
        if not success then break; end if;
    end for;
    return success;
end function;

/////////////////////////////////////////////////////////////////////
// Assuming that R has already had computed H^2(G,C_2),
// Computes the subset that are marked.
procedure GetMarkedGeometricElements(~R)
    winners:=[];
    for beta in R`H2 do        
        if IsGeometricallyMarked(beta,R) then
            Append(~winners,beta);
        end if;
    end for;
    R`H2Marked:=sub< R`H2 | winners>;
end procedure;

/////////////////////////////////////////////////////////////////////
// Computes H^1(Q(\zeta_n)/Q), \hat{G}[2])
procedure GetAlgebraicElements(~R)
    Zn := Integers(n);
    U, Umap := UnitGroup(Zn);
    Hsmod2 := [pi2(H) : H in Hs];
    gensH := &cat[[H.i : i in [1..Ngens(H)]] : H in Hsmod2];

    Gab, piab := AbelianQuotient(G);
    Gabmod2, piabmod2 := ElementaryAbelianQuotient(Gab,2);
    A, phi := Dual(Gabmod2);
    dimA := #AbelianInvariants(A);

    H1, psi := Hom(Umod2,A);
    val := [&cat[[phi(piabmod2(piab(gi)),psi(H1.i)(x)) : x in gensH] : gi in gis] : i in [1..Ngens(H1)]];

    return H1, A, val;
end procedure;
// G:=Alt(4);
// // Gab,ab:=AbelianQuotient(G);
// C:=[G!(1,2,3),G!(1,2,4),G!(1,2)(3,4)];
// R:=InitialiseDataStructure(G,C);
G:=Sym(4);
C:=[G!(1,2)];
R:=InitialiseBrauerDataStructure(G,C);
GetH2G_C2(~R);
GetMarkedGeometricElements(~R);

GG:=sub<R`H2|R`H2Marked>;
