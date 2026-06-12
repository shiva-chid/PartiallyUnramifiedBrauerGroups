C2:=AbelianGroup([2]);
// G  is the group actually used by the cohomology code.
// C  is the list of elements representing the conjugacy classes
// M  is the one-dimensional trivial F_2[G]-module.
// H2 is the vector space H^2(G, F_2).
// CMH2 is MAGMA's cohomology-module object for H^2(G,F_2).
// H2Marked is the set of marked elements in H2.
DataFormat := recformat< G, C, M, H2, CMH2, H2Marked >;

function InitialiseDataStructure(G,C)
    F2 := GF(2);
    M  := TrivialModule(G, F2);
    CMH2 := CohomologyModule(G, M);
    H2 := CohomologyGroup(CMH2, 2);
    return rec< DataFormat | G := G, C := C, M := M, CMH2 := CMH2, H2 := H2 >;
end function;

function FindMarkedElements(R)
    winners:=[**];
    for beta in R`H2 do
        GbetaFP, phibetaFP, psibetaFP := Extension(R`CMH2, beta);
        Gbeta, isoToPerm := PermutationGroup(GbetaFP);
        phibeta := hom< Gbeta -> R`G | [ phibetaFP((Gbeta.i) @@ isoToPerm) : i in [1..Ngens(Gbeta)] ]>;
        success:=true;
        for g in R`C do
            // printf "g:%o, beta=%o\n", g, beta;
            _,gtilde:=HasPreimage(phibeta,g);
            ZGg:=Centraliser(R`G,g);
            for h in Generators(ZGg) do
                _,htilde:=HasPreimage(phibeta,h);
                if (gtilde, htilde) ne Id(Gbeta) then
                    success:=false;
                    // printf "ERROR:  %o\n", beta;
                    break;
                end if;
            end for;
            // print "help";
            if not success then break; end if;
        end for;
        if success then
            Append(~winners,beta);
        end if;
    end for;
    return winners;
end function;

// G:=Alt(4);
// // Gab,ab:=AbelianQuotient(G);
// C:=[G!(1,2,3),G!(1,2,4),G!(1,2)(3,4)];
// R:=InitialiseDataStructure(G,C);
G:=Sym(4);
C:=[G!(1,2,3)];
R:=InitialiseDataStructure(G,C);
R`H2Marked:=FindMarkedElements(R);
