C2:=AbelianGroup([2]);
// G  is the group actually used by the cohomology code.
// C  is the list of elements representing the conjugacy classes
// M  is the one-dimensional trivial F_2[G]-module.
// H2 is the vector space H^2(G, F_2).
// CMH2 is MAGMA's cohomology-module object for H^2(G,F_2).
// H2Marked is the set of marked elements in H2.
DataFormat := recformat< G, C, M, H2, CMH2, H2Marked >;

function initialise(G,C)
    F2 := GF(2);
    M  := TrivialModule(G, F2);
    CMH2 := CohomologyModule(G, M);
    H2 := CohomologyGroup(CMH2, 2);
    return rec< DataFormat | G := G, C := C, M := M, CMH2 := CMH2, H2 := H2 >;
end function;

function FindMarkedElements(R)
    Gab,Gabmap:=AbelianQuotient(R`G);
    winners:=[**];
    for beta in R`H2 do
        Gbeta, phibeta, psibeta:= Extension(R`CMH2, beta);
        success:=true;
        for g in R`C do
            printf "g:%o, beta=%o\n", g, beta;
            _,gtilde:=HasPreimage(g,phibeta);
            ZGgab,ZGgabmap:=AbelianQuotient(Centraliser(R`G,g));
            for hab in Generators(ZGgab) do
                _,h:=HasPreimage(hab,ZGgabmap);
                _,htilde:=HasPreimage(h,phibeta);;
                if htilde*gtilde*htilde^(-1)*gtilde^(-1) ne Id(Gbeta) then
                    success:=false;
                    printf "ERROR:  %o\n", htilde*gtilde*htilde^(-1)*gtilde^(-1);
                    continue;
                end if;
            end for;
            if not success then continue; end if;
        end for;
        if success then
            Append(~winners,beta);
        end if;
    end for;
    return winners;
end function;


G:=Alt(4);
Gab,ab:=AbelianQuotient(G);
C:=[G!(1,2,3),G!(1,2,4),G!(1,2)(3,4)];
R:=initialise(G,C);
R`H2Marked:=FindMarkedElements(R);
