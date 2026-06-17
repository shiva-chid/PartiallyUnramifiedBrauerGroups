// SetProfile(true);
load "../main.mg";

procedure printdata(R)
    printf "BrauerGroup: %o\nExtra factor: %o\n\n", AbelianInvariants(R`Btilde), AbelianInvariants(R`Gabmod2);
end procedure;

procedure printheader(name)
    printf "\n----------------------------------------\n" cat name cat "\n----------------------------------------\n";
end procedure;


printheader("SYMMETRIC GROUPS WITH TRANSPOSITIONS");
for n in [4..9] do
    G:=Sym(n);
    C:=[G!(1,2)];
    R:=Btilde(G,C);
    printf "S_%o\n", n;
    printdata(R);
end for;

printheader("ALTERNATING GROUPS WITH THREE-CYCLES");
for n in [4..9] do
    G:=Alt(n);
    C:=[G!(1,2,3)];
    R:=Btilde(G,C);
    printf "A_%o\n", n;
    printdata(R);
end for;

printheader("CYCLIC GROUPS WITH ALL ELEMENTS");
for k in [1..9] do
    n:=2^k;
    G:=CyclicGroup(n);
    C:=[g: g in G| g ne Id(G)];
    R:=Btilde(G,C);
    printf "C_%o\n", n;
    printdata(R);
end for;

printheader("CYCLIC GROUPS WITH INVERTIBLE ELEMENTS");
for k in [1..9] do
    n:=2^k;
    G:=CyclicGroup(n);
    C:=[G.1^k : k in [1..n] | IsOdd(k)];
    R:=Btilde(G,C);
    printf "C_%o\n", n;
    printdata(R);
end for;

printheader("BICYCLIC GROUPS WITH ALL ELEMENTS");
for k in [1..6] do
    n:=2^k;
    G:=PermutationGroup(AbelianGroup([n,n]));
    C:=[g: g in G| g ne Id(G)];
    R:=Btilde(G,C);
    printf "C_%o x C_%o\n", n, n;
    printdata(R);
end for;

printf "\n----------------------------------------\nSPECIAL GROUP\n----------------------------------------\n";
    G:=PermutationGroup(FPGroup(SmallGroup(32,5)));
    g:=Random(G);
    while Order(g) ne 8 do g:=Random(G); end while; 
    C:=[x[3] : x in ConjugacyClasses(G) | x[1] eq 8];
    R:=Btilde(G,C);
    printf "%o\n", GroupName(G);
    printdata(R);


// G := ProfileGraph();
// ProfilePrintByTotalTime(G);
