load "main.mg";

procedure printdata(R)
    printf "BrauerGroup: %o\nExtra factor: %o\n\n", AbelianInvariants(R`Btilde), AbelianInvariants(R`Gabmod2);
end procedure;

printf "\n----------------------------------------\nSYMMETRIC GROUPS WITH TRANSPOSITIONS\n----------------------------------------\n";
for n in [4..8] do
    G:=Sym(n);
    C:=[G!(1,2)];
    R:=Btilde(G,C);
    printf "S_%o\n", n;
    printdata(R);
end for;

printf "\n----------------------------------------\nALTERNATING GROUPS WITH THREE-CYCLES\n----------------------------------------\n";
for n in [4..9] do
    G:=Alt(n);
    C:=[G!(1,2,3)];
    R:=Btilde(G,C);
    printf "A_%o\n", n;
    printdata(R);
end for;

printf "\n----------------------------------------\nCYCLIC GROUPS WITH ALL ELEMENTS\n----------------------------------------\n";
for k in [1..7] do
    n:=2^k;
    G:=CyclicGroup(n);
    C:=[g: g in G| g ne Id(G)];
    R:=Btilde(G,C);
    printf "C_%o\n", n;
    printdata(R);
end for;

printf "\n----------------------------------------\nBICYCLIC GROUPS WITH ALL ELEMENTS\n----------------------------------------\n";
for k in [1..7] do
    n:=2^k;
    G:=AbelianGroup([n,n]);
    C:=[g: g in G| g ne Id(G)];
    R:=Btilde(G,C);
    printf "C_%o^2\n", n;
    printdata(R);
end for;


// for GC in testgroups do
//     R:=Btilde(GC[1],GC[2]);
//     // print G;
//     // print C;
//     print GroupName(GC[1]);
//     print R`Btilde;
//     print "";
// end for;



//     G:=CyclicGroup(4);
//     C:=[ G.1, G.1^3 ];
// Append(~testgroups, [*G,C*]);
//     G:=CyclicGroup(8);
//     C:=[ g : g in G | g ne Id(G)];
// Append(~testgroups, [*G,C*]);
//     G:=Sym(4);
//     C:=[ G!(1,2), G!(1,2,3) ];
// Append(~testgroups, [*G,C*]);
//     G:=Alt(4);
//     C:=[ G!(1,2,3), G!(1,2,4) ];
// Append(~testgroups, [*G,C*]);


// // procedure testsize(G,C)
// //     R := PartiallyRamifiedBrauerPairs(G, C);
// //     printf "Group: %o\nConjugacy Classes: %o\nSize of Brauer: %o\n\n", GroupName(G), C, #R`MatchingPairs;
// // end procedure;

// for GC in testgroups do
//     R:=Btilde(GC[1],GC[2]);
//     // print G;
//     // print C;
//     print GroupName(GC[1]);
//     print R`Btilde;
//     print "";
// end for;





