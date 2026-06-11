load "ChatGPT_implementation.mg";

testgroups := [* *];
    G:=CyclicGroup(4);
    C:=[ G.1, G.1^3 ];
Append(~testgroups, [*G,C*]);
    G:=CyclicGroup(8);
    C:=[ g : g in G | g ne Id(G)];
Append(~testgroups, [*G,C*]);
    G:=Sym(4);
    C:=[ G!(1,2), G!(1,2,3) ];
Append(~testgroups, [*G,C*]);
    G:=Alt(4);
    C:=[ G!(1,2,3), G!(1,2,4) ];
Append(~testgroups, [*G,C*]);


procedure testsize(G,C)
    R := PartiallyRamifiedBrauerPairs(G, C);
    printf "Group: %o\nConjugacy Classes: %o\nSize of Brauer: %o\n\n", GroupName(G), C, #R`MatchingPairs;
end procedure;

for GC in testgroups do
    testsize(GC[1],GC[2]);
end for;





