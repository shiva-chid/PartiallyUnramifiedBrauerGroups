\\ Generates the conjugacy classes of G from the representatives of Creps.
function GenerateCSets(G, Creps)
    Csets := [];
    reps := AssociativeArray();
    e := Id(G);
    for g in Creps do
        if g eq e then
            continue;
        end if;
        C := Class(G, g);
        if C notin Csets then
            Append(~Csets, C);
            reps[C] := g;
        end if;
    end for;
    return reps, Csets;
end function;

\\ Checks whether the representatives of Creps generate G.
function Validate(G, Creps)
    reps, Csets := GenerateCSets(G, Creps);
    if #Csets eq 0 then
        return false, "C is empty after removing identity.";
    end if;
    // Check whether the representatives normally generate G.
    repslist := [G | reps[C] : C in Csets];
    N := ncl< G | repslist >;
    if N eq G then
        return true, "C generates the group G.";
    end if;
    return false, "C does not generate the group G.";
end function;


N := Exp(G) * 2;
R := Integers(N);
U, phi := UnitGroup(R);
U2 := SylowSubgroup(U, 2);

\\ Generates representatives of the orbits of the powering action on the conjugacy classes of G.
\\ Also keeps track of the stabilizers of the powering action.
function PowerRepresentative(G, reps, Csets)
    Remaining := {1..#Csets};
    PowerReps := AssociativeArray();
    PowerCsets := [];
    Kernels := AssociativeArray();
    while not IsEmpty(Remaining) do
        i := Representative(Remaining);
        Exclude(~Remaining, i);
        C := Csets[i];
        Append(~PowerCsets, C);
        PowerReps[C] := reps[C];
        stabilizerElements := [U2 | ];
        for u in U do
            k := Integers() ! phi(u);
            y := reps[C]^k;
            // Record elements of U2 that stabilize C under the powering action.
            if u in U2 and y in C then
                Append(~stabilizerElements, U2 ! u);
            end if;
            // Remove the conjugacy class which are in the same orbit as C in the powering action.
            for j in Setseq(Remaining) do
                if y in Csets[j] then
                    Exclude(~Remaining, j);
                    break;
                end if;
            end for;
        end for;
        Kernels[C] := sub<U2 | stabilizerElements>;
    end while;
    return PowerCsets, PowerReps, Kernels;
end function;
