///////////////////////////////////////////////////////////////////////////
//
// h2_z2_central_extensions.m
//
// Compute H^2(G, F_2) with trivial G-action and construct the central
// extension represented by any chosen cohomology class.
//
// Supported input group types:
//     GrpPerm   finite permutation groups
//     GrpMat    finite matrix groups
//     GrpPC     finite polycyclic groups
//
///////////////////////////////////////////////////////////////////////////

// G  is the group actually used by the cohomology code.
// M  is the one-dimensional trivial F_2[G]-module.
// CM is MAGMA's cohomology-module object.
// H2 is the vector space H^2(G, F_2).
H2Z2DataFormat := recformat< G, M, CM, H2 >;


///////////////////////////////////////////////////////////////////////////
// H2Z2Data(G)
//
// Return all reusable data needed for H^2(G, F_2) and its extensions.
//
// For a pc group, MAGMA requires a conditioned pc presentation.  The call
// to ConditionedGroup has no effect if G is already conditioned.
///////////////////////////////////////////////////////////////////////////

H2Z2Data := function(G)
    supported_types := { GrpPerm, GrpMat, GrpPC };
    if not Type(G) in supported_types then
        error "G must be a finite permutation, matrix, or pc group";
    end if;

    if Type(G) eq GrpPC then
        G := ConditionedGroup(G);
    end if;

    F2 := GF(2);
    M  := TrivialModule(G, F2);
    CM := CohomologyModule(G, M);
    H2 := CohomologyGroup(CM, 2);

    return rec< H2Z2DataFormat |
        G := G, M := M, CM := CM, H2 := H2 >;
end function;


///////////////////////////////////////////////////////////////////////////
// H2ClassFromCoordinates(D, coordinates)
//
// The vector space D`H2 has a basis selected by MAGMA.  A class is therefore
// specified by a sequence such as [1, 0, 1].  Entries are reduced in F_2.
///////////////////////////////////////////////////////////////////////////

H2ClassFromCoordinates := function(D, coordinates)
    if #coordinates ne Dimension(D`H2) then
        error "The number of coordinates must equal Dimension(D`H2)";
    end if;

    return D`H2 ! coordinates;
end function;


///////////////////////////////////////////////////////////////////////////
// RepresentativeTwoCocycle(D, c)
//
// Return a representative 2-cocycle alpha for the class c.
//
// Evaluate it by:
//     alpha(<g, h>)
//
// The result is an element of the one-dimensional module D`M.  Its single
// F_2 coordinate is:
//     alpha(<g, h>)[1]
///////////////////////////////////////////////////////////////////////////

RepresentativeTwoCocycle := function(D, c)
    if not Parent(c) cmpeq D`H2 then
        error "c must be an element of D`H2";
    end if;

    return TwoCocycle(D`CM, c);
end function;


///////////////////////////////////////////////////////////////////////////
// CentralExtensionFromClass(D, c : PermutationModel := false)
//
// Construct the extension represented by c:
//
//                  iota                pi
//     1 ----> C_2 ----> E ----------------> G ----> 1.
//
// Returns:
//     E       the middle group
//     pi      the surjective homomorphism E -> G
//     iota    the injective homomorphism C_2 -> E
//
// If G is a permutation or matrix group, the default E is finitely
// presented.  Set PermutationModel := true to ask MAGMA for a permutation
// group, which is usually more convenient for finite-group computations.
//
// If G is a pc group, leave PermutationModel equal to false; MAGMA then
// constructs E as a pc group.
///////////////////////////////////////////////////////////////////////////

CentralExtensionFromClass := function(D, c : PermutationModel := false)
    if not Parent(c) cmpeq D`H2 then
        error "c must be an element of D`H2";
    end if;

    if PermutationModel then
        if not Type(D`G) in { GrpPerm, GrpMat } then
            error "PermutationModel is available only for permutation or matrix groups";
        end if;

        if IsZero(c) then
            E, pi, iota := SplitExtension(GrpPerm, D`CM);
        else
            E, pi, iota := Extension(GrpPerm, D`CM, c);
        end if;
    else
        if IsZero(c) then
            E, pi, iota := SplitExtension(D`CM);
        else
            E, pi, iota := Extension(D`CM, c);
        end if;
    end if;

    return E, pi, iota;
end function;


///////////////////////////////////////////////////////////////////////////
// PrintH2Z2Summary(D)
//
// Print the dimension, order, and MAGMA basis of H^2(G, F_2).
///////////////////////////////////////////////////////////////////////////

PrintH2Z2Summary := procedure(D)
    printf "H^2(G, F_2) is an F_2-vector space of dimension %o.\n",
        Dimension(D`H2);
    printf "It has %o cohomology classes.\n", #D`H2;
    print "MAGMA's chosen basis is:";
    print Basis(D`H2);
end procedure;
