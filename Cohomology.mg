ZZ:=Integers();
Ghat:=[4]; // Ghat needs to be specified as a sequence of elem divisors
N:=2*(&*Ghat); // Proposed cyclotomic field we are computing H1 over

Gamma,m:=UnitGroup(Integers(N)); // m has domain Gamma, this is the Galois group
m_inv:=Inverse(m);
Gamma_perm := AbelianGroup(GrpPerm, [Order(Gamma.i) : i in [1..Ngens(Gamma)]]); // Galois group as permutation group
mats:=[(ZZ!m(Gamma.i))*IdentityMatrix(ZZ, #Ghat) : i in [1..Ngens(Gamma)]]; // Specifying action of Gamma on Ghat

CM := CohomologyModule(Gamma_perm, Ghat, mats);
H1:=CohomologyGroup(CM,1); 

// If we want to evaluate an element of H1 on an integer ell which is coprime to N
function eval_H1(f,ell)
    F:=OneCocycle(CM, f);
    return F(<&*[Gamma_perm.i^(Eltseq(m_inv(ell))[i]) : i in [1..Ngens(Gamma)]]>);
end function;

// Testing H1.1 and H1.2
eval_H1(H1.1, 3);
eval_H1(H1.2, 5);


///////////////////////////////////////////////////////////////////////
//
///////////////////////////////////////////////////////////////////////

