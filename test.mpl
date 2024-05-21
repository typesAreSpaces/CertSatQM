restart;

with(CertSatQM);

#printlevel := -1;
#printlevel := 5;

basis := [(x+3)*(x+2)*(x-1), -(x+1)*(x-2)*(x-3)];
#basis := [x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3];
 
semialg_nat := semiAlgebraicIntervals(basis, x);
nat := natGens(semialg_nat, x);

split_basis := splitBasis(basis, semialg_nat, x);
todo := extractInbetweenSplitFactors(split_basis[2], -2, 2, x);

test1 := splitBoundedCert(x+3, -(x+3)*(x-3), x);
lprint(">> test1", test1);
lprint(expand(test[1]*1 + test[2]*(-(x+3)*(x-3))));

# Terminates
test2 := splitUnboundedCert(x+3, (x+3)*(x+2)*(x-1), basis, -3, 3, x);
lprint(">> test2", test2);

# Terminates
#test3 := splitUnboundedCert((x+3)*(x+2), (x+3)*(x+2)*(x-2)*(x-3), basis, -3, 3, x);
#lprint(">> test3", test3);

#basis := [x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3];
 
#semialg_nat := semiAlgebraicIntervals(basis, x);
#nat := natGens(semialg_nat, x);

#split_basis := splitBasis(basis, semialg_nat, x);
#todo := extractInbetweenSplitFactors(split_basis[2], -2, 2, x);
#lprint(todo);

##lemma_4_7 := proc(nat_gen, G_fix, a0, a, b, bl, x)
#a0 := -3;
#bl := 3;
#a := -2;
#b := 2;
#lprint(lemma_4_7(todo, a0, a, b, bl, x));
