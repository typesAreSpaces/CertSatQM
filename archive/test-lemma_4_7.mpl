restart;

with(CertSatQM);

#printlevel := -1;
#printlevel := 5;

basis := [x+3, (x+2)*(x-1), (x+1)*(x-2), -x+3];
 
semialg_nat := semiAlgebraicIntervals(basis, x);
nat := natGens(semialg_nat, x);

split_basis := splitBasis(basis, semialg_nat, x);
todo := extractInbetweenSplitFactors(split_basis[2], -2, 2, x);

#lemma_4_7 := proc(nat_gen, G_fix, a0, a, b, bl, x)
a0 := -3;
bl := 3;
a := -2;
b := 2;
lprint(lemma_4_7(todo, a0, a, b, bl, x));
