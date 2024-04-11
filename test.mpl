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

#splitBoundedCert := proc(split_gen, gen, x)
#ok := splitBoundedCert(x+3, -(x+3)*(x-3), x);
#lprint(expand(ok[1]*1 + ok[2]*(-(x+3)*(x-3))));

#splitUnboundedCert := proc(t1, gen, basis, a0, bl, x);

#ok1 := splitUnboundedCert(x+3, (x+3)*(x+2)*(x-1), basis, -3, 3, x);
#lprint(ok1);

ok2 := splitUnboundedCert((x+3)*(x+2), (x+3)*(x+2)*(x-2)*(x-3), basis, -3, 3, x);
lprint(">> ok2", ok2);
