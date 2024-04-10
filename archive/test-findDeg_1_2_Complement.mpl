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

#splitUnboundedCert := proc(t1, gen, basis, a0, bl, x)
#ok := splitUnboundedCert(x+3, (x+3)*(x+2)*(x-1), basis, -3, 3, x);
#lprint(ok);

#f1 := (x+2)*(x+1);
#sigma, tau, h := findDeg2Complement(f1, 0, 0, x);
#lprint(expand(sigma*f + tau*h));
#sigma, tau, h := findDeg2Complement(f1, -20, 20, x);
#lprint(expand(sigma*f + tau*h));

f2 := (x+2)*x^2*(x+1);
sigma, tau, h := findDeg2Complement(f2, -20, 20, x);
lprint(expand(evala(sigma*f2 + tau*h)));
sigma, tau, h := findDeg2Complement(f2, -3, 3, x);
lprint(expand(evala(sigma*f2 + tau*h)));

f3 := (x+2)*x*(x+1)^2;
sigma, tau, h := findDeg2Complement(f3, -20, 20, x);
lprint(expand(evala(sigma*f3 + tau*h)));
sigma, tau, h := findDeg2Complement(f3, -3, 3, x);
lprint(expand(evala(sigma*f3 + tau*h)));
