with(CertSatQM):

printlevel := -1;
#printlevel := 8;

nat := [x+6, (x+4)*(x+2), x*(x-2), -(x-4)];
f := (x+7)*(x+3)*(x+5/2);

qmCert := certInQM(f, nat, -6, 4, x);
print(qmCert);
print(checkCorrectnessQM(qmCert, f));
print(testRealCertify(f, [op(nat), 100-x^2]));

nat := [x+6, (x+4)*(x+2), x*(x-2), (x-4)*(x-6), -(x-9)];
f := (x+100)*(x+3)*(x+5/2);

qmCert := certInQM(f, nat, -6, 9, x);
print(qmCert);
print(checkCorrectnessQM(qmCert, f));

print(semiAlgebraicIntervals(nat, x));
