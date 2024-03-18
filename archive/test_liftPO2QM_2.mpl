restart;

with(CertSatQM):

#printlevel := -1;
#printlevel := 5;

nat := [x+6, (x+4)*(x+2), x*(x-2), -(x-4)];
f1 := -x*(x-2)*(x-4);
f2 := -(x+4)*(x+2)*(x-4);
f3 := (x+4)*(x+2)*x*(x-2);
f4 := (x+4)*(x+2)*x*(x-2)*(-(x-4));
f5 := (x+6)*(x+4)*(x+2)*x*(x-2)*(-(x-4));

qmCert := certInQM(f1, nat, -6, 4, x);
#print(qmCert);
print(checkCorrectnessQM(qmCert, f1));
#print(simplify(fromQMtoPoly(qmCert)));

qmCert := certInQM(f2, nat, -6, 4, x);
#print(qmCert);
print(checkCorrectnessQM(qmCert, f2));
#print(simplify(fromQMtoPoly(qmCert)));

qmCert := certInQM(f3, nat, -6, 4, x);
#print(qmCert);
print(checkCorrectnessQM(qmCert, f3));
#print(simplify(fromQMtoPoly(qmCert)));

qmCert := certInQM(f4, nat, -6, 4, x);
#print(qmCert);
print(checkCorrectnessQM(qmCert, f4));
lprint(simplify(fromQMtoPoly(qmCert)));

qmCert := certInQM(f5, nat, -6, 4, x);
#print(qmCert);
print(checkCorrectnessQM(qmCert, f5));
print(simplify(fromQMtoPoly(qmCert)));
