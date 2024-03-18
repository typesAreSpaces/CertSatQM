restart;

with(CertSatQM):

check := proc(f, nat, a, b, x)
    qmCert := certInQM(f, nat, a, b, x);
#print(qmCert);
    print(checkCorrectnessQM(qmCert, f));
#print(simplify(fromQMtoPoly(qmCert)));
end proc;

#printlevel := -1;
#printlevel := 5;

nat := [x, x*(x-1), (x-1)*(x-2), -(x-2)];

f := -81/16*x^4 + 369/16*x^3 - 63/2*x^2 + 19/2*x + 5;

check(f1, nat, -6, 4, x);
check(f2, nat, -6, 4, x);
check(f3, nat, -6, 4, x);
check(f4, nat, -6, 4, x);
check(f5, nat, -6, 4, x);
check(f6, nat, -6, 4, x);
