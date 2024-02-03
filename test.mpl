with(CertSatQM):

#printlevel := -1;
#printlevel := 8;

nat := [x+1, (x-1)*(x-2), (x-2)*(x-3), -(x-4)];
f := (x+2)*(x-3/2)^5*(x-4/3)^3*(x-17/12)^2*(x-297/221)*(x-170/149)*(x-67/48)*(x-359/336);

inductiveCert(f, nat, x);

#nat := [x+1, (x-2)*(x-3), -(x-4)];

#notZero := zeroPO(nat);
#updateNatEntry(notZero, x+1, 2);
#test := addPO(notZero, notZero, nat);
#print(test);

#test1 := prodPO(notZero, notZero, nat, x);
#print(test1);

#test2 := prodPO(notZero, test1, nat, x);
#print(test2);

#updateNatEntry(test2, -(x-4), 2);

#test3 := prodPO(test2, test2, nat, x);
#print(test3);

unit := unitPO(nat);
test1 := prodPO(unit, unit, nat, x);
print(test1);
