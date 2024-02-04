with(CertSatQM):

#printlevel := -1;
#printlevel := 8;

test1 := proc(nat)
  unit := unitPO(nat);
  test1 := prodPO(unit, unit, nat, x);
  print(test1);
  return;
end proc;

test2 := proc(nat, f)
  test := inductiveCert(f, nat, x);
  print(test);
  return;
end proc;

nat := [x+1, (x-1)*(x-2), (x-2)*(x-3), -(x-4)];
f := (x+3)*(x+1)*(x+2)*(x-3/2)^5*(x-4/3)^3*(x-17/12)^2*(x-297/221)*(x-170/149)*(x-67/48)*(x-359/336)*(x-4)*(x-5);

#test2(nat, f);

nat := [x-1, (x-2)*(x-3), -(x-4)];
p := cases(1, 2, 3, 4, nat, x);

#nat := [x-1, (x-2)*(x-3), -(x-5)];
#p := cases(1, 2, 3, 5, nat, x);
