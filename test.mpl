with(CertSatQM):

printlevel := -1;
#printlevel := 8;

_pwd := currentdir();
currentdir(homedir);
currentdir("Documents/GithubProjects/RealCertify");
read "multivsos/multivsos.mm";
currentdir(_pwd);

read "nat_gens.mpl";

testRealCertify := proc(f, basis)
  local out := multivsos_internal(
      f,
      epsilon=1,
      precSVD=10,
      precSDP=200,
      precOut=30,
      precIn=100,
      gmp=true,
      algo=2,
      glist=basis,
      relaxorder=0,
      denom=false);
end proc;

inductiveTest := proc(nat, f)
  test := inductiveCert(f, nat, x);
  print(test);
  return;
end proc;

testPO := proc(f, nat)
  factorable_sos, certPO := inductiveCert(f, nat, x);
  print(">> factorable_sos", factorable_sos);
  for basis in [indices(certPO, 'nolist')] do
    if evalb(certPO[basis] = 0) = false then
      lprint(">> basis", basis);
      lprint(">> sos multiplier", certPO[basis]);
    end if;
  end do;
  print(certPO);
end proc;

testQM := proc(f, nat, a_0, b_k, x)
  factorable_sos, certPO := inductiveCert(f, nat, x);
  local _temp;
  PO_2_QM := table();
  print(">> factorable_sos", factorable_sos);
  for basis in [indices(certPO, 'nolist')] do
    if evalb(certPO[basis] = 0) = false then
      if assigned(PO_2_QM[basis]) = false then
        PO_2_QM[basis] := unitQM(nat);
      end if;
      todo := split_basis_PO(basis, nat);
      #print(">> todo @ testQM", todo);
      for _todo in todo do
        _temp := zeroQM(nat);
        updateQMNatEntry(_temp, nat[_todo], 1);
        #print(">> _temp @ testQM", _temp);
        #print(">> before prodQM PO_2_QM[basis] @ testQM", PO_2_QM[basis]);
        PO_2_QM[basis] := prodQM(PO_2_QM[basis], _temp, a_0, b_k, nat, x);
        #print(">> after prodQM PO_2_QM[basis] @ testQM", PO_2_QM[basis]);
      end do;
    end if;
  end do;
  print(PO_2_QM);
  for basis in [indices(PO_2_QM, 'nolist')] do
    lprint(">> basis", basis);
    print(">> as a QM certificate", PO_2_QM[basis]);
  end do;
end proc;


#nat := [x+1, (x-1)*(x-2), (x-2)*(x-3), -(x-4)];
#f := (x+3)*(x+1)*(x+2)*(x-3/2)^5*(x-4/3)^3*(x-17/12)^2*(x-297/221)*(x-170/149)*(x-67/48)*(x-359/336)*(x-4)*(x-5);
#inductiveTest(nat, f);

#nat := [x-1, (x-2)*(x-3), -(x-4)];
#p := case_3_4(1, 2, 3, 4, nat, x);
#nat := [x-1, (x-2)*(x-3), -(x-5)];
#p := case_3_4(1, 2, 3, 5, nat, x);
#nat := [x-1, (x-2)*(x-3), (x-4)*(x-5) -(x-6)];
#p := case_3_5(1, 2, 3, 4, 5, 6, nat, x);
#print(p);

#print(">>", gen_nat_gens([-(x-1)*(x-2)*(x-3)*(x-4)*(x-5)^2], x));

nat := [x+6, (x+4)*(x+2), x*(x-2), -(x-4)];
testQM((x+7)*(x+3)*(x+5/2), nat, -6, 4, x);

#p := table([1 = 1, x + 6 = 0, x^2 + 6*x + 8 = 0, -x + 4 = 0, x^2 - 2*x = 0]);
#q := table([1 = 0, x + 6 = 1, x^2 + 6*x + 8 = 0, -x + 4 = 0, x^2 - 2*x = 0]);

#print(prodQM(p, q, -6, 4, nat, x));
