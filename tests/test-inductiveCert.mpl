with(CertSatQM):

#printlevel := -1;
#printlevel := 8;

inductiveTest := proc(nat, f)
local test := inductiveCert(f, nat, x);
    print(test);
    return;
end proc;

testPO := proc(f, nat)
local factorable_sos, certPO := inductiveCert(f, nat, x);
local basis;
    print(">> factorable_sos", factorable_sos);
    for basis in [indices(certPO, 'nolist')] do
        if evalb(certPO[basis] = 0) = false then
            lprint(">> basis", basis);
            lprint(">> sos multiplier", certPO[basis]);
        end if;
    end do;
    print(certPO);
end proc;

nat := [x+1, (x-1)*(x-2), (x-2)*(x-3), -(x-4)];
f := (x+3)*(x+1)*(x+2)*(x-3/2)^5*(x-4/3)^3*(x-17/12)^2*(x-297/221)*(x-170/149)*(x-67/48)*(x-359/336)*(x-4)*(x-5);
inductiveTest(nat, f);

nat := [x-1, (x-2)*(x-3), -(x-4)];
p := case_3_4(1, 2, 3, 4, nat, x);

nat := [x-1, (x-2)*(x-3), -(x-5)];
p := case_3_4(1, 2, 3, 5, nat, x);
print(p);

nat := [x-1, (x-2)*(x-3), (x-4)*(x-5) -(x-6)];
p := case_3_5(1, 2, 3, 4, 5, 6, nat, x);
print(p);

#print(">>", gen_nat_gens([-(x-1)*(x-2)*(x-3)*(x-4)*(x-5)^2], x));
