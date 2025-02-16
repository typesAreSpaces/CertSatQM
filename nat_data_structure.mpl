with(combinat, powerset);
with(Bits, And, Split, Xor);

# The data structure
# is table([<binary-prod-repr = coeff>])

zeroPO := proc(nat)
local elem, i, l;
  l := 2^nops(nat) - 1;
  po := table();
  for i from 0 to l do
    po[i] := 0;
  end do;
  return po;
end proc; 

# Input:
# nat is the natural generator basis
# encoded as a list of polynomials
unitPO := proc(nat)
local output := zeroPO(nat);
  output[0] := 1;
  return output;
end proc;

updatePONatEntry := proc(po, nat_i, new_element)
  po[nat_i] := new_element;
  return;
end proc;

# Input:
# nat is the natural generator basis
# encoded as a list of polynomials
addPO := proc(p1, p2, nat)
local i;
local output := zeroPO(nat);
local _indices := [indices(p1, 'nolist')];
  for i from 1 to nops(_indices) do
    output[_indices[i]] := p1[_indices[i]] + p2[_indices[i]];
  end do;
  return output;
end proc;

# Input:
# nat is the natural generator basis
# encoded as a list of polynomials
scalarProdPO := proc(p1, sos, nat, x)
local i;
local output := zeroPO(nat);
local _indices := [indices(p1, 'nolist')];
  for i from 1 to nops(_indices) do
    output[_indices[i]] := sos*p[_indices[i]];
  end do;
  return output;
end proc;

hashToPoly := proc(n, nat)
local size := nops(nat), k;
local _bits := Split(n, bits=size);
local output := 1;

  for k from 1 to size do
    if _bits[k] = 1 then
      output := output*nat[k];
    end if;
  end do;

  return output;
end proc;

# TODO: Improve this method
# by hashconsing the hashToPoly method using a global table.
# Input:
# nat is the natural generator basis
# encoded as a list of polynomials
prodPO := proc(p1, p2, nat, x)
local i, j, k;
local output := zeroPO(nat);
local size := nops(nat);
local l := 2^size - 1;

local sos; 
local sos_bits;

  for i from 0 to l do
    for j from 0 to l do
      if evalb(i = j) then
        output[0] := 
          output[0] + hashToPoly(i, nat)^2*p1[i]*p2[i];
      else
        sos_bits := Split(And(i, j), bits=size);
        sos := 1; 
        for k from 1 to size do
          if sos_bits[k] = 1 then
            sos := sos*hashToPoly(k, nat)^2;
          end if;
        end do;
        output[Xor(i, j)] :=
          output[Xor(i, j)] + sos*p1[i]*p2[j];
      end if;
    end do;
  end do;
  return output;
end proc;

nat := [x+3, (x+3)*(x-3), -(x-3)];
zero := zeroPO(nat);
one := unitPO(nat);
two := addPO(one, one, nat);
print(two);
another_two := scalarProdPO(one, 2, nat, x);
print(another_two);

g1 := zeroPO(nat);
updatePONatEntry(g1, 1, 1);
print(g1);

g1_1 := addPO(one, g1, nat);
print(g1_1);

test := prodPO(g1, g1_1, nat, x);
print(test);

#print(nat);
#for k from 0 to 7 do
  #test1 := hashToPoly(k, nat);
#end do;
