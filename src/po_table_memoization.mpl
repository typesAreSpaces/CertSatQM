with(combinat, permute);
with(Bits, Split, Join);

local gens;

#gens := [x+1, (x+1)*(x-1), (x-1)*(x-2), -(x-2)];
gens := [x+3, (x+2)*(x+1), (x-1)*(x-2), -(x-3)];

local output;
local num_gens, i;
local curr_index, extra, curr_length, num_ones;
local curr_seq, fst_seq, snd_seq;

output := table();
num_gens := nops(gens);

# Base case n = 0
output[0] := 1;

# Base case n = 1
curr_index := 1;
for i from 1 to num_gens do
  output[curr_index] := gens[i];
  curr_index := 2*curr_index;
end do;

# Inductive case n = curr_length
curr_index := 1;
extra := 2;
for curr_length from 2 to num_gens do
  curr_index := curr_index + extra;
  extra := 2*extra;

  for curr_seq in permute(Split(curr_index, bits=num_gens)) do
    fst_seq := [];
    snd_seq := [];

    num_ones := 0;
    for i from 1 to num_gens do
      if num_ones < floor(curr_length/2) then
        fst_seq := [op(fst_seq), curr_seq[i]];
        snd_seq := [op(snd_seq), 0];
        if curr_seq[i] = 1 then
          num_ones := num_ones + 1;
        end if
      else
        fst_seq := [op(fst_seq), 0];
        snd_seq := [op(snd_seq), curr_seq[i]];
      end if;
    end do;

    output[Join(curr_seq)] := output[Join(fst_seq)]*output[Join(snd_seq)];
  end do;
end do;

print(output);

ok := module()
local big_table;
end module;
