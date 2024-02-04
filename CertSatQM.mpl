$define ENABLE_DEBUGGING true

$define DEBUG(F, L, y, x) if (y) then lprint("Debugging file ", F, " at line ", L); x; end if

with(combinat, powerset);
with(SolveTools, SemiAlgebraic);
with(RegularChains, SemiAlgebraicSetTools, PolynomialRing);
with(SemiAlgebraicSetTools, IsEmpty);

#_pwd := currentdir();
#currentdir(homedir);
#currentdir("Documents/GithubProjects/RealCertify");

#read "univsos/univsos1.mm";
#read "univsos/univsos2.mm";
#read "univsos/univsos3.mm";

#currentdir(_pwd);

CertSatQM := module() option package;

local sqf;

local auxiliarSosStep;
export zeroPO, unitPO, updateNatEntry, addPO, prodPO;

local semiAlgebraicIntervals;
local ord, boundInfo;
local decompositionFromBasis;

local checkMembership;
local lemma_1_5;
local natGens;

local checkSosMultipliers;
local checkCorrectness;

export inductiveCert;

# products of the form (x-a), -(x-b), a \leq b
local case_3_1;

# products of the form (x-a), (x-a)(x-b), a < b
local case_3_2;

# products of the form (x-a)(x-b), (x-b)(x-c), a < b < c
local case_3_3;

local lemma_3_1;
local lemma_3_2;
# products of the form (x-a), (x-b)(x-c), a < b < c
local case_3_4;

# products of the form (x-a)(x-b), (x-c)(x-d), a < b < c
local case_3_5;

export cases;

    sqf := proc(poly)
    local L, h, f_u, i;
        L := sqrfree(poly);
        h := 1;
        f_u := L[1];
        for i to numelems(L[2]) do
            if type(L[2][i][2], even) then
                h := h*L[2][i][1]^L[2][i][2];
            else
                h := h*L[2][i][1]^(L[2][i][2] - 1);
                f_u := f_u*L[2][i][1];
            end if;
        end do;
        # f_u is the strictly positive polynomial
        # h is the sums of squares part
        return expand(f_u), h;
    end proc;

    auxiliarSosStep := proc(sos, _basis_element, x)
        if sos = 1 then
            return 1, expand(_basis_element);
        end if;

    local _sos_roots := [solve(sos=0,x)];
    local i, sos_output := 1, basis_element := _basis_element;
    local min_fix := table();
        for i from 1 to nops(_sos_roots) do
            if assigned(min_fix[_sos_roots[i]]) = false then
                min_fix[_sos_roots[i]] := 0;
            end if;
            if subs(x = _sos_roots[i], _basis_element) < 0 and min_fix[_sos_roots[i]] < 2 then
                basis_element := basis_element*(x - _sos_roots[i]);
                min_fix[_sos_roots[i]] := min_fix[_sos_roots[i]] + 1;
            else
                sos_output := sos_output*(x - _sos_roots[i]);
            end if;
        end do;
        return sos_output, expand(basis_element);
    end proc;

    # We implement the vector-like data structure
    # using the `table` data structure
    zeroPO := proc(nat)
    local elem, i;
    local basisPO, _zerosPO, _po, po;
        basisPO := map(
            _index -> expand(mul(elem, elem in map(i -> nat[i], _index))),
            powerset([seq(i, i=1..nops(nat))])
                      );
        _zerosPO := [seq(0, i=1..2^nops(nat))];
        _po := zip(`=`, basisPO, _zerosPO);
        po := table(_po);
        return po;
    end proc;

    unitPO := proc(nat)
    local output := zeroPO(nat);
        output[1] := 1;
        return output;
    end proc;

    updateNatEntry := proc(po, nat_i, new_element)
        po[expand(nat_i)] := new_element;
        return;
    end proc;

    addPO := proc(p1, p2, nat)
    local i;
    local output := zeroPO(nat);
    local _indices := [indices(p1, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := p1[_indices[i]] + p2[_indices[i]];
        end do;
        return output;
    end proc;

    prodPO := proc(p1, p2, nat, x)
    local i, j;
    local output := zeroPO(nat);
    local _indices := [indices(p1, 'nolist')];
    local size := nops(_indices);
    local _sos, _basis;
        for i from 1 to size do
            for j from 1 to size do
                if evalb(_indices[i] = _indices[j]) then
                    output[1] := output[1] + _indices[i]^2*p1[_indices[i]]*p2[_indices[j]];
                else
                    _basis, _sos := sqf(_indices[i]*_indices[j]);
                    _sos, _basis := auxiliarSosStep(_sos, _basis, x);
                    output[_basis] :=
                    output[_basis] + _sos*p1[_indices[i]]*p2[_indices[j]];
                end if;
            end do;
        end do;
        return output;
    end proc;

    semiAlgebraicIntervals := proc(basis, x)
        return map
        (bound -> boundInfo(x, bound, 0),
         SemiAlgebraic(map(g -> g >= 0, basis), [x]));
    end proc;

    ord := proc(f, x, _point)
    local g, T;
        g := subs(x = T + _point, f);
        return ldegree(expand(g), T);
    end proc;

    boundInfo := proc(x, bound, eps)
    local i1, i2, j1, j2;
        # This is a bounded inequality
        if(nops(bound) = 2) then
            i1 := simplify(op(bound[1])[1]);
            i2 := simplify(op(bound[1])[2]);
            j1 := simplify(op(bound[2])[1]);
            j2 := simplify(op(bound[2])[2]);
            if evalb(i1 = x) then
                if evalb(j1 = x) then
                    return [min(i2, j2)+eps, max(i2, j2)-eps];
                else
                    return [min(i2, j1)+eps, max(i2, j1)-eps];
                end if;
            else
                if evalb(j1 = x) then
                    return [min(i1, j2)+eps, max(i1, j2)-eps];
                else
                    return [min(i1, j1)+eps, max(i1, j1)-eps];
                end if;
            end if;
            # This is an equality or unbounded inequality
        else
            i1 := simplify(op(bound[1])[1]);
            j1 := simplify(op(bound[1])[2]);
            if type(bound[1], `=`) then
                if evalb(i1 = x) then
                    return [j1, j1];
                else
                    return [i1, i1];
                end if;
            end if;
            if type(bound[1], `<=`) then
                if evalb(i1 = x) then
                    return [-infinity, j1-eps];
                else
                    return [i1+eps, infinity];
                end if;
            end if;
        end if;
    end proc;

    # Assumption:
    # - SemiAlgebraic(basis) is bounded and non-empty
    # - QM(basis) is saturated
    # Output:
    # A list of list of the form [X, Y] where:
    # - X list with information about the root
    # and its multiplicity of f
    # i.e., [..., [..., [root_{}, multiplicity_{i, j}], ...], ...]
    # where ... < roots_{i-1, n_{i-1}} < roots_{i, 1}
    # < ... < roots_{i, n_i} < roots_{i+1, 1} < ...
    # - Y contains the intervals which contains the roots in X
    decompositionFromBasis := proc(f, intervals, x)
    local f_roots := [RealDomain:-solve(f = 0, x)];
    local sep_roots_ords := [], factorable_sos := 1;
    local first_end_point := intervals[1, 1];
        sep_roots_ords := [
            op(sep_roots_ords),
            [
                # TODO
                # I'm not sure if this should be sorted
                select(_root -> _root <= first_end_point, f_roots),
                [-infinity, first_end_point]
            ]
                          ];
    local i, j, num_intervals := nops(intervals);
        for i from 1 to num_intervals - 1 do
            sep_roots_ords :=
            [op(sep_roots_ords),
             [
                 # TODO
                 # I'm not sure if this should be sorted
                 select
                 (_root ->
                  intervals[i, 2] <= _root and _root <= intervals[i+1,1],
                  f_roots),
                 [intervals[i, 2], intervals[i+1, 1]]
             ]
            ];
        end do;
    local last_end_point := intervals[num_intervals, 2];
        sep_roots_ords := [
            op(sep_roots_ords),
            [
                select(_root ->
                       _root >= last_end_point, f_roots),
                [last_end_point, infinity]
            ]
                          ];
        sep_roots_ords := map(
            l -> [map(_root -> [_root, ord(f, x, _root)], l[1]), l[2]],
            sep_roots_ords
                             );

    local simpl_roots := [];
    local k := 1;
        for i from 1 to nops(sep_roots_ords) do
            simpl_roots := [op(simpl_roots), []];
            for j from 1 to nops(sep_roots_ords[i, 1]) do
                # sep_roots_ords[i, 1, j, 1] <- root info
                # sep_roots_ords[i, 1, j, 2] <- multiplicity info
                factorable_sos :=
                factorable_sos*(x-sep_roots_ords[i, 1, j, 1])^(2*iquo(sep_roots_ords[i, 1, j, 2], 2));
                if modp(sep_roots_ords[i, 1, j, 2], 2) = 1 then
                    simpl_roots[i] := [op(simpl_roots[i]), sep_roots_ords[i, 1, j, 1]];
                end if;
            end do;
            simpl_roots[i] := [simpl_roots[i], sep_roots_ords[i, 2]];
        end do;

        return factorable_sos, simpl_roots;
    end proc;

    # Assumption: QM(basis) is a saturated quadratic module
    checkMembership := proc(f, basis, x)
    local R := PolynomialRing([x]);
        return IsEmpty([op(map(g -> g >= 0, basis)), f < 0], R);
    end proc;

    # Assumption a \leq c_1 \leq c_2 \leq b
    # Output: Computes gamma such that
    # (x-c_1)(x - c_2) - gamma * (x - a)(x - b) is a sums of squares
    lemma_1_5 := proc(c1, c2, a, b)
        if c1 + c2 > a + b then
            return 2/(b-a)*(b - (c1+c2)/2);
        elif c1 + c2 < a + b then
            return 2/(b-a)*((c1+c2)/2 - a);
        else
            return ((c2-c1)/(b-a))^2;
        end if;
    end proc;

    natGens := proc(intervals, x)
    local i;
    local output := [x-intervals[1, 1]];
        for i from 1 to nops(intervals) - 1 do
            output := [op(output), (x - intervals[i, 2])*(x - intervals[i+1, 1])];
        end do;
        output := [op(output), -(x - intervals[nops(intervals), 2])];
        return output;
    end proc;

    checkSosMultipliers := proc(po)
        print(">> Entries of po:");
    local sos_multipliers := [entries(po, 'nolist')];
        map(proc(_p)
                print(SemiAlgebraic([_p < 0], [x]));
            end proc, sos_multipliers);
    end proc;

    checkCorrectness := proc(po, sos_extra, f)
    local basis_element := [indices(po, 'nolist')];
    local sos_multiplier := [entries(po, 'nolist')];
    local i, output := 0;
        for i from 1 to nops(basis_element) do
            output := output + sos_multiplier[i]*basis_element[i];
        end do;

        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Original polynomial: ", expand(f)));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Result: ", expand(sos_extra*output)));

        return expand(sos_extra*output - f);
    end proc;

    # Assumption: SemiAlgebraic(basis) is bounded and non-empty
    inductiveCert := proc(f, basis, x)
        if checkMembership(f, basis, x) = false then
            return false;
        end if;

    local intervals := semiAlgebraicIntervals(basis, x);
    local nat := natGens(intervals, x);
    local output := unitPO(nat), _temp;
    local todo;

    local factorable_sos, simpl_roots;
        factorable_sos, simpl_roots := decompositionFromBasis(f, intervals, x);

    local i, j, k, size := nops(simpl_roots);
    local a, b, c1, c2, _gamma;

        # Update output using left factors
        a := simpl_roots[1, 2, 2];
        for i from 1 to nops(simpl_roots[1, 1]) do
            c1 := simpl_roots[1, 1, i];
            _temp := zeroPO(nat);
            updateNatEntry(_temp, 1, a - c1);
            updateNatEntry(_temp, x - a, 1);
            output := prodPO(output, _temp, nat, x)
        end do;

        # Update output using in between factors
        for i from 2 to size - 1 do
            j := 1;
            todo := simpl_roots[i, 1];
            k := nops(todo);
            a := simpl_roots[i, 2, 1];
            b := simpl_roots[i, 2, 2];
            while j <= k do
                c1 := todo[j];
                c2 := todo[k];
                _gamma := lemma_1_5(c1, c2, a, b);
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(SemiAlgebraic([(x-c1)*(x-c2)-_gamma*(x-a)*(x-b) < 0], [x])));

                _temp := zeroPO(nat);
                updateNatEntry(_temp, 1, (x-c1)*(x-c2) - _gamma*(x-a)*(x-b));
                updateNatEntry(_temp, (x-a)*(x-b), _gamma);
                output := prodPO(output, _temp, nat, x);

                j := j + 1;
                k := k - 1;
            end do;
        end do;

        # Update output using right factors
        b := simpl_roots[size, 2, 1];
        for i from 1 to nops(simpl_roots[size, 1]) do
            c2 := simpl_roots[size, 1, i];
            _temp := zeroPO(nat);
            updateNatEntry(_temp, 1, c2 - b);
            updateNatEntry(_temp, -(x - b), 1);
            output := prodPO(output, _temp, nat, x)
        end do;

        #
        # Verify output
        #
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, checkSosMultipliers(output));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Check correctness (difference should be zero):", checkCorrectness(output, factorable_sos, f)));

        return factorable_sos, output;
    end proc;

    case_3_1 := proc(a, b, nat, x)
    local output := zeroPO(nat);
        if a = b then
            updateNatEntry(output, x - a, (x-a-1)^2/4);
            updateNatEntry(output, -(x - a), (x-a+1)^2/4);
        elif a < b then
            updateNatEntry(output, x - a, (x-b)^2/(b-a));
            updateNatEntry(output, -(x - b), (x-a)^2);
        else
            return case_3_1(b, a);
        end if;
        return output;
    end proc;

    case_3_2 := proc(a, b, nat, x)
    local output := zeroPO(nat);
        updateNatEntry(output, (x-a), (x-b)^2);
        updateNatEntry(output, (x-b), (b-a)*(x-a));
        return output;
    end proc;

    case_3_3 := proc(a, b, c, nat, x)
    local output := zeroPO(nat);
    local alpha := (b-a)/(c-b);
        updateNatEntry(output, (x-a)*(x-b), alpha/(alpha+1)*(x-c)^2);
        updateNatEntry(output, (x-b)*(x-b), 1/(alpha+1)*(x-a)^2);
        return output;
    end proc;

    # Assume 0 < a < b, 0 < a < c
    lemma_3_1 := proc(a, b, c, x)
        #print(">> Check 1", evalb(0 < a));
        #print(">> Check 2", evalb(a < b));
        #print(">> Check 3", evalb(a < c));
    local p := (x-a)*(x+a)*(x-c)*(x-(a+c)/2)^(2*n);
    local pDeriv := 2*n*(x + a)*(x - a)*(x - c)
        + (x - (a + c)/2)*((x + a)*(x - a) + (x + a)*(x - c) + (x - a)*(x - c));
    local n_curr := 0;
    local min_a_c, sols;

        while true do
            sols := [RealDomain:-solve(subs({n = n_curr}, pDeriv)=0,x)];
            min_a_c := min(map(x_arg -> subs({n=n_curr,x=evalf(x_arg)}, p), sols));
            min_b := subs({n=n_curr,x=-b}, p);
            if min_b < min_a_c then
                break;
            end if;
            n_curr := n_curr + 1;
        end do;

    local alpha := 1/((b+(a+c)/2)^(2*n_curr)*(b-a)*(b+a)*(b+c));
    local s1 := alpha*(x-(a+c)/2)^(2*n_curr);
    local s0 := (x+b)*(1+s1*(x+a)*(x-a)*(x-c));

        return s0, s1;
    end proc;

    lemma_3_2 := proc(a, b, d, x)
    local alpha;
        if d = -a then
            alpha := d^2 - b^2;
            return 1/alpha*(x-b)^2*(x+b)^2, 1/alpha;
        else
            # WORK
            return 1, 1;
        end if;
    end proc;

    # TODO
    case_3_4 := proc(a, b, c, d, nat, x)
        # Assume b = -c, otherwise
        # x \mapsto x + (b+c)/2;
    local _a := a - (b+c)/2, _b := b - (b+c)/2;
    local _c := c - (b+c)/2, _d := d - (b+c)/2;

        # Compute certificates of g1 in QM(g1 g2 g3)
    local g1_s0, g1_s1;
        g1_s0, g1_s1 := lemma_3_1(_c, -_a, _d, x);

        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of Lemma 3.1 in construction", SemiAlgebraic([g1_s0 < 0], [x])));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of Lemma 3.1 in construction", SemiAlgebraic([g1_s1 < 0], [x])));

        # Compute certificates of g2 in QM(g1 g2 g3)
    local g2_s0, g2_s1;
        g2_s0, g2_s1 := lemma_3_2(_c, -_a, _d, x);

    local output := zeroPO(nat);
        #x := x - (b+c)/2;
        #updateNatEntry(output, nat_gen, sos_multiplier);
        return g1_s0, g1_s1;
    end proc;

    # TODO
    case_3_5 := proc(a, b, c, nat, x)
        return;
    end proc;

    # Assume 0 < a < b, 0 < a < c < d
    cases := proc(a, b, c, d, nat, x)
    local ok1, ok2;
        ok1, ok2 := case_3_4(a, b, c, d, nat, x);
        return ok1, ok2;
    end proc;
end module;
