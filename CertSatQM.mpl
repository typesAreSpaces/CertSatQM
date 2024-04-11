$define ENABLE_DEBUGGING    false
$define ENABLE_VERIFICATION false
$define LOG_TIME

$define DEBUG_EXIT lprint(">> Debugging, getting out"); return 0
$define DEBUG(F, L, y, x) if (y) then lprint(">> Debugging file ", F, " at line ", L); x; end if

$define START_LOG_TIME(X, S) stack_level:=stack_level+1;fd := FileTools:-Text:-Open("log_time.txt", append);local _log_time_S := time();FileTools:-Text:-WriteString(fd, cat("Start: ", X, " ", convert(stack_level, string), "\n"));FileTools:-Text:-Close(fd);
$define END_LOG_TIME(X, S) fd := FileTools:-Text:-Open("log_time.txt", append);FileTools:-Text:-WriteString(fd, cat("End: ", X, " ", convert(stack_level, string), "\nTime: ", convert(time() - _log_time_S, string), "\n"));FileTools:-Text:-Close(fd);stack_level:=stack_level-1;
$define INIT_START_LOG_TIME(X, S) local fd;START_LOG_TIME(X, S)

#StrictlyPositiveCert:-spCertificates := proc(f, basis, x)
$define spCert StrictlyPositiveCert:-spCertificates
#BasicLemma:-lift := proc(f, g, basis, x)
$define basiclemma BasicLemma:-lift
$define _isolate RootFinding:-Isolate

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

#read "multivsos/multivsos.mm";

#currentdir(_pwd);

CertSatQM := module() option package;

$ifdef LOG_TIME
local stack_level := -1;
$endif

local computeMin;
local sqf, bound_info;

# Compute minimum of polynomial poly
# over semialgebraic set S
# S is a finite list of intervals
# poly is a polynomial
    computeMin := proc(S, poly, x)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("computeMin",0)
$endif
        if evalb(S = []) then
$ifdef LOG_TIME
            END_LOG_TIME("computeMin",0)
$endif
            return 0, infinity;
        end if;
    local roots_poly := map(sol -> op(sol)[2], _isolate(diff(poly, x)));
    local num_roots := nops(roots_poly);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> poly", poly));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> roots_poly", roots_poly));
    local curr_point;
    local curr_min := infinity, arg_min;
    local i, j := 1;
    local interval;
        for i from 1 to nops(S) do
            interval := bound_info(x, S[i], 0);
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Current interval", interval));

            curr_point := subs(x=interval[1], poly);
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_point", curr_point));
            if evalf(curr_point <= curr_min) then
                curr_min := curr_point;
                arg_min := interval[1];
            end if;
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_min", curr_min));

            curr_point := subs(x=interval[2], poly);
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_point", curr_point));
            if evalf(curr_point <= curr_min) then
                curr_min := curr_point;
                arg_min := interval[2];
            end if;
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> curr_min", curr_min));

            while j <= num_roots and evalf(roots_poly[j] < interval[1]) do
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> j @1", j));
                j := j + 1;
            end do;

            while j <= num_roots and evalf(roots_poly[j] < interval[2]) do
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> j @2", j));
                curr_point := subs(x=roots_poly[j], poly);
                if evalf(curr_point <= curr_min) then
                    curr_min := curr_point;
                    arg_min := roots_poly[j];
                end if;
                j := j + 1;
            end do;
        end do;
$ifdef LOG_TIME
        END_LOG_TIME("computeMin",0)
$endif
        return arg_min, curr_min;
    end proc;

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

    bound_info := proc(x, bound, eps)
$ifdef LOG_TIME
        INIT_START_LOG_TIME("bound_info",0)
$endif
    local i1, i2, j1, j2;
        # This is a bounded bounduality
        if(nops(bound) = 2) then
            i1 := simplify(op(bound[1])[1]);
            i2 := simplify(op(bound[1])[2]);
            j1 := simplify(op(bound[2])[1]);
            j2 := simplify(op(bound[2])[2]);
            if evalb(i1 = x) then
                if evalb(j1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i2, j2)+eps, max(i2, j2)-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i2, j1)+eps, max(i2, j1)-eps];
                end if;
            else
                if evalb(j1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i1, j2)+eps, max(i1, j2)-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [min(i1, j1)+eps, max(i1, j1)-eps];
                end if;
            end if;
            # This is an equality or unbounded bounduality
        else
            i1 := simplify(op(bound[1])[1]);
            j1 := simplify(op(bound[1])[2]);
            if type(bound[1], `=`) then
                if evalb(i1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [j1, j1];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [i1, i1];
                end if;
            end if;
            if type(bound[1], `<=`) then
                if evalb(i1 = x) then
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [-infinity, j1-eps];
                else
$ifdef LOG_TIME
                    END_LOG_TIME("bound_info",0)
$endif
                    return [i1+eps, infinity];
                end if;
            end if;
        end if;
    end proc;

# ---------------------------------------------------
#) Algorithms from Section 3

local auxiliarSosStep;

export zeroPO, unitPO, updatePONatEntry;
export addPO, prodPO,  scalarProdPO;

export semiAlgebraicIntervals;
local ord, epsSign;
local decompositionFromBasis;

local checkMembership;
local lemma_1_5;
export natGens;

local checkSosMultipliers;
local checkCorrectnessPO;

export certInPO;

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

local lemma_3_4_compute_A;
local lemma_3_4;
# products of the form (x-a)(x-b), (x-c)(x-d), a < b < c
local case_3_5;

local cases;

export zeroQM, unitQM, updateQMNatEntry;
export addQM, prodQM, negQM, scalarProdQM;

export fromQMtoPoly, showQM;
local  splitPO2QM;
export certInQM, checkCorrectnessQM;
# ---------------------------------------------------

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
    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
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

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    unitPO := proc(nat)
    local output := zeroPO(nat);
        output[1] := 1;
        return output;
    end proc;

    updatePONatEntry := proc(po, nat_i, new_element)
        po[expand(nat_i)] := new_element;
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

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    scalarProdPO := proc(p, sos, nat, x)
    local i;
    local output := zeroPO(nat);
    local _indices := [indices(p1, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := sos*p[_indices[i]];
        end do;
        return output;
    end proc;

    semiAlgebraicIntervals := proc(basis, x)
        return map
        (bound -> bound_info(x, bound, 0),
         SemiAlgebraic(map(g -> g >= 0, basis), [x]));
    end proc;

    ord := proc(f, x, _point)
    local g, T;
        g := subs(x = T + _point, f);
        return ldegree(expand(g), T);
    end proc;

    epsSign := proc(f, t, point)
    local g, T;
        g := subs(t = T + point, f);
        return tcoeff(expand(g), T);
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
                # DEBUG
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
                 # DEBUG
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

    checkCorrectnessPO := proc(po, sos_extra, f)
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
    certInPO := proc(f, basis, x)
        if checkMembership(f, basis, x) = false then
            return 0, 0;
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
            updatePONatEntry(_temp,     1, a - c1);
            updatePONatEntry(_temp, x - a,      1);
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
                DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, lprint(SemiAlgebraic([(x-c1)*(x-c2)-_gamma*(x-a)*(x-b) < 0], [x])));

                _temp := zeroPO(nat);
                updatePONatEntry(_temp,           1, (x-c1)*(x-c2) - _gamma*(x-a)*(x-b));
                updatePONatEntry(_temp, (x-a)*(x-b),                             _gamma);
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
            updatePONatEntry(_temp,        1, c2 - b);
            updatePONatEntry(_temp, -(x - b),      1);
            output := prodPO(output, _temp, nat, x)
        end do;

        #
        # Verify output
        #
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(output));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, checkSosMultipliers(output));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Check correctness (difference should be zero):", checkCorrectnessPO(output, factorable_sos, f)));

        return factorable_sos, output;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    case_3_1 := proc(a, b, nat, x)
    local output := zeroQM(nat);
        if a = b then
            updatePONatEntry(output,    x - a, (x-a-1)^2/4);
            updatePONatEntry(output, -(x - a), (x-a+1)^2/4);
        elif a < b then
            updatePONatEntry(output,    x - a, (x-b)^2/(b-a));
            updatePONatEntry(output, -(x - b), (x-a)^2/(b-a));
        else
            return case_3_1(b, a);
        end if;
        return output;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    # Assume a < b
    case_3_2 := proc(a, b, nat, x)
    local output := zeroQM(nat);
        updatePONatEntry(output,       (x-a), (x-b)^2);
        updatePONatEntry(output, (x-a)*(x-b),   (b-a));
        return output;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    # Assume a < b < c
    case_3_3 := proc(a, b, c, nat, x)
    local output := zeroQM(nat);
    local alpha := (b-a)/(c-b);
        updatePONatEntry(output, (x-a)*(x-b), alpha/(alpha+1)*(x-c)^2);
        updatePONatEntry(output, (x-b)*(x-c),     1/(alpha+1)*(x-a)^2);
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
    local min_b, min_a_c, sols;

        while true do
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> n_curr", n_curr));
            sols := [RealDomain:-solve(subs({n=n_curr}, pDeriv)=0,x)];
            min_a_c := min(map(x_arg -> subs({n=n_curr,x=evalf(x_arg)}, p), sols));
            min_b := subs({n=n_curr,x=-b}, p);
            if min_b <= min_a_c then
                break;
            end if;
            n_curr := n_curr + 1;
        end do;

    local alpha := 1/((b+(a+c)/2)^(2*n_curr)*(b-a)*(b+a)*(b+c));
    local s1 := alpha*(x-(a+c)/2)^(2*n_curr);
    local s0 := (x+b)*(1+s1*(x+a)*(x-a)*(x-c));

        return s0, s1;
    end proc;

    # Assume 0 < a < b, 0 < a < c
    lemma_3_2 := proc(a, b, c, x)
    local alpha, beta, s0, s1;
        if c = b then
            alpha := c^2 - a^2;
            return 1/alpha*(x-a)^2*(x+a)^2, 1/alpha;
        else
            beta := (a^2 - b*c - sqrt((b^2 - a^2)*(c^2 - a^2)))/(b - c);
            alpha := (a + beta)^2*(b - a)*(a+c);
            s1 := 1/alpha*(x - beta)^2;
            s0 := (x+a)*(x-a)*(1 + s1*(x+b)*(x-c));
            #print(">> sign @-a", convert(subs(x=-a, s1*(x+b)*(x-c)), float));
            #print(">> sign @a", convert(subs(x=a, s1*(x+b)*(x-c)), float));
            return s0, s1;
        end if;
    end proc;

    # Computes certificates of (x-a) * (x-b)(x-c)
    # Assume a < b < c
    # Assume a is the left most endpoint of the semialgebraic set
    # Assume b = -c, otherwise
    # x \mapsto x + (b+c)/2;
    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    case_3_4 := proc(a, b, c, d, nat, x)
    local _a := a - (b+c)/2, _b := b - (b+c)/2;
    local _c := c - (b+c)/2, _d := d - (b+c)/2;

        # 1. Compute certificates of g1 in QM(g1 g2 g3)
    local g1__1, g1__g1g2g3;
        g1__1, g1__g1g2g3 := lemma_3_1(_c, -_a, _d, x);

        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, print(">> Verification of Lemma 3.1 in construction", SemiAlgebraic([g1__1 < 0], [x])));
        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, print(">> Verification of Lemma 3.1 in construction", SemiAlgebraic([g1__g1g2g3 < 0], [x])));
        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, print(">> Verification of g1 in QM(g1 g2 g3)", expand((x-_a)-(g1__1 + g1__g1g2g3*(x-_a)*(x-_b)*(x-_c)*(-(x-_d))))));

        # 2. Compute certificates of g2 in QM(g1 g2 g3)
    local g2__1, g2__g1g2g3;
        g2__1, g2__g1g2g3 := lemma_3_2(_c, -_a, _d, x);
        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, lprint(">> Verification of Lemma 3.2 in construction", SemiAlgebraic([g2__1 < 0], [x])));
        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, lprint(">> Verification of Lemma 3.2 in construction", SemiAlgebraic([g2__g1g2g3 < 0], [x])));
        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, print(">> Verification of g2 in QM(g1 g2 g3)", expand((x-_b)*(x+_b)-(g2__1 + g2__g1g2g3*(x-_a)*(x-_b)*(x-_c)*(-(x-_d))))));

    local g1g2__1 := g1__1*g2__1 + g1__g1g2g3*g2__g1g2g3*((x-_a)*(x-_b)*(x-_c)*(-(x-_d)))^2;
    local g1g2__g1g2g3 := g1__1*g2__g1g2g3 + g1__g1g2g3*g2__1;

        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, print(">> Verification of g1 g2 in QM(g1 g2 g3)", expand((x-_a)*(x-_b)*(x-_c)-(g1g2__1 + g1g2__g1g2g3*(x-_a)*(x-_b)*(x-_c)*(-(x-_d))))));

    local g1g2g3__g1g3 := g2__1;
    local g1g2g3__g2 := g2__g1g2g3*((x-_a)*(x-_d))^2;

        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, print(">> Verification of g1 g2 g3 in QM(g1, g2, g3)", expand((x-_a)*(x-_b)*(x-_c)*(-(x-_d))-(g1g2g3__g1g3*((x-_a)*(-(x-_d))) + g1g2g3__g2*(x-_b)*(x-_c)))));

    local cert_g1g3 := case_3_1(_a, _d, map(poly -> subs(x=x+(b+c)/2, poly), nat), x);

    local sos_1 := g1g2__1;
    local sos_g1 := g1g2__g1g2g3*g1g2g3__g1g3*cert_g1g3[(x-_a)];
    local sos_g2 := g1g2__g1g2g3*g1g2g3__g2;
    local sos_g3 := g1g2__g1g2g3*g1g2g3__g1g3*cert_g1g3[-(x-_d)];

        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, print(">> Verification of g1 g2 in QM(g1, g2, g3)", expand((x-_a)*(x-_b)*(x-_c) - (sos_1 + sos_g1*(x-_a) + sos_g2*(x-_b)*(x-_c) + sos_g3*(-(x-_d))))));

    local output := zeroQM(nat);
        #updateQMNatEntry(output, nat_gen, sos_multiplier);
        updateQMNatEntry(output,           1, subs(x=x-(b+c)/2, sos_1));
        updateQMNatEntry(output,       (x-a), subs(x=x-(b+c)/2, sos_g1));
        updateQMNatEntry(output, (x-b)*(x-c), subs(x=x-(b+c)/2, sos_g2));
        updateQMNatEntry(output,      -(x-d), subs(x=x-(b+c)/2, sos_g3));

        DEBUG(__FILE__, __LINE__, ENABLE_VERIFICATION, print(">> Verification of g1 g2 in QM(g1, g2, g3)", expand((x-a)*(x-b)*(x-c) - (output[1] + output[x-a]*(x-a) + output[expand((x-b)*(x-c))]*(x-b)*(x-c) + output[-(x-d)]*(-(x-d))))));
        return output;
    end proc;

    # Returns solution for parameter A in (x-A)^2 g1 g3 g4
    lemma_3_4_compute_A := proc(a, b, c, d, e, x)
        # The following returns 1 if g1 g3 g4|_{x = -b} = g1 g3 g4|_{x = -c}
    local gamma0 := (a-b)*(b+c)*(b+d)*(b+e);
    local gamma1 := 2*(a-c)*c*(c+d)*(c+e);
        if gamma0 = gamma1 then
            return 1;
        end if;

    local _a := (gamma0 - gamma1);
    local _b := 2*(gamma0*b - gamma1*c);
    local _c := (gamma0*b^2 - gamma1*c^2);
    local A := (-_b - sqrt(_b^2 - 4*_a*_c))/(2*_a);
        return (x-A)^2;
    end proc;

    # Assume 0 < c < b < a
    # Assume 0 < c < d < e
    lemma_3_4 := proc(a, b, c, d, e, x)
    local g1 := (x+a), g2 := (x+b)*(x+c), g3 := (x-c)*(x-d), g4 := -(x-e);
    local _alpha, _beta;
        # Case 1: e + (b+c)/2 = a - (b+c)/2
        if e + b + c = a then
            _alpha := -a;
            _beta := e;
        end if;
        # Case 2: e + (b+c)/2 > a - (b+c)/2
        if e + b + c > a then
            _alpha := -(e + b + c);
            _beta := e;
        end if;
        # Case 3: e + (b+c)/2 < a - (b+c)/2
        if e + b + c < a then
            _alpha := -a;
            _beta := a - b - c;
        end if;

    local s_A := lemma_3_4_compute_A(a, b, c, d, e, x);

    local s := (x - _alpha)^(2*n)*(x - _beta)^(2*n);
    local p := -s_A*s*g1*g3*g4;
    local pDeriv:= -2*n*((x - _beta) + (x - _alpha))*g1*g3*g4
        - (x-_alpha)*(x-_beta)*(g3*g4 + g1*(x-d)*g4 + g1*(x-c)*g4 - g1*g3);
        if not(s_A = 1) then
            pDeriv:= diff(s_A, x)/2*pDeriv - 2*(x-_alpha)*(x-_beta)*g1*g3*g4;
        end if;

    local n_curr := 0, min_b_c, min_outside;
    local sols;
        while true do
            sols := select(point -> evalf(point) < -b or evalf(point) > -c,
                           [RealDomain:-solve(subs({n=n_curr}, pDeriv)=0,x)]);
            min_outside :=
            min(
                map(x_arg ->
                    #evalf(subs({n=n_curr, x=x_arg}, p)),
                    evala(subs({n=n_curr, x=x_arg}, p)),
                    sols)
               );
            min_b_c := subs({n=n_curr, x=-b}, p);
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> n_curr", n_curr));
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> min_outside", min_outside));
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> min_b_c", evalf(min_b_c)));
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> p", subs({n=n_curr}, p)));
            DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> pDeriv", subs({n=n_curr}, pDeriv)));
            #if evalf(min_b_c) < evalf(min_outside) then
            if is(min_b_c < simplify(min_outside)) then
                break;
            end if;
            n_curr := n_curr + 1;
        end do;

        s := subs(n=n_curr, s);
    local alpha := -1/(subs({n=n_curr, x=-b}, p));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> alpha", evalf(alpha)));
    local s1 := alpha*s_A*s;
    local s0 := g2*(1- s1*g1*g3*g4);

        return s0, s1;
    end proc;

    # Computes certificates of (x-a)(x-b) * (x-c)(x-d)
    # Assume e < a < b < c < d < f
    # Assume a, b, c, d are endpoints 'in-between' the semialgebraic set
    # Assume b = -c, otherwise
    # x \mapsto x + (b+c)/2;
    # Assume g1 = (x+a), g2 = (x+b)(x+c), g3 = (x-c)(x-d), g4 = -(x-e)
    # i.e., g1 = (x+_e), g2 = (x+_a)(x+_c), g3 = (x-_c)(x-_d), g4 = -(x-_f)
    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    case_3_5 := proc(a, b, c, d, e, f, nat, x)
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> e", e));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> a", a));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> b", b));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> c", c));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> d", d));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> f", f));
    local _a := a - (b+c)/2, _b := b - (b+c)/2;
    local _c := c - (b+c)/2, _d := d - (b+c)/2;
    local _e := e - (b+c)/2, _f := f - (b+c)/2;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> _e", _e));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> _a", _a));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> _b", _b));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> _c", _c));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> _d", _d));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> _f", _f));

        # 1. Find certificate of g2 in QM(g1 g2 g3 g4)
    local s0_g2_in_g1g2g3g4, s1_g2_in_g1g2g3g4;
        s0_g2_in_g1g2g3g4, s1_g2_in_g1g2g3g4 := lemma_3_4(-_e, -_a, _c, _d, _f, x);

        # 2. Find certificate of g2 g3 in QM(g3, g1 g2 g4)
    local s0_g2g3_in_g1g2g4:= s0_g2_in_g1g2g3g4;
    local s1_g2g3_in_g1g2g4:= ((x-_c)*(x-_d))^2*s1_g2_in_g1g2g3g4;

        # 3. Find certificate of g1 g2 g4 in QM(g1, g2, g4)
    local shifted_basis1 := map(poly -> subs(x=x+(b+c)/2, poly), nat);

    local cert_g1g4 := case_3_1(_e, _f, shifted_basis1, x);
        #print(">> cert_g1g4", cert_g1g4);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> check cert_g1g4", fromQMtoPoly(cert_g1g4)));
    local s0_2_ := cert_g1g4[1];
    local s1_2_ := cert_g1g4[x-_e];
    local s2_2_ := cert_g1g4[-x+_f];

    local cert_g1g2 := case_3_4(_e, _a, _b, _f, shifted_basis1, x);
        #print(">> cert_g1g2", cert_g1g2);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> check cert_g1g2", fromQMtoPoly(cert_g1g2)));
    local s0_3_ := cert_g1g2[1];
    local s1_3_ := cert_g1g2[x-_e];
    local s2_3_ := cert_g1g2[expand((x-_a)*(x-_b))];
    local s3_3_ := cert_g1g2[-x+_f];

    local shifted_basis2 := map(poly -> subs(x=-x+(b+c)/2, poly), nat);

    local cert_g2g4 := negQM(case_3_4(-_f, -_b, -_a, -_e, shifted_basis2, x), shifted_basis2, x);
        #print(">> cert_g2g4", cert_g2g4);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> check cert_g2g4", fromQMtoPoly(cert_g2g4)));
    local s0_4_ := cert_g2g4[1];
    local s1_4_ := cert_g2g4[x-_e];
    local s2_4_ := cert_g2g4[expand((x-_a)*(x-_b))];
    local s3_4_ := cert_g2g4[-x+_f];

    local s0_1 := s1_g2g3_in_g1g2g4*(        s1_2_*s0_3_ + s2_2_*s0_4_);
    local s1_1 := s1_g2g3_in_g1g2g4*(        s1_2_*s1_3_ + s2_2_*s1_4_);
    local s2_1 := s1_g2g3_in_g1g2g4*(s0_2_ + s1_2_*s2_3_ + s2_2_*s2_4_);
    local s4_1 := s1_g2g3_in_g1g2g4*(        s1_2_*s3_3_ + s2_2_*s3_4_);

        # 4. Translate back to original coordinates using data structure for QMs
    local output := zeroQM(nat);
        updateQMNatEntry(output,           1, subs(x=x-(b+c)/2, s0_1));
        updateQMNatEntry(output,         x-e, subs(x=x-(b+c)/2, s1_1));
        updateQMNatEntry(output, (x-a)*(x-b), subs(x=x-(b+c)/2, s2_1));
        updateQMNatEntry(output, (x-c)*(x-d), subs(x=x-(b+c)/2, s0_g2g3_in_g1g2g4));
        updateQMNatEntry(output,      -(x-f), subs(x=x-(b+c)/2, s4_1));
        return output;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    # p, q \in nat
    # Output:
    # QMtable of p*q
    cases := proc(p, q, a_0, b_k, nat, x)
    local output := zeroQM(nat);
    local roots_p := sort([solve(p=0,x)]);
    local roots_q := sort([solve(q=0,x)]);
    local num_roots_p := nops(roots_p);
    local num_roots_q := nops(roots_q);
    local shifted_basis;
        # DEBUG
        #print(">> p", p);
        #print(">> q", q);
        #print(">> roots p", roots_p);
        #print(">> roots q", roots_q);

        # Case product of the form (x-a) * -(x-b)
        if num_roots_p = 1 and num_roots_q = 1 then
            # Case (x-a) * (x-a)
            if lcoeff(p) = lcoeff(q) then
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 1"));
                updateQMNatEntry(output, 1, p^2);
                return output;
                # Case (x-a) * -(x-b), a <= b
            else
                #print(">> case_3_1 1");
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 2"));
                return case_3_1(roots_p[1], roots_q[1], nat, x);
            end if;
        end if;

        # Case product of the form (+/-)(x-a) * (x-b)(x-c), a <= b < c
        if num_roots_p = 1 and num_roots_q = 2 then
            # Case product of the form (x-a) * (x-b)(x-c)
            if roots_p[1] <= roots_q[1] then
                # Case product of the form (+/-)(x-a) * (x-a)(x-c)
                if subs(x=roots_p[1], q) = 0 then
                    #print(">> case_3_2 2");
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 3"));
                    return case_3_2(roots_q[1], roots_q[2], nat, x);
                    # Case product of the form (+/-)(x-a) * (x-b)(x-c), a < b
                else
                    #print(">> case_3_4 2");
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 4"));
                    return case_3_4(roots_p[1], roots_q[1], roots_q[2], b_k, nat, x);
                end if
            end if;

            # Case product of the form -(x-a) * (x-b)(x-c), b < c <= a
            if roots_q[2] <= roots_p[1] then
                shifted_basis := map(poly -> subs(x=-x, poly), nat);
                # Case product of the form -(x-c) * (x-b)(x-c), b < c
                if subs(x=roots_p[1], q) = 0 then
                    #print(">> case_3_2 2");
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 5"));
                    return negQM(
                        case_3_2(-roots_q[2], -roots_q[1], shifted_basis, x),
                        shifted_basis, x);
                    # Case product of the form -(x-a) * (x-b)(x-c), b < c < a
                else
                    #print(">> case_3_4 2");
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 6"));
                    return negQM(
                        case_3_4(-roots_p[1], -roots_q[2], -roots_q[1], -a_0, shifted_basis, x),
                        shifted_basis, x);
                end if
            end if;
        end if;

        # Case product of the form (x-a)(x-b) * (+/-)(x-c)
        if num_roots_p = 2 and num_roots_q = 1 then
            # Case product of the form (x-a) * (x-b)(x-c)
            if roots_q[1] <= roots_p[1] then
                # Case product of the form (+/-)(x-a) * (x-a)(x-c)
                if subs(x=roots_q[1], p) = 0 then
                    #print(">> case_3_2 2");
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 7"));
                    return case_3_2(roots_p[1], roots_p[2], nat, x);
                    # Case product of the form (+/-)(x-a) * (x-b)(x-c), a < b
                else
                    #print(">> case_3_4 2");
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 8"));
                    return case_3_4(roots_q[1], roots_p[1], roots_p[2], b_k, nat, x);
                end if
            end if;

            # Case product of the form -(x-a) * (x-b)(x-c), b < c <= a
            if roots_p[2] <= roots_q[1] then
                shifted_basis := map(poly -> subs(x=-x, poly), nat);
                # Case product of the form -(x-c) * (x-b)(x-c), b < c
                if subs(x=roots_q[1], p) = 0 then
                    #print(">> case_3_2 2");
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 9"));
                    return negQM(
                        case_3_2(-roots_p[2], -roots_p[1], shifted_basis, x),
                        shifted_basis, x);
                    # Case product of the form -(x-a) * (x-b)(x-c), b < c < a
                else
                    #print(">> case_3_4 2");
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 10"));
                    return negQM(
                        case_3_4(-roots_q[1], -roots_p[2], -roots_p[1], -a_0, shifted_basis, x),
                        shifted_basis, x);
                end if
            end if;
        end if;

        # Case product of the form (x-a)(x-b) * (x-c)(x-d), b = c or b \neq c
        if num_roots_p = 2 and num_roots_q = 2 then
            # Case product of the form (x-a)(x-b) * (x-b)(x-c), a < b < c
            if subs(x=roots_p[2], q) = 0 then
                #print(">> case_3_3 4 1");
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 11"));
                return case_3_3(roots_p[1], roots_p[2], roots_q[2], nat, x);
            end if;
            # Case product of the form (x-c)(x-d) * (x-b)(x-c), b < c < d
            if subs(x=roots_q[2], p) = 0 then
                #print(">> case_3_3 4 2");
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 12"));
                return case_3_3(roots_q[1], roots_q[2], roots_p[2], nat, x);
            end if;
            # Case product of the form (x-a)(x-b) * (x-c)(x-d), a < b < c < d
            if evalb(roots_p[2] < roots_q[1]) then
                #print(">> case_3_5 4 1");
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 13"));
                return case_3_5(roots_p[1], roots_p[2], roots_q[1], roots_q[2], a_0, b_k, nat, x)
                # Case product of the form (x-a)(x-b) * (x-c)(x-d), c < d < a < b
            else
                #print(">> case_3_5 4 2");
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Case 14"));
                return case_3_5(roots_q[1], roots_q[2], roots_p[1], roots_p[2], a_0, b_k, nat, x)
            end if;
        end if;

        return false, false;
    end proc;

    # We implement the vector-like data structure
    # using the `table` data structure
    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    zeroQM := proc(nat)
    local elem, i;
    local basisQM, _zerosQM, _qm, qm;
        basisQM := [1, op(map(expand, nat))];
        _zerosQM := [seq(0, i=0..nops(nat))];
        _qm := zip(`=`, basisQM, _zerosQM);
        qm := table(_qm);
        return qm;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    unitQM := proc(nat)
    local output := zeroQM(nat);
        output[1] := 1;
        return output;
    end proc;

    updateQMNatEntry := proc(qm, nat_i, new_element)
        qm[expand(nat_i)] := new_element;
        return;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    addQM := proc(q1, q2, nat)
    local i;
    local output := zeroQM(nat);
    local _indices := [indices(q1, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := q1[_indices[i]] + q2[_indices[i]];
        end do;
        return output;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    # Input:
    # q1, q2 \in QMtable
    # Output:
    # QMtable of p*q
    prodQM := proc(q1, q2, a_0, b_k, nat, x)
    local i, j;
    local output := zeroQM(nat), _temp, todo;
    local _indices := [indices(q1, 'nolist')];
    local size := nops(_indices);
    local _basis, basis_element;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> @prodQM fromQMtoPoly q1", fromQMtoPoly(q1)));
        #showQM(q1);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> @prodQM fromQMtoPoly q2", fromQMtoPoly(q2)));
        #showQM(q2);
        for i from 1 to size do
            if q1[_indices[i]] = 0 then
                next;
            end if;
            for j from 1 to size do
                if q2[_indices[j]] = 0 then
                    next;
                end if;
                if evalb(_indices[i] = _indices[j]) then
                    # DEBUG
                    #print(">> i", i);
                    #print(">> indices[i]", _indices[i]);
                    #lprint(">> q1[indices[i]]", q1[_indices[i]]);
                    #lprint(">> q2[indices[j]]", q2[_indices[j]]);
                    output[1] := output[1] + _indices[i]^2*q1[_indices[i]]*q2[_indices[j]];
                else
                    if _indices[i] = 1 then
                        #output[_indices[j]] := q2[_indices[j]];
                        output[_indices[j]] := q1[_indices[i]]*q2[_indices[j]];
                    elif _indices[j] = 1 then
                        #output[_indices[i]] := q1[_indices[i]];
                        output[_indices[i]] := q1[_indices[i]]*q2[_indices[j]];
                    else
                        # DEBUG
                        #print(">> i", i);
                        #print(">> j", j);
                        #print(">> indices[i]", _indices[i]);
                        #print(">> indices[j]", _indices[j]);
                        #lprint(">> q1[indices[i]]", q1[_indices[i]]);
                        #lprint(">> q2[indices[j]]", q2[_indices[j]]);
                        _temp := cases(_indices[i], _indices[j], a_0, b_k, nat, x);
                        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> fromQMtoPoly _temp", fromQMtoPoly(_temp)));
                        #print(">> _temp @ prodQM", _temp);
                        #print(">> _temp@prodQM", _temp);
                        # Update
                        todo := [indices(_temp, 'nolist')];
                        #print(">> todo@prodQM", todo);
                        for basis_element in todo do
                            #print(">> basis_element", basis_element);
                            #print(">> _temp[basis_element]", _temp[basis_element]);
                            _temp[basis_element] := q1[_indices[i]]*q2[_indices[j]]*_temp[expand(basis_element)];
                        end do;
                        output := addQM(output, _temp, nat);
                    end if;
                end if;
            end do;
        end do;
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> @prodQM fromQMtoPoly output", fromQMtoPoly(output)));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> @prodQM haha check", evalb(expand(fromQMtoPoly(q1)*fromQMtoPoly(q2) - fromQMtoPoly(output)) = 0)));
        return output;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    # Output:
    # returns p but replacing every x with -x
    negQM := proc(p, nat, x)
    local i;
    local output := zeroQM(map(poly -> subs(x=-x, poly), nat));
    local _indices := [indices(p, 'nolist')];
        for i from 1 to nops(_indices) do
            output[expand(subs(x=-x,_indices[i]))] := subs(x=-x, p[_indices[i]]);
        end do;
        return output;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    scalarProdQM := proc(p, sos, nat, x)
    local i;
    local output := zeroQM(nat);
    local _indices := [indices(p, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := sos*p[_indices[i]];
        end do;
        return output;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    splitPO2QM := proc(basis_element, nat);
    local i, elem;
    local todo := map(
        _index -> [expand(mul(elem, elem in map(i -> nat[i], _index))), _index],
        powerset([seq(i, i=1..nops(nat))])
                     );
    local j := 1;
        while true do
            if evalb(expand(todo[j, 1] - basis_element) = 0) then
                return todo[j, 2];
            end if;
            j := j + 1;
        end do;
    end proc;

    # Input:
    # nat is the natural generator basis
    # encoded as a list of polynomials
    certInQM := proc(f, nat, a_0, b_k, x)
    local factorable_sos, certPO, basis, _basis;
    local st;
        factorable_sos, certPO := certInPO(f, nat, x);
    local output := zeroQM(nat), _temp1, _temp2;
        #print(">> factorable_sos", factorable_sos);
        for basis in [indices(certPO, 'nolist')] do
            if evalb(certPO[basis] = 0) = false then
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> basis@certInQM", basis));
                _temp1 := unitQM(nat);
                for _basis in splitPO2QM(basis, nat) do
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> _basis@certInQM", nat[_basis]));
                    _temp2 := zeroQM(nat);
                    updateQMNatEntry(_temp2, nat[_basis], 1);
                    st := time();
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Done 1 one step within _basis@certInQM", fromQMtoPoly(_temp1)));
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Done 2 one step within _basis@certInQM", fromQMtoPoly(_temp2)));
                    _temp1 := prodQM(_temp1, _temp2, a_0, b_k, nat, x);
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Done 3 one step within _basis@certInQM", fromQMtoPoly(_temp1)));
                    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">>"));
                end do;
                _temp1 := scalarProdQM(_temp1, certPO[basis], nat, x);
                output := addQM(output, _temp1, nat);
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(" "));
            end if;
        end do;
        if evalb(factorable_sos = 1) = false then
            output := scalarProdQM(output, factorable_sos, nat, x);
        end if;
        return output;
    end proc;

    fromQMtoPoly := proc(p)
    local y;
        return simplify(add(y,
                            y in map(
                                proc(eq)
                                local ops := op(eq);
                                    ops[1]*ops[2]
                                end proc,
                                [indices(p, 'pairs')])));
    end proc;

    showQM := proc(p)
    local i;
    local _indices := [indices(p, 'nolist')];
        for i from 1 to nops(_indices) do
            lprint("Basis:", _indices[i], " SOS multiplier:", simplify(p[_indices[i]]));
        end do;
    end proc;

    checkCorrectnessQM := proc(p, f)
        return evalb(0 = expand(f - fromQMtoPoly(p)));
    end proc;

# ------------------------------------------------------------------
#) Algorithms from Section 4.1
# Compute certificates of natural generators in terms of split basis

export isBounded;

    isBounded := proc(f, x)
        return type(degree(f, x), even) and lcoeff(f) < 0;
    end proc;

export hasOrd1;

# If check = 1 then it checks for positive sign
# If check = -1 then it checks for negative sign
    hasOrd1 := proc(f, point, x, check)
    local pderiv := diff(f, x);
        return subs(x=point, f) = 0 and subs(x=point, check*pderiv) > 0;
    end proc;

export extractInbetweenSplitFactors;

    extractInbetweenSplitFactors := proc(poly_list, point_a, point_b, x)
        # Assume f = (x - a)*f1
    local f := poly_list[1];
    local roots_f := select(
        _root -> point_a < _root and _root <= point_b and epsSign(f, x, _root) > 0,
        [RealDomain:-solve](f = 0, x));
    local ords_f := map(_root -> ord(f, x, _root), roots_f);
    local size_f := nops(roots_f);

        # Assume g = (x - b)*g1
    local g := poly_list[2];
    local roots_g := select(
        _root -> point_a <= _root and _root < point_b and epsSign(g, x, _root) < 0,
        [RealDomain:-solve](g = 0, x));
    local ords_g := map(_root -> ord(g, x, _root), roots_g);
    local size_g := nops(roots_g);

    local i, j, i_, j_, min_deg := infinity, curr_deg;
        for i from 1 to size_f do
            for j from 1 to size_g do
                curr_deg := max(ords_g[j], ords_f[i]);
                if roots_g[j] < roots_f[i] and curr_deg < min_deg  then
                    min_deg := curr_deg;
                    i_ := i;
                    j_ := j;
                end if;
            end do;
        end do;

        return [
            [roots_f[i_], ords_f[i_]],
            [roots_g[j_], ords_g[j_]]
               ];
    end proc;

export scalarprodCerts;
export addCerts;
export dot_product;

    scalarprodCerts := proc(scalar, certs)
        return map(_poly -> scalar*_poly, certs);
    end proc;

    addCerts := proc(cert1, cert2)
        return map[indices](i -> cert1[i] + cert2[i], cert1);
    end proc;

    dot_product := proc(v1, v2)
    local output := 0, i;
        for i from 1 to nops(v1) do
            output := output + v1[i]*v2[i];
        end do;
        return output;
    end proc;

export splitBasis;
export lemma_4_7;

    splitBasis := proc(basis, semialg_nat, x)

    local poly_roots := map(poly -> [RealDomain:-solve](poly = 0, x), basis);
    local num_poly_roots := map(poly_root -> nops(poly_root), poly_roots);
    local output := [];
    local num_intervals := nops(semialg_nat);
    local num_gens := nops(basis);

    local i, j;
    local min_bounded_deg, min_unbounded_deg;
    local curr_deg;
    local curr_poly1, curr_poly2, poly2_flag;

        min_bounded_deg := infinity;
        min_unbounded_deg := infinity;

        # Left
        for i from 1 to num_gens do
            if hasOrd1(basis[i], semialg_nat[1][1], x, 1) then
                curr_deg := degree(basis[i], x);
                if isBounded(basis[i], x) then
                    if curr_deg < min_bounded_deg then
                        min_bounded_deg := curr_deg;
                        curr_poly1 := basis[i];
                    end if;
                else
                    if min_bounded_deg = infinity
                    and curr_deg < min_unbounded_deg then
                        min_unbounded_deg := curr_deg;
                        curr_poly1 := basis[i];
                    end if;
                end if;
            end if;
        end do;
        output := [op(output), [curr_poly1]];

        # In-between
        for i from 1 to nops(semialg_nat)-1 do
            # Dealing with (semialg_nat[i][2], semialg_nat[i+1][1])

            poly2_flag := false;
            min_bounded_deg := infinity;
            min_unbounded_deg := infinity;

            # Find f_i \in basis such that f = (x-semialg_nat[i][2])*g
            for j from 1 to num_gens do
                if hasOrd1(basis[j], semialg_nat[i][2], x, -1) then
                    curr_deg := degree(basis[j], x);
                    # Keep f_i if f = (x-semialg_nat[i][2])*(x-semialg_nat[i][1])*g
                    if hasOrd1(basis[j], semialg_nat[i+1][1], x, 1) then
                        if isBounded(basis[j], x) then
                            if curr_deg < min_bounded_deg then
                                min_bounded_deg := curr_deg;
                                curr_poly1 := basis[j];
                                poly2_flag := true;
                            end if;
                        else
                            if min_bounded_deg = infinity
                            and curr_deg < min_unbouded_deg then
                                min_unbounded_deg := curr_deg;
                                curr_poly1 := basis[j];
                                poly2_flag := true;
                            end if;
                        end if;
                    else
                        if not(poly2_flag)
                        and isBounded(basis[j], x) then
                            if curr_deg < min_bounded_deg then
                                min_bounded_deg := curr_deg;
                                curr_poly1 := basis[j];
                            end if;
                        else
                            if not(poly2_flag)
                            and min_bounded_deg = infinity
                            and curr_deg < min_unbounded_deg then
                                min_unbounded_deg := curr_deg;
                                curr_poly1 := basis[j];
                            end if;
                        end if;
                    end if;
                end if;
            end do;

            min_bounded_deg := infinity;
            min_unbounded_deg := infinity;

            if poly2_flag then
                output := [op(output), [curr_poly1, curr_poly1]];
            else
                for j from 1 to num_gens do
                    if hasOrd1(basis[j], semialg_nat[i+1][1], x, 1) then
                        curr_deg := degree(basis[j], x);
                        if isBounded(basis[j], x) then
                            if curr_deg < min_bounded_deg then
                                min_bounded_deg := curr_deg;
                                curr_poly2 := basis[j];
                            end if;
                        else
                            if min_bounded_deg = infinity
                            and curr_deg < min_unbounded_deg then
                                min_unbounded_deg := curr_deg;
                                curr_poly2 := basis[j];
                            end if;
                        end if;
                    end if;
                end do;
                output := [op(output), [curr_poly1, curr_poly2]];
            end if;
        end do;

        min_bounded_deg := infinity;
        min_unbounded_deg := infinity;

        # Right
        for i from 1 to num_gens do
            if hasOrd1(basis[i], semialg_nat[num_intervals][2], x, -1) then
                curr_deg := degree(basis[i], x);
                if isBounded(basis[i], x) then
                    if curr_deg < min_bounded_deg then
                        min_bounded_deg := curr_deg;
                        curr_poly1 := basis[i];
                    end if;
                else
                    if min_bounded_deg = infinity
                    and curr_deg < min_unbounded_deg then
                        min_unbounded_deg := curr_deg;
                        curr_poly1 := basis[i];
                    end if;
                end if;
            end if;
        end do;
        output := [op(output), [curr_poly1]];

        return output;
    end proc;

    # This follows the notation in
    # proof of Lemma 4.7
    lemma_4_7 := proc(G_fix, a0, a, b, bl, x)
        # i) Find polynomial q...
    local g_nat := (x - a)*(x - b);
    local c_2 := G_fix[1][1];
    local c_1 := G_fix[2][1];
    local m_2 := G_fix[1][2];
    local m_1 := G_fix[2][2];
    local m := max(m_1, m_2);
    local _m := min(m_1, m_2);
    local alpha2 := 1, alpha3 := 1;

        if m_1 < m_2 then
            alpha2 := (x  - c_2)^(m-_m);
        end if;

        if m_2 < m_1 then
            alpha3 := (x  - c_1)^(m-_m);
        end if;

        alpha2 := 1/((a-b)*(a - c_2)^m)*alpha2;
        alpha3 := 1/((b-a)*(b - c_1)^m)*alpha3;

    local q2 := quo(alpha2*(x-b)*(x-c_2)^m + alpha3*(x-a)*(x-c_1)^m, (x-a)*(x-b), x);
    local alpha1 := 1/1000;
    local q3 := alpha1*(bl - a0) + q2;
        #local q_cert := [0, alpha1*(x-a)^2*(x-b)^2, alpha2*(x-b)^2, alpha3*(x-a)^2, alpha1*(x-a)^2*(x-b)^2];
    local q_cert := [0, alpha1*(x-a)^2*(x-b)^2, alpha2*(x-b)^2, alpha3*(x-a)^2, alpha1*(x-a)^2*(x-b)^2, 0];
        #local Gfix := [x-a0, (x-a)*(x-c_2)^m_2, (x-c_1)^m_1*(x-b), -(x-bl)];
        # TODO Add certificate of -(x-a0)*(x-bl)
    local Gfix := [x-a0, (x-a)*(x-c_2)^m_2, (x-c_1)^m_1*(x-b), -(x-bl), -(x-a0)*(x-bl)];

        # ii) Using q and Theorem 4.3, compute...
    local sigma, tau;
        sigma, tau := basiclemma(g_nat, q3*g_nat + 1, Gfix, x);
        #DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Gfix", Gfix));
        #DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> sigma", sigma));
        #DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> tau", tau));
        #DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> this should be 1", expand(sigma*g_nat + tau*(q3*g_nat + 1))));
        #DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> this should be []", SemiAlgebraic([op(map(_poly -> _poly >= 0, Gfix)), sigma <= 0], [x])));
        #DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> this should be []", SemiAlgebraic([op(map(_poly -> _poly >= 0, Gfix)), tau <= 0], [x])));

        # iii) Compute certificates for...
    local sigma_cert := spCert(sigma, Gfix, x);
    local tau_cert := spCert(tau, Gfix, x);
    local sigma_tau_cert := spCert(sigma*tau, Gfix, x);

        # iv) Using the previous two steps, compute...
    local tau_g_nat_cert := addCerts(
        scalarprodCerts(g_nat^2, sigma_tau_cert),
        scalarprodCerts(tau^2, q_cert));

        return addCerts(
            scalarprodCerts(g_nat^2, sigma_cert),
            addCerts(
                scalarprodCerts(g_nat^2*q3, tau_cert),
                tau_g_nat_cert));
    end proc;
# ------------------------------------------------------------------

# --------------------------------------------------------------
#) Algorithms from Section 4.2
# Compute certificates of split basis in terms of original basis

export findDeg1Complement;
export findDeg2Complement;

    # Returns sigma, tau, h
    # such that:
    # *) sigma, tau \in \sum{\mathbb{R}[x]}^2
    # *) sigma gen + tau h = 1
    # *) tau = \pm (x - \alpha) with \alpha \in \mathbb{R}
    findDeg1Complement := proc(f, bound, x);
    local roots_f := RealDomain:-solve(f = 0, x);
        #local eps1 := -computeMin([[min(roots_f) <= x, x <= max(roots_f)]], f, x)[2];
    local eps1 := -minimize(f, x= min(roots_f) .. max(roots_f));
        # There should be only one real root of eps1 - f
    local alpha := RealDomain:-solve(eps1 - f = 0, x);
    local beta, _sign;
        if lcoeff(f) > 0 then
            beta := max(ceil(alpha), bound);
            _sign := -1;
        else
            beta := min(floor(alpha), bound);
            _sign := 1;
        end if;
    local eps2 := -eps1 + subs(x = beta, f);
    local sigma := 1/(eps2 + eps1);
    local h := _sign*(x-beta);
        return sigma, sigma*(quo(eps2 + eps1 - f, h, x)), h;
    end proc;

    findDeg2Complement := proc(f, lower_bound, upper_bound, x);
    local roots_f := RealDomain:-solve(f = 0, x);
        #local eps1 := -computeMin([[min(roots_f) <= x, x <= max(roots_f)]], f, x)[2];
    local eps1 := -minimize(f, x= min(roots_f) .. max(roots_f));
    local eps2 := max(0, -eps1 + subs(x = lower_bound, f), -eps1 + subs(x = upper_bound, f));
    local sigma := 1/(eps2 + eps1);
    local alpha := RealDomain:-solve(eps2 + eps1 - f = 0, x);
        # There should be only two real roots of eps1 - f
    local h := -(x-alpha[1])*(x-alpha[2]);
        return sigma, sigma*(quo(eps2 + eps1 - f, h, x)), h;
    end proc;

export splitBoundedCert;
export splitUnboundedCertOneSide;
export splitUnboundedCertBothSides;
export splitUnboundedCert;

    splitBoundedCert := proc(t1, gen, x)
    local t2 := quo(gen, t1, x);
    local sigma, tau;
    local G := [gen];
        sigma, tau := basiclemma(t1, t2, [gen], x);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> sigma", sigma));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> tau", tau));

    local sigma_cert := spCert(sigma, G, x);
    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> sigma_cert", sigma_cert));
    local tau_cert := spCert(tau, G, x);
    DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> tau_cert", tau_cert));
    local tau_gen_cert := [tau_cert[2]*gen^2, tau_cert[1]];

        return addCerts(scalarprodCerts(t1^2, sigma_cert), tau_gen_cert);
    end proc;

    splitUnboundedCertOneSide := proc(gen, basis, bl, x)

    local i, gen_cert := map(0, basis);
        for i from 1 to nops(basis) do
            if expand(gen-basis[i]) = 0 then
                gen_cert[i] := 1;
                break;
            end if;
        end do;
        gen_cert := [0, op(gen_cert)];

    local sigma_2, tau_2, h;
        sigma_2, tau_2, h := findDeg1Complement(gen, bl, x);

    local h_cert := spCert(h, basis, x);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> h_cert", h_cert));

        return h, addCerts(
            scalarprodCerts(sigma_2*gen^2, h_cert),
            scalarprodCerts(tau_2*h^2, gen_cert));
    end proc;

    splitUnboundedCertBothSides := proc(gen, basis, a0, bl, x)
    local i, gen_cert := map(0, basis);
        for i from 1 to nops(basis) do
            if expand(gen-basis[i]) = 0 then
                gen_cert[i] := 1;
                break;
            end if;
        end do;
        gen_cert := [0, op(gen_cert)];

    local sigma_2, tau_2, h;
        sigma_2, tau_2, h := findDeg2Complement(gen, a0, bl, x);

    local h_cert := spCert(h, basis, x);
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> h_cert", h_cert));

        return h, addCerts(
            scalarprodCerts(sigma_2*gen^2, h_cert),
            scalarprodCerts(tau_2*h^2, gen_cert));
    end proc;

    splitUnboundedCert := proc(t1, gen, basis, a0, bl, x)

    local _coeff := lcoeff(gen);
    local _deg := degree(gen, x);
    local h, gen_h_cert;

        if type(_deg, odd) then
            if lcoeff(gen) > 0 then
                h, gen_h_cert := splitUnboundedCertOneSide(gen, basis, bl + 10, x);
            else
                h, gen_h_cert := splitUnboundedCertOneSide(gen, basis, a0 - 10, x);
            end if;
        else
            h, gen_h_cert := splitUnboundedCertBothSides(gen, basis, a0 - 10, bl + 10, x);
        end if;

    local t1_cert_in_gen_h := splitBoundedCert(t1, gen*h, x);
    local output_cert := scalarprodCerts(t1_cert_in_gen_h[2], gen_h_cert);
        output_cert[1] := output_cert[1] + t1_cert_in_gen_h[1];
        return output_cert;
    end proc;

# --------------------------------------------------------------
end module;
