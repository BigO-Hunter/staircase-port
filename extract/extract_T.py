#!/usr/bin/env python3
"""Resolve T for staircase witness-1 (task b).

T is the temporary-role budget of QHNet (ZMod 2) W T 529 (Defs4:212 `structure QHNet`).
r6: T = 3217907 = 46v + N with v = C(h,3) = 1771, N = v^2 = 3136441
(accepted_bitNetR6_mom.lean:2126-2127: tmp1(b,c)=23b+c, tmp2(a,c)=23v+23a+c,
tau(a1,a2)=46v+a1v+a2, "T = 46 v + N = 3217907"); the R8 Oppbank port kept the same T
(Def_IntMul_Kappa_R8_Data_BitOppbankConsts.lean:16,45 "same temporary budget as R6").
Witness-1 (certificate_round7.py:27-30) has the SAME h=23 hence same v, N; only R and W
change (deferred.py:187: W = 2N + 2vR). This script recomputes all of it from the frozen
witness_23.json.gz / deferred_23.json.gz and asserts the r6-side identities.
Output: extract/out/T_data.json
"""
import json, os, sys
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'jainroot', 'independent', 'deferred-readout'))
sys.path.insert(0, os.path.join(HERE, 'jainroot', 'scripts'))
import deferred as dr
import certificate_round7 as c7

OUT = os.path.join(HERE, 'out')
os.makedirs(OUT, exist_ok=True)

wit = c7.WITNESSES[0]                      # staircase headline witness (certificate_round7.py:26-31)
W, D = dr.load(wit['h'], wit['witness'], wit['data'])
S = dr.Schedule(W, D)

h = S.h                                    # 23
v = len(S.trip)                            # C(23,3) = 1771
N = v * v                                  # 3136441
R = S.R                                    # 28866 slots
T = 46 * v + N                             # r6 addressing (accepted_bitNetR6_mom.lean:2126-2127)
Wroles = 2 * N + 2 * v * R                 # deferred.py:187 Wd = 2N + 2A, A = vR
L = 2 * v * h * (h - 1)

cov = S.adjoint(); ylev = S.ylevels(cov); rk = dr.chain_ranks(S); xd = S.xdata()
c = dr.histogram(S, rk, ylev, xd, dr.STAIRCASE_CORNER(h))

res = dict(
    h=h, v=v, N=N, R=R, T=T, W=Wroles, L=L, s=c['s'],
    sum_nw=sum(c['hist'].values()),
    checks=dict(
        h_is_23=(h == 23), v_is_C23_3=(v == comb(23, 3) == 1771),
        N_is_v2=(N == 1771 ** 2 == 3136441),
        R_is_28866=(R == 28866),
        T_is_3217907=(T == 3217907),
        T_equals_46v_plus_N=(T == 46 * v + N),
        W_is_108516254=(Wroles == 108516254),
        W_matches_histogram=(c['W'] == Wroles),
        ranksum_matches_histogram=(c['s'] == 57403754177),
        sum_nw_matches=(sum(c['hist'].values()) == 1905413587),
        staircase_corner=dr.STAIRCASE_CORNER(h),
        r6_T_reference=3217907,
    ),
    note=("T = 46v + N depends only on (h, v, N): the per-invocation temporaries tmp1/tmp2 "
          "(23 per stage-1/stage-2 invocation pair set) and tau(a1,a2) = 46v + a1 v + a2 "
          "(N pair slots). Witness-1 keeps h=23 => v=1771, N=3136441 => T=3217907, same as "
          "r6. CAVEAT: the tau addressing lives in the Lean QHNet construction (Defs), not in "
          "the frozen JSON; final confirmation is the net definition itself (port task N5/D2)."),
)
allc = [x for k, x in res['checks'].items() if isinstance(x, bool)]
res['all_checks_pass'] = all(allc)
with open(os.path.join(OUT, 'T_data.json'), 'w') as fh:
    json.dump(res, fh, indent=1)
print(json.dumps({k: res[k] for k in ('h', 'v', 'N', 'R', 'T', 'W', 'L', 's', 'sum_nw',
                                      'all_checks_pass')}, indent=1))
assert res['all_checks_pass'], 'CHECK FAIL: %s' % res['checks']
print('OK')
