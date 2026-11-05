"""MIDRUN deliverable 2 (+ generic control arms): does the middle-run pivot status of
qM M depend on flagEquiv's ARBITRARY middle order?

flagEquiv is only pinned on the first 45 (aL) and last 45 (bL) positions
(Defs4:891-903 exists_flagEquiv); the middle 439 are whatever Classical.choose picks.
The Lean statement quantifies over fixed flag positions, so it is provable only if the
answer is order-UNIFORM.  We rebuild qM M under 4 middle orders x 2 primes and compare
the full pc profile on the middle block.  Control arms: 3 random label sets satisfying
y.x = 1, hu/hv/hT != 0 (n2d_generic_probe.py's generator, rational labels reduced mod p)
with the STAIRCASE-frame corner invertible (the statement's hdet), natural order.

Outputs extract/out/midrun_orders.json.
"""
import json
import random
from fractions import Fraction as F
import midrun_lib as L

x1, y1, x2, y2, d = L.witness()
Q = L.qM_pair_coords(x1, y1, x2, y2)

def stair_corner_invertible(x1, y1, x2, y2, p):
    """hdet analogue: rank of the staircase-frame corner (LtermsStair/RtermsStair) = 45 mod p."""
    al, be = d['coeffs']['al'], d['coeffs']['be']
    aC, bC = d['coeffs']['a'], d['coeffs']['b']
    def Mof(xx1, yy1, xx2, yy2):
        A1 = [[(1 if a == c else 0) - xx1[a] * yy1[c] for c in range(23)] for a in range(23)]
        A2 = [[(1 if b == e else 0) - xx2[b] * yy2[e] for e in range(23)] for b in range(23)]
        return [[A1[a][c] * A2[b][e] for c in range(23) for e in range(23)]
                for a in range(23) for b in range(23)]
    def Ls(i):
        if i < 22: return [(1, (i, i))]
        if i == 22: return [(al, (22, 0)), (be, (0, 22))]
        if i == 23: return [(1, (0, 3))]
        if i < 45: return [(1, (i - 22, i - 24))]
        return []
    def Rs(j):
        if j < 20: return [(1, (j + 1, j + 3))]
        if j == 20: return [(1, (0, 20))]
        if j == 21: return [(1, (0, 21))]
        if j < 44: return [(aC[j - 22], (j - 22, j - 21)), (bC[j - 22], (j - 21, j - 22))]
        if j == 44: return [(1, (22, 22))]
        return []
    M = Mof(x1, y1, x2, y2)
    C = [[sum(cs * ct * M[a * 23 + b][c * 23 + e]
              for cs, (a, b) in Ls(i) for ct, (c, e) in Rs(j)) % p
          for j in range(45)] for i in range(45)]
    R = [row[:] for row in C]
    r = 0
    for c in range(45):
        piv = next((i for i in range(r, 45) if R[i][c]), None)
        if piv is None: continue
        R[r], R[piv] = R[piv], R[r]
        inv = pow(R[r][c], p - 2, p)
        for i in range(45):
            if i != r and R[i][c]:
                f = R[i][c] * inv % p
                R[i] = [(R[i][j] - f * R[r][j]) % p for j in range(45)]
        r += 1
    return r

out = {'question': 'is the r6-frame middle-run claim of qM M uniform over flagEquiv middle orders?',
       'witness_orders': {}, 'generic_controls': []}

print('=== witness: 4 middle orders x 2 primes ===')
profiles = {}
for kind in ('natural', 'reversed', 'shuffled', 'colmajor'):
    flag = L.flag_order(kind)
    pcs = {p: L.rightmost_pivots(Q, p, flag)[0] for p in (L.P1, L.P2)}
    assert pcs[L.P1] == pcs[L.P2], (kind, 'prime disagreement')
    pc = pcs[L.P1]
    fails = [i for i in range(L.MID_LO, L.MID_HI) if pc[i] != i]
    profiles[kind] = pc
    out['witness_orders'][kind] = {
        'middle_fails': fails,
        'middle_pivots': 439 - len(fails),
        'pc_mid_delta': {str(i): pc[i] for i in fails},
        'rank': sum(1 for c in pc if c >= 0),
        'corner21_ok': all(pc[i] == i + 506 for i in range(1, 22)),
        'corner_rows_pc': {r: pc[r] for r in range(45)},
    }
    print(f'{kind:9s}: middle pivots {439 - len(fails)}/439  fails at {fails}'
          f'  (pc there: {[pc[i] for i in fails]})  corner21 {out["witness_orders"][kind]["corner21_ok"]}')

uniform = len({tuple(p[L.MID_LO:L.MID_HI]) for p in profiles.values()}) == 1
out['middle_profile_order_uniform'] = uniform
out['all_orders_fail_positions'] = sorted(set().union(
    *(set(o['middle_fails']) for o in out['witness_orders'].values())))
print('middle pc profile order-uniform:', uniform)
print('union of failing positions over orders:', out['all_orders_fail_positions'])

print('=== generic control arms (natural order, y.x=1, hu/hv/hT != 0, stair corner rank 45) ===')
rng = random.Random(20261106)
for trial in range(3):
    while True:
        g = lambda: F(rng.randrange(1, 50))
        gx1 = [g() for _ in range(23)]; gy1 = [F(rng.randrange(-5000, 5000)) for _ in range(23)]
        gx2 = [g() for _ in range(23)]; gy2 = [F(rng.randrange(-5000, 5000)) for _ in range(23)]
        gy1[0] = (1 - sum(gy1[i] * gx1[i] for i in range(1, 23))) / gx1[0]
        gy2[0] = (1 - sum(gy2[i] * gx2[i] for i in range(1, 23))) / gx2[0]
        if (gx1[0] * gx2[0] != 0 and gy1[22] * gy2[22] != 0
                and all(gx1[l] * gy1[22] + gx2[l] * gy2[22] != 0 for l in range(1, 22))):
            break
    red = lambda v, p: int(v.numerator * pow(v.denominator, p - 2, p)) % p
    res = {}
    for p in (L.P1, L.P2):
        rx1 = [red(v, p) for v in gx1]; ry1 = [red(v, p) for v in gy1]
        rx2 = [red(v, p) for v in gx2]; ry2 = [red(v, p) for v in gy2]
        assert sum(ry1[i] * rx1[i] for i in range(23)) % p == 1
        s = stair_corner_invertible(rx1, ry1, rx2, ry2, p)
        Qg = L.qM_pair_coords(rx1, ry1, rx2, ry2)
        pcg, rank = L.rightmost_pivots(Qg, p, L.flag_order('natural'))
        fails = [i for i in range(L.MID_LO, L.MID_HI) if pcg[i] != i]
        res[p] = (s, rank, fails, pcg)
    (s1, r1, f1, pc1), (s2, r2, f2, pc2) = res[L.P1], res[L.P2]
    assert (r1, f1) == (r2, f2), ('prime disagreement', trial)
    out['generic_controls'].append({'trial': trial, 'stair_corner_rank': s1,
                                    'rank_qM': r1, 'middle_fails': f1,
                                    'middle_pivots': 439 - len(f1),
                                    'corner21_ok': all(pc1[i] == i + 506 for i in range(1, 22)),
                                    'n_corner_rows_in_SW': sum(1 for c in pc1[:45] if c < 484)})
    print(f'trial {trial}: stair corner rank {s1} | rank(qM) {r1} | middle pivots '
          f'{439 - len(f1)}/439 fails {f1[:8]}{"..." if len(f1) > 8 else ""} ({len(f1)} total)'
          f' | corner21 {out["generic_controls"][-1]["corner21_ok"]}'
          f' | corner rows pivoting into SW: {out["generic_controls"][-1]["n_corner_rows_in_SW"]}')

json.dump(out, open('extract/out/midrun_orders.json', 'w'))
print('wrote extract/out/midrun_orders.json')
