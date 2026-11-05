#!/usr/bin/env python3
"""N3 data: integer kernel certificate for the staircase data corner.

Mirrors nb_flagBasis_solution.lean:97-147 (cert_chk / cert_entries / data_cert over
certChk, Defs4:1000) at the STAIRCASE flag family (check_stair.py design(23,'stair')
rows/cols) instead of r6's LtermsZ/RtermsZ (Defs4:1004-1016 region).

Witness point: check_stair --ij mode (U = V = I + J explicit, check_stair.py:157), first
sampled line pair (seed=1, prng=Random(8)), labels lifted from ZMod P (P = 67108859,
check_stair.py:26) to Z, then corrected by extended-Euclid shifts of multiples of P so
that y . x = 1 EXACTLY over Z (the correction leaves every value unchanged mod P, hence
leaves the corner mod P - and its nonzero det - untouched).

Family coefficients: sparse_params(23, Random(1001)) (check_stair.py:93-95,160) lifted
to [0, P). Corner computed over Z exactly (replicating check_stair.corner_at without
mod), verified det != 0 mod P, inverse mod P dumped as certRows'/certCols' in the r6
certChk convention (rows . cols == 1 mod p, cols[j] = column j of the inverse).

Output: extract/out/cert_data.json; asserts every check.
"""
import json, os, random, sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'jainroot', 'independent', 'deferred-readout'))
import linalg
import check_stair as cs

OUT = os.path.join(HERE, 'out')
os.makedirs(OUT, exist_ok=True)
P = cs.P
H = 23


def egcd(a, b):
    if b == 0:
        return (a, 1, 0)
    g, u, w = egcd(b, a % b)
    return (g, w, u - (a // b) * w)


def lift(x):
    return x % P


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def fix_dot(x, y, target=1):
    """Return y' == y (mod P) with dot(x, y') == target exactly over Z."""
    d = dot(x, y)
    need = target - d
    assert need % P == 0, (d, 'dot not congruent to target mod P')
    k = need // P
    if k == 0:
        return list(y)
    # vector Bezout: coefficients c_i with sum c_i x_i = g = gcd(x), then shift by k*P/g
    coeffs = []
    g = 0
    u_prev, v_prev = 1, 0  # Bezout of running gcd against current entry
    cs_acc = []            # accumulated Bezout coeffs for the running gcd
    for xi in x:
        g2, u2, v2 = egcd(g, xi)
        cs_acc = [c * u2 for c in cs_acc] + [v2]
        g = g2
    assert g != 0
    rhs = k * P
    assert rhs % g == 0, 'dot correction unsolvable'
    y2 = [yi + ci * (rhs // g) for yi, ci in zip(y, cs_acc)]
    assert dot(x, y2) == target and all((a - b) % P == 0 for a, b in zip(y, y2))
    return y2


def main():
    # --- witness point (--ij mode, first sampled pair, same RNG order as check_stair.main)
    U = [[1 + int(i == k) for k in range(H)] for i in range(H)]
    V = [r[:] for r in U]
    U = [[x % P for x in r] for r in U]
    V = [[x % P for x in r] for r in V]
    Ui, Vi = linalg.inv_mod_matrix(U, P), linalg.inv_mod_matrix(V, P)
    sp = cs.sparse_params(H, random.Random(1000 + 1))
    trip = list(combinations(range(H), 3))
    prng = random.Random(1 + 7)
    UT = [list(c) for c in zip(*U)]
    VT = [list(c) for c in zip(*V)]
    i9, i2 = cs.iv(9), cs.iv(2)

    def line(t, AT, Ai):
        tv = [int(i in t) for i in range(H)]
        g = [(x - 3 * i9) * i2 % P for x in tv]
        return cs.mv(AT, tv), cs.mv(Ai, g)

    t1, t2 = prng.choice(trip), prng.choice(trip)
    p, xi = line(t1, UT, Ui)
    v, nu = line(t2, VT, Vi)
    # lift to Z and fix dots exactly (x1=p, y1=xi, x2=v, y2=nu; need y.x = 1)
    pZ = [lift(a) for a in p]
    xiZ = fix_dot(pZ, [lift(a) for a in xi])
    vZ = [lift(a) for a in v]
    nuZ = fix_dot(vZ, [lift(a) for a in nu])
    assert dot(xiZ, pZ) == 1 and dot(nuZ, vZ) == 1
    # --- staircase family with concrete Z coefficients (sparse_params lifted)
    alZ, beZ = lift(sp['al']), lift(sp['be'])
    aZ = [lift(x) for x in sp['a']]
    bZ = [lift(x) for x in sp['b']]
    RC, CC = cs.design(H, 'stair')
    rows = [{(b, b): 1} for b in range(H - 1)] + [{(H - 1, 0): alZ, (0, H - 1): beZ}] + \
           [{c: 1} for c in RC]
    cols = [{c: 1} for c in CC] + [{(j, j + 1): aZ[j], (j + 1, j): bZ[j]} for j in range(H - 1)] + \
           [{(H - 1, H - 1): 1}]

    # --- corner over Z: replicate check_stair.corner_at with q1 = I - pZ xiZ^T etc, NO mod
    n = 2 * H - 1
    q1 = [[int(i == k) - pZ[i] * xiZ[k] for k in range(H)] for i in range(H)]
    q2 = [[int(i == k) - vZ[i] * nuZ[k] for k in range(H)] for i in range(H)]
    CZ = [[0] * n for _ in range(n)]
    for j, col in enumerate(cols):
        G = [[0] * H for _ in range(H)]
        for (a, b), val in col.items():
            G[a][b] = val
        qG = [[sum(q1[i][k] * G[k][l] for k in range(H)) for l in range(H)] for i in range(H)]
        Y = [[sum(qG[i][l] * q2[k][l] for l in range(H)) for k in range(H)] for i in range(H)]
        for i, row in enumerate(rows):
            CZ[i][j] = sum(val * Y[a][b] for (a, b), val in row.items())
    CZmod = [[x % P for x in r] for r in CZ]
    # sanity: matches check_stair's mod-P corner (corner_at) at the same point
    Cref = cs.corner_at(H, rows, cols, p, xi, v, nu)  # same lifts => equal mod P
    assert CZmod == [[x % P for x in r] for r in Cref], 'Z corner != check_stair corner mod P'
    # det mod P via elimination
    def det_mod(A, p):
        Mx = [r[:] for r in A]
        d = 1
        for c in range(len(Mx)):
            piv = next((r for r in range(c, len(Mx)) if Mx[r][c] % p), None)
            if piv is None:
                return 0
            if piv != c:
                Mx[c], Mx[piv] = Mx[piv], Mx[c]
                d = -d
            inv = pow(Mx[c][c], p - 2, p)
            d = d * Mx[c][c] % p
            Mx[c] = [x * inv % p for x in Mx[c]]
            for r in range(len(Mx)):
                if r != c and Mx[r][c]:
                    f = Mx[r][c]
                    Mx[r] = [(a - f * b) % p for a, b in zip(Mx[r], Mx[c])]
        return d % p
    detP = det_mod(CZmod, P)
    assert detP != 0, 'corner singular mod P'
    invP = linalg.inv_mod_matrix(CZmod, P)
    certRows = CZmod                                    # rows . inv == 1
    certCols = [list(c) for c in zip(*invP)]            # cols[j] = column j of inverse (r6 convention)
    # verify the r6 certChk product convention: of(rows) * of(fun l j => cols[j][l]) == 1
    prod = [[sum(CZmod[i][l] * invP[l][j] for l in range(n)) % P for j in range(n)]
            for i in range(n)]
    assert prod == [[int(i == j) for j in range(n)] for i in range(n)]

    res = dict(
        certP=P, det_mod_P=detP,
        labels=dict(x1=pZ, y1=xiZ, x2=vZ, y2=nuZ,
                    dot1=dot(xiZ, pZ), dot2=dot(nuZ, vZ)),
        coeffs=dict(al=alZ, be=beZ, a=aZ, b=bZ),
        RC=[list(c) for c in RC], CC=[list(c) for c in CC],
        cornerZ_entry_sizes=dict(max_abs=max(max(abs(x) for x in r) for r in CZ),
                                 max_digits=len(str(max(max(abs(x) for x in r) for r in CZ)))),
        certRows=certRows, certCols=certCols,
        ij_mode=True, seed=1, first_pair=[list(t1), list(t2)],
    )
    with open(os.path.join(OUT, 'cert_data.json'), 'w') as fh:
        json.dump(res, fh)
    print('certP=%d det!=0: %s; label max digits=%d; corner entry max digits=%d; dots=%d,%d'
          % (P, detP != 0, max(len(str(abs(a))) for a in pZ + xiZ + vZ + nuZ),
             res['cornerZ_entry_sizes']['max_digits'], res['labels']['dot1'],
             res['labels']['dot2']))
    print('OK')


if __name__ == '__main__':
    main()
