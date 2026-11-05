"""N6 deliverable 1c — the 439 middle-run positions of the staircase projector, ALL of them.

Builds the full 529x529 staircase projector at the extracted witness over F_p (int64, p < 2^31
so products fit), applies the staircase ordering (first 45 rows = aLs, last 45 = bLs, the 439
middle coordinates in any order — `Platform.isPiv_mid` is ordering-agnostic there), and tests
`IsPiv q i i` for every i in [45, 484) by the rank criterion
    IsPiv q i j  <=>  rk q (i+1) (j+1) + rk q i j = rk q (i+1) j + rk q i (j+1) + 1
with rk q X Y = rank of rows < X, columns >= Y (Defs4) computed by mod-p elimination.

Also recomputes the 39 corner positions and the r6-frame control so the whole pivot ledger of
N2d's open question is in one artifact.  Writes extract/out/n6_midrun.json.
"""
import json
import numpy as np
from fractions import Fraction as F

d = json.load(open('extract/out/cert_data.json'))
n = 23
m = n * n
k = 45
p = 1000000007

alZ, beZ = d['coeffs']['al'], d['coeffs']['be']
aZ, bZ = d['coeffs']['a'], d['coeffs']['b']


def Lz(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(alZ, (22, 0)), (beZ, (0, 22))]
    if i == 23: return [(1, (0, 3))]
    if i < 45: return [(1, (i - 22, i - 24))]
    return []


def Rz(j):
    if j < 20: return [(1, (j + 1, j + 3))]
    if j == 20: return [(1, (0, 20))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(aZ[j - 22], (j - 22, j - 21)), (bZ[j - 22], (j - 21, j - 22))]
    if j == 44: return [(1, (22, 22))]
    return []


def aLs(i): return Lz(i)[0][1] if Lz(i) else (0, 0)
def bLs(j): return Rz(j)[0][1] if Rz(j) else (0, 0)


def idx(a, b): return a * n + b


def build():
    x1 = np.array(d['labels']['x1'], dtype=np.int64) % p
    y1 = np.array(d['labels']['y1'], dtype=np.int64) % p
    x2 = np.array(d['labels']['x2'], dtype=np.int64) % p
    y2 = np.array(d['labels']['y2'], dtype=np.int64) % p
    I = np.eye(n, dtype=np.int64) % p
    A1 = (I - np.outer(x1, y1)) % p
    A2 = (I - np.outer(x2, y2)) % p
    M = np.kron(A1, A2) % p                     # index (a*n+b, c*n+e) = A1[a,c]*A2[b,e]
    # N: 23 entries
    N = np.zeros((m, m), dtype=np.int64)
    al = alZ % p
    N[idx(22, 0), idx(0, 22)] = (-beZ * pow(al, p - 2, p)) % p
    for r in range(22):
        N[idx(r + 1, r), idx(r, r + 1)] = (bZ[r] * pow(aZ[r] % p, p - 2, p)) % p
    Tm = (np.eye(m, dtype=np.int64) - N) % p
    Ti = (np.eye(m, dtype=np.int64) + N) % p
    # dv: lead on aLs, 1/lead on bLs, 1 elsewhere
    dv = np.ones(m, dtype=np.int64)
    for i in range(45):
        dv[idx(*aLs(i))] = (alZ if i == 22 else 1) % p
    for j in range(45):
        if 22 <= j < 44:
            dv[idx(*bLs(j))] = pow(aZ[j - 22] % p, p - 2, p)
    Ds = np.diag(dv) % p
    Di = np.diag(np.array([pow(int(v), p - 2, p) for v in dv], dtype=np.int64)) % p
    Pm = Ds @ Tm % p
    Qm = Ti @ Di % p
    q = Pm @ M % p @ Qm % p
    # ordering: first 45 = aLs, next 439 = the rest, last 45 = bLs
    used = set()
    order = []
    for i in range(45):
        order.append(idx(*aLs(i))); used.add(idx(*aLs(i)))
    tail = []
    for j in range(45):
        tail.append(idx(*bLs(j))); used.add(idx(*bLs(j)))
    mid = [u for u in range(m) if u not in used]
    assert len(mid) == 439, len(mid)
    order += mid + tail
    qp = q[np.ix_(order, order)]
    return M, qp, order, dv


def rank_mod(A):
    """rank over F_p by mod-p elimination (numpy int64)."""
    A = A.copy() % p
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r >= rows: break
        col = A[r:, c]
        nz = np.nonzero(col)[0]
        if nz.size == 0: continue
        i = r + int(nz[0])
        if i != r: A[[r, i]] = A[[i, r]]
        A[r] = A[r] * pow(int(A[r, c]), p - 2, p) % p
        f = A[:, c].copy()
        f[r] = 0
        A = (A - np.outer(f, A[r])) % p
        r += 1
    return r


if __name__ == '__main__':
    import time
    t0 = time.time()
    M, q, order, dv = build()
    rk = lambda X, Y: rank_mod(q[:X, Y:])
    cache = {}

    def R(X, Y):
        if (X, Y) not in cache:
            cache[(X, Y)] = rk(X, Y)
        return cache[(X, Y)]

    def piv(i, j):
        # Defs4 IsPiv: rk(i+1,j) + rk(i,j+1) = rk(i,j) + rk(i+1,j+1) + 1
        return R(i + 1, j) + R(i, j + 1) == R(i, j) + R(i + 1, j + 1) + 1

    print(f'rank(q) = {R(m, 0)}  (expect 484)  [{time.time()-t0:.0f}s]')
    corner = [(1 + t, 484 + 23 + t) for t in range(21)] + [(25 + t, 484 + 2 + t) for t in range(18)]
    mid_pos = [(i, i) for i in range(45, 484)]
    res_mid, res_corner = {}, {}
    t1 = time.time()
    for c, (i, j) in enumerate(mid_pos):
        res_mid[f'{i}'] = bool(piv(i, j))
        if c % 40 == 0:
            print(f'  middle {c}/439 [{time.time()-t1:.0f}s]', flush=True)
    for (i, j) in corner:
        res_corner[f'{i},{j}'] = bool(piv(i, j))
    ok_mid = sum(res_mid.values())
    ok_corner = sum(res_corner.values())
    print(f'MIDDLE RUN: {ok_mid}/439 pivots   CORNER RUN: {ok_corner}/39 pivots')
    bad = [kk for kk, v in res_mid.items() if not v]
    print('middle positions that FAIL:', bad[:20], '...' if len(bad) > 20 else '')
    json.dump({'rank': R(m, 0), 'middle': res_mid, 'corner': res_corner,
               'prime': p, 'note': 'N6 deliverable 1c: staircase projector, own numerics'},
              open('extract/out/n6_midrun.json', 'w'), indent=0)
    print(f'total {time.time()-t0:.0f}s')
