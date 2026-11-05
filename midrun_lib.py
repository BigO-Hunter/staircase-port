"""Shared machinery for the mid-run study (exact arithmetic).

Frame (r6): qM M = (Tm * M * Ti).submatrix flagEquiv flagEquiv with M the flattened
Kronecker (1 - x1 y1^T) (x) (1 - x2 y2^T), h = 19 (carrier h+3 = 22, corner 2h+7 = 45,
m = (h+4)^2 = 529).  Defs4:853-942.

PIVOT-PROFILE THEOREM (the workhorse here, matches the producer's convention):
for the rightmost-pivot echelon pc of a matrix (rows processed top to bottom, each new
row reduced against all previous pivot rows, pc_i = rightmost nonzero column of the
reduced row, -1 if it dies) one has, for EVERY (X, Y):

    rk(X, Y) = #{r < X : pc_r >= Y}

(producer: check_stair.py:175 rho[i][j] = #{r <= i : pc[r] >= j}; linalg.py:150-162
rightmost_pivots).  Proof: pivot rows restricted to cols >= Y keep their rightmost
nonzero at pc_r, so the ones with pc_r >= Y are independent (ordered triangularly) and
the ones with pc_r < Y restrict to zero.  Hence

    IsPiv(i, j)  <=>  pc_i = j .

One 529x529 elimination answers every NE-block rank of the run claims.

Exactness: everything is integer; modular reduction mod p uses only int64-safe products
(p < 2^31, so f*y < 2^62).
"""
import json
import numpy as np

N = 23          # Pr 23
CAR = 22        # h+3, h = 19
K45 = 45        # 2h+7
M529 = 529      # (h+4)^2
MID_LO, MID_HI = 45, 484          # middle-run flag positions [45, 484)
P1, P2 = 1000000007, 998244353

STAIR_DATA_RUNS = [(45, 45, 439), (1, 507, 21), (25, 486, 18)]
STAIR_SINGLES = [(0, 528, 1), (22, 506, 1), (23, 505, 1), (24, 504, 1), (43, 485, 1), (44, 484, 1)]


def witness():
    d = json.load(open('extract/out/cert_data.json'))
    L = d['labels']
    return L['x1'], L['y1'], L['x2'], L['y2'], d


def kronecker_M(x1, y1, x2, y2):
    """M[P(a,b)][P(c,e)] = A1[a][c] * A2[b][e], A_i = 1 - x_i y_i^T (exact ints)."""
    A1 = [[(1 if a == c else 0) - x1[a] * y1[c] for c in range(N)] for a in range(N)]
    A2 = [[(1 if b == e else 0) - x2[b] * y2[e] for e in range(N)] for b in range(N)]
    M = [[0] * M529 for _ in range(M529)]
    for a in range(N):
        for b in range(N):
            row, g = M[a * N + b], A2[b]
            for c in range(N):
                f = A1[a][c]
                if f == 0:
                    continue
                cb = c * N
                for e in range(N):
                    v = g[e]
                    if v:
                        row[cb + e] = f * v
    return M


def apply_T(Q, sign):
    """conjugate by T^(sign): Tm = 1 - Nm (sign=-1), Ti = 1 + Nm (sign=+1).
    Nm[u][v] = 1 iff u=(CAR,b), b<CAR, v=(b,CAR)   (Defs4:877-881).
    Right-multiply by (1 + s*Nm): col w gains s*col (CAR,w.1) when w=(a,CAR), a<CAR.
    Left-multiply by  (1 + s*Nm): row u gains s*row (u.2,CAR) when u=(CAR,b), b<CAR."""
    if sign > 0:
        # Ti on the right: new[u][w] = Q[u][w] + Q[u][(CAR, w.1)] if w=(a, CAR), a < CAR
        for w1 in range(CAR):                      # w = (w1, CAR)
            src = CAR * N + w1                     # pair (CAR, w1)
            for u in range(M529):
                Q[u][w1 * N + CAR] += Q[u][src]
        # Tm on the left: new[u][w] = Q[u][w] - Q[(u.2, CAR)][w] if u=(CAR,b), b < CAR
        for b in range(CAR):                       # u = (CAR, b)
            src = b * N + CAR                      # pair (b, CAR)
            for w in range(M529):
                Q[CAR * N + b][w] -= Q[src][w]
    return Q


def qM_pair_coords(x1, y1, x2, y2):
    """Tm * M * Ti in PAIR coordinates (exact ints), 529x529."""
    Q = kronecker_M(x1, y1, x2, y2)
    apply_T(Q, +1)   # M * Ti
    apply_T(Q, -1)   # Tm * (M * Ti)
    return Q


def aL(i):
    if i < CAR: return (i, i)
    if i == CAR: return (CAR, 0)
    if i < 2 * CAR: return (i - (CAR + 1), i - (CAR + 1) + 1)
    return (CAR, 1)


def bL(j):
    if j < CAR - 1: return (j + 1, j)
    if j == CAR - 1: return (0, CAR - 1)
    if j < 2 * CAR: return (j - CAR, CAR)
    return (CAR, CAR)


def flag_order(kind, seed=20261105):
    """Concrete flagEquiv: first 45 = aL(0..44), last 45 = bL(0..44), middle = 'kind'."""
    top = [aL(i) for i in range(K45)]
    bot = [bL(j) for j in range(K45)]
    used = set(top) | set(bot)
    pairs = [(a, b) for a in range(N) for b in range(N) if (a, b) not in used]
    assert len(pairs) == M529 - 2 * K45 == 439
    if kind == 'natural':        # row-major (n2d_qm_corner_check.py's order)
        pass
    elif kind == 'reversed':
        pairs = pairs[::-1]
    elif kind == 'shuffled':
        import random
        random.Random(seed).shuffle(pairs)
    elif kind == 'colmajor':     # column-major
        pairs = [(a, b) for b in range(N) for a in range(N) if (a, b) not in used]
    else:
        raise ValueError(kind)
    flag = top + pairs + bot
    assert len(flag) == M529 and len(set(flag)) == M529
    return flag


def rightmost_pivots(Q, p, flag):
    """pc of Q in flag coordinates mod p.  Exact: all intermediates int64-safe.
    Returns (pc list length 529, rank).  Row i is reduced on demand against previous
    pivot rows == producer's eager downward elimination (same reduced row)."""
    Qm = np.array([[v % p for v in row] for row in Q], dtype=np.int64)
    idx = np.array([flag[u][0] * N + flag[u][1] for u in range(M529)])
    Qm = Qm[np.ix_(idx, idx)] % p
    pc = [-1] * M529
    pivrows = {}
    for i in range(M529):
        row = Qm[i]
        while True:
            nz = np.nonzero(row)[0]
            if nz.size == 0:
                break
            c = int(nz[-1])
            pr = pivrows.get(c)
            if pr is None:
                pivrows[c] = row
                pc[i] = c
                break
            f = int(row[c]) * pow(int(pr[c]), p - 2, p) % p
            row = (row - f * pr) % p
    return pc, len(pivrows)


def rho_table(pc):
    """rho[X][j] = #{r < X : pc_r >= j} (529+1 x 529+1)."""
    ind = np.zeros((M529, M529 + 1), dtype=np.int64)
    for r, c in enumerate(pc):
        if c >= 0:
            ind[r, :c + 1] = 1
    return np.vstack([np.zeros((1, M529 + 1), dtype=np.int64), np.cumsum(ind, axis=0)])


def rk_of(rho, X, Y):
    return int(rho[X, Y])


def ispiv(rho, i, j):
    return (rk_of(rho, i + 1, j) + rk_of(rho, i, j + 1)
            == rk_of(rho, i, j) + rk_of(rho, i + 1, j + 1) + 1)


def claimed_positions():
    """runPairs (stairDataRuns 23 529) ++ singles, tagged."""
    out = []
    for (a, b, r) in STAIR_DATA_RUNS:
        tag = 'middle' if r == 439 else ('corner21' if r == 21 else 'corner18')
        out += [{'pos': (a + k, b + k), 'tag': tag} for k in range(r)]
    for (a, b, r) in STAIR_SINGLES:
        out.append({'pos': (a, b), 'tag': 'single'})
    return out


def analyze(Q, p, flag):
    """pc, rho, and the full verdict table for one (matrix, prime, order)."""
    pc, rank = rightmost_pivots(Q, p, flag)
    rho = rho_table(pc)
    res = []
    for t in claimed_positions():
        i, j = t['pos']
        t.update(A=rk_of(rho, i, j), B=rk_of(rho, i + 1, j),
                 C=rk_of(rho, i, j + 1), D=rk_of(rho, i + 1, j + 1))
        t['ispiv'] = ispiv(rho, i, j)
        t['pc'] = pc[i]
        res.append(t)
    return pc, rank, rho, res
