"""N6 cross-check against the INDEPENDENT middle-run arm (sp-midrun, MIDRUN_REPORT.md).

Their headline: in the **r6 frame** (`qM M`) the middle run is **437/439** at the witness, the
failures being (464,464) and (483,483) for the "natural" middle order.  Their numbers were
produced from the r6 frame; mine (n6_midrun.py) are the staircase frame, where the answer is
439/439.  The two objects differ, so the cross-check is: rebuild the r6-frame middle run here
with MY machinery and see whether the same two positions fail.

Method (independent of theirs): full r6 projector qM = (Tm*M*Ti) permuted by the r6 ordering
(first 45 = aL, natural middle, last 45 = bL), over F_p, IsPiv by the Defs4 rank criterion.
"""
import json
import numpy as np
from fractions import Fraction as F

d = json.load(open('extract/out/cert_data.json'))
n, m, k, p = 23, 529, 45, 1000000007


def Lr6(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(1, (22, 0)), (-1, (0, 22))]
    if i < 44: return [(1, (i - 23, i - 22))]
    if i == 44: return [(1, (22, 1)), (-1, (1, 22))]
    return []


def Rr6(j):
    if j < 21: return [(1, (j + 1, j))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(1, (j - 22, 22)), (1, (22, j - 22))]
    if j == 44: return [(1, (22, 22))]
    return []


def aL6(i): return Lr6(i)[0][1]
def bL6(j): return Rr6(j)[0][1]
def idx(a, b): return a * n + b


def rank_mod(A):
    A = A.copy() % p
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r >= rows: break
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0: continue
        i = r + int(nz[0])
        if i != r: A[[r, i]] = A[[i, r]]
        A[r] = A[r] * pow(int(A[r, c]), p - 2, p) % p
        f = A[:, c].copy()
        f[r] = 0
        A = (A - np.outer(f, A[r])) % p
        r += 1
    return r


def build_r6():
    x1 = np.array(d['labels']['x1'], dtype=np.int64) % p
    y1 = np.array(d['labels']['y1'], dtype=np.int64) % p
    x2 = np.array(d['labels']['x2'], dtype=np.int64) % p
    y2 = np.array(d['labels']['y2'], dtype=np.int64) % p
    I = np.eye(n, dtype=np.int64)
    M = np.kron((I - np.outer(x1, y1)) % p, (I - np.outer(x2, y2)) % p) % p
    Nm = np.zeros((m, m), dtype=np.int64)
    for c in range(22):                       # Defs4 Nm: (h+3, c) -> (c, h+3)
        Nm[idx(22, c), idx(c, 22)] = 1
    Tm = (np.eye(m, dtype=np.int64) - Nm) % p
    Ti = (np.eye(m, dtype=np.int64) + Nm) % p
    q = Tm @ M % p @ Ti % p
    used, order, tail = set(), [], []
    for i in range(k):
        order.append(idx(*aL6(i))); used.add(idx(*aL6(i)))
    for j in range(k):
        tail.append(idx(*bL6(j))); used.add(idx(*bL6(j)))
    mid = [u for u in range(m) if u not in used]
    assert len(mid) == 439
    order += mid + tail
    return q[np.ix_(order, order)]


if __name__ == '__main__':
    q = build_r6()
    cache = {}

    def R(X, Y):
        if (X, Y) not in cache:
            cache[(X, Y)] = rank_mod(q[:X, Y:])
        return cache[(X, Y)]

    def piv(i, j):
        return R(i + 1, j) + R(i, j + 1) == R(i, j) + R(i + 1, j + 1) + 1

    print('r6 frame: rank(qM) =', R(m, 0), '(expect 484)')
    r6claim = [(l, 484 + 22 + l) for l in range(1, 22)]
    print('r6 run 21 positions:', sum(piv(i, j) for (i, j) in r6claim), '/21  (proved thm: 21)')
    fails = [i for i in range(45, 484) if not piv(i, i)]
    print(f'r6-frame MIDDLE RUN: {439 - len(fails)}/439 pivots; failing positions {fails}')
    print('sp-midrun reported: 437/439, failing (464,464) and (483,483)')
