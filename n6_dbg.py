import json
import numpy as np
from fractions import Fraction as F
import n6_midrun as nm

d = json.load(open('extract/out/cert_data.json'))
n, p = 23, 1000000007
M, q, order, dv = nm.build()

# independent corner matrix (exact Fractions, same as n6_proj_probe)
def corner_of(Mf, Lf, Rf):
    C = [[F(0)] * 45 for _ in range(45)]
    for i in range(45):
        for j in range(45):
            s = F(0)
            for cs, (a, b) in Lf(i):
                for ct, (c, e) in Rf(j):
                    s += cs * ct * Mf[(a * n + b, c * n + e)]
            C[i][j] = s
    return C

x1 = [F(v) for v in d['labels']['x1']]
y1 = [F(v) for v in d['labels']['y1']]
x2 = [F(v) for v in d['labels']['x2']]
y2 = [F(v) for v in d['labels']['y2']]
A1 = [[(1 if a == c else 0) - x1[a] * y1[c] for c in range(n)] for a in range(n)]
A2 = [[(1 if a == c else 0) - x2[a] * y2[c] for c in range(n)] for a in range(n)]
Mf = {(a * n + b, c * n + e): A1[a][c] * A2[b][e] for a in range(n) for b in range(n)
      for c in range(n) for e in range(n)}
C = corner_of(Mf, nm.Lz, nm.Rz)

qcorner = q[:45, 484:529]
bad = 0
for i in range(45):
    for j in range(45):
        want = int(C[i][j].numerator) * pow(int(C[i][j].denominator), p - 2, p) % p
        got = int(qcorner[i][j])
        if want != got:
            bad += 1
            if bad < 4: print('MISMATCH', i, j, want, got)
print('corner mismatches:', bad, '/2025')

# sanity of the rank helper
I45 = np.eye(45, dtype=np.int64)
print('rank(I45) =', nm.rank_mod(I45))
Z = np.zeros((10, 10), dtype=np.int64)
print('rank(0) =', nm.rank_mod(Z))
A = np.array([[1, 2], [2, 4]], dtype=np.int64)
print('rank([[1,2],[2,4]]) =', nm.rank_mod(A), '(expect 1)')

# pivots of the CORNER block itself, corner-relative (known answer: 39/39)
def R(X, Y, k=45):
    return nm.rank_mod(q[:45, 484:529][:X, Y:])
def piv(i, j):
    return R(i + 1, j) + R(i, j + 1) == R(i, j) + R(i + 1, j + 1) + 1
claim = [(1 + t, 23 + t) for t in range(21)] + [(25 + t, 2 + t) for t in range(18)]
print('corner-relative pivots:', sum(piv(i, j) for (i, j) in claim), '/39')
allp = [(i, j) for i in range(45) for j in range(45) if piv(i, j)]
print('corner pivot set size', len(allp))
