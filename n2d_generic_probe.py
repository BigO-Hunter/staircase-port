"""N2d control arm + generic-labels probe.

Control arm (validates the rank machinery): the PROVED r6 theorem `data_edge_sol_aux`
says that at labels with `y·x = 1` and the r6-frame corner invertible, the corner
positions (l, 484+22+l), l = 1..21, ARE pivots. If the code below fails this at random
labels, the code is wrong.

Probe (informs the honest reformulation): for random labels with the STAIRCASE frame
corner invertible (hdet, N3's `stair_data_cert` at the witness), do the 39 staircase
positions hold as pivots of the STAIRCASE corner? If some random point fails, then
`hdet` alone does not imply the pattern: extra nonvanishing factors are needed
(SCAFFOLD.md GAP 3), i.e. the symbolic staircase-frame statement is not a
consequence of `hdet`.
"""
import json, random
from fractions import Fraction as F

d = json.load(open('extract/out/cert_data.json'))
n = 23
P1, P2 = 1000000007, 998244353
al, be = d['coeffs']['al'], d['coeffs']['be']
aC, bC = d['coeffs']['a'], d['coeffs']['b']

def Lterms(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(1, (22, 0)), (-1, (0, 22))]
    if i < 44: return [(1, (i-23, i-22))]
    return [(1, (22, 1)), (-1, (1, 22))]

def Rterms(j):
    if j < 21: return [(1, (j+1, j))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(1, (j-22, 22)), (1, (22, j-22))]
    return [(1, (22, 22))]

def LtermsS(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(al, (22, 0)), (be, (0, 22))]
    if i == 23: return [(1, (0, 3))]
    if i < 45: return [(1, (i-22, i-24))]
    return []

def RtermsS(j):
    if j < 20: return [(1, (j+1, j+3))]
    if j == 20: return [(1, (0, 20))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(aC[j-22], (j-22, j-21)), (bC[j-22], (j-21, j-22))]
    if j == 44: return [(1, (22, 22))]
    return []

def make_M(x1, y1, x2, y2):
    A1 = [[(1 if a == c else 0) - x1[a]*y1[c] for c in range(n)] for a in range(n)]
    A2 = [[(1 if a == c else 0) - x2[a]*y2[c] for c in range(n)] for a in range(n)]
    M = [[F(0)]*(n*n) for _ in range(n*n)]
    for a in range(n):
        for b in range(n):
            for c in range(n):
                for e in range(n):
                    M[a*n+b][c*n+e] = A1[a][c]*A2[b][e]
    return M

def corner_of(M, Lt, Rt):
    C = [[F(0)]*45 for _ in range(45)]
    for i in range(45):
        for j in range(45):
            s = F(0)
            for cs, (a, b) in Lt(i):
                for ct, (c, e) in Rt(j):
                    s += cs*ct*M[a*n+b][c*n+e]
            C[i][j] = s
    return C

def rank_mod(C, rows, cols, p):
    R = [[int(C[i][j].numerator * pow(C[i][j].denominator, p-2, p)) % p for j in cols] for i in rows]
    m, nn = len(R), (len(R[0]) if R else 0)
    r = 0
    for c in range(nn):
        piv = next((i for i in range(r, m) if R[i][c]), None)
        if piv is None: continue
        R[r], R[piv] = R[piv], R[r]
        inv = pow(R[r][c], p-2, p)
        for i in range(m):
            if i != r and R[i][c]:
                f = R[i][c]*inv % p
                R[i] = [(R[i][j]-f*R[r][j]) % p for j in range(nn)]
        r += 1
        if r == m: break
    return r

def profile(C):
    A = [[rank_mod(C, range(X), range(Y, 45), P1) for Y in range(46)] for X in range(46)]
    B = [[rank_mod(C, range(X), range(Y, 45), P2) for Y in range(46)] for X in range(46)]
    assert A == B, 'prime disagreement'
    return A

def piv(R, i, j):
    return R[i+1][j] + R[i][j+1] == R[i][j] + R[i+1][j+1] + 1

runs = [(1, 507, 21), (25, 486, 18)]
claimed = [(a+k, b+k-484) for (a, b, r) in runs for k in range(r)]
r6claimed = [(l, 22+l) for l in range(1, 22)]

rng = random.Random(20261105)
for trial in range(4):
    while True:
        x1 = [F(rng.randrange(1, 50)) for _ in range(n)]
        y1 = [F(rng.randrange(-5000, 5000)) for _ in range(n)]
        x2 = [F(rng.randrange(1, 50)) for _ in range(n)]
        y2 = [F(rng.randrange(-5000, 5000)) for _ in range(n)]
        y1[0] = (1 - sum(y1[i]*x1[i] for i in range(1, n))) / x1[0]
        y2[0] = (1 - sum(y2[i]*x2[i] for i in range(1, n))) / x2[0]
        ok = (x1[0]*x2[0] != 0 and y1[22]*y2[22] != 0 and
              all(x1[l]*y1[22] + x2[l]*y2[22] != 0 for l in range(1, 22)))
        if ok: break
    M = make_M(x1, y1, x2, y2)
    Cr6 = corner_of(M, Lterms, Rterms)
    Cs = corner_of(M, LtermsS, RtermsS)
    R6 = profile(Cr6); Rs = profile(Cs)
    rk6 = R6[45][0]; rks = Rs[45][0]
    ctrl = sum(1 for t in r6claimed if piv(R6, *t))
    stair = sum(1 for t in claimed if piv(Rs, *t))
    print(f'trial {trial}: r6corner rank={rk6} (control: {ctrl}/21 r6 pivots hold, must be 21) | '
          f'stair corner rank={rks}, staircase pivots {stair}/{len(claimed)}')
