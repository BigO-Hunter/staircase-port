"""N2d decisive frame test.

Question: at the staircase witness labels, is the r6/Defs4 `cor` frame corner
(the ACTUAL top-right 45x45 corner of qM M) pivot-patterned like the staircase
pc permutation that isPiv_stair_lower claims?

isPiv_stair_lower concludes IsPiv (qM M) i (484 + pc i) for the corner runs.
For i < 45 and col >= 484, all four ranks are read inside the top-right 45x45
corner block of qM M, which equals cor M in the r6 frame (qM_corner).
So the claim is FALSE iff the r6-frame corner's NE rank profile differs from
the staircase pc profile.
"""
import json
from fractions import Fraction

d = json.load(open('extract/out/cert_data.json'))
L = d['labels']
n = 23
x1 = L['x1']; y1 = L['y1']; x2 = L['x2']; y2 = L['y2']
print('dot y1.x1 =', sum(a*b for a, b in zip(y1, x1)))
print('dot y2.x2 =', sum(a*b for a, b in zip(y2, x2)))

# M = (1 - x1 y1^T) kron (1 - x2 y2^T)   indexed by pairs (a,b) row, (c,e) col
def P(a, b):
    return a * n + b

A1 = [[(1 if a == c else 0) - x1[a]*y1[c] for c in range(n)] for a in range(n)]
A2 = [[(1 if a == c else 0) - x2[a]*y2[c] for c in range(n)] for a in range(n)]
M = [[0]*(n*n) for _ in range(n*n)]
for a in range(n):
    for b in range(n):
        for c in range(n):
            for e in range(n):
                M[P(a, b)][P(c, e)] = A1[a][c] * A2[b][e]

# ---- r6 frame (Defs4 Lterms/Rterms at h=19, n=23) ----
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

# ---- staircase frame (Cert.lean LtermsZStair/RtermsZStair) ----
al, be = d['coeffs']['al'], d['coeffs']['be']
aC, bC = d['coeffs']['a'], d['coeffs']['b']

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

def cor_of(Lt, Rt):
    C = [[0]*45 for _ in range(45)]
    for i in range(45):
        for j in range(45):
            s = 0
            for cs, (a, b) in Lt(i):
                for ct, (c, e) in Rt(j):
                    s += cs * ct * M[P(a, b)][P(c, e)]
            C[i][j] = s
    return C

def rank_mod(C, rows, cols, p=1000000007):
    # exact integers -> rank over F_p equals rank over Q unless p | a nonzero minor;
    # cross-check with a second prime.
    R = [[C[i][j] % p for j in cols] for i in rows]
    m = len(R); nn = len(R[0]) if m else 0
    r = 0
    for c in range(nn):
        piv = None
        for i in range(r, m):
            if R[i][c] % p:
                piv = i; break
        if piv is None: continue
        R[r], R[piv] = R[piv], R[r]
        inv = pow(R[r][c], p-2, p)
        for i in range(m):
            if i != r and R[i][c]:
                f = R[i][c] * inv % p
                R[i] = [(R[i][j] - f*R[r][j]) % p for j in range(nn)]
        r += 1
        if r == m: break
    return r

def profile(C, p):
    # rk(X,Y) = rank rows<X, cols>=Y
    R = [[0]*(46) for _ in range(46)]
    for X in range(46):
        for Y in range(46):
            R[X][Y] = rank_mod(C, range(X), range(Y, 45), p)
    return R

def ispiv(R, i, j, base=0):
    return R[i+1][j]+R[i][j+1] == R[i][j]+R[i+1][j+1]+1

pc = [44]+list(range(23, 44))+[22, 21, 20]+list(range(2, 20))+[1, 0]
print('pc =', pc, 'len', len(pc))
print('pc is perm 0..44:', sorted(pc) == list(range(45)))

runs = [(45,45,439), (1,507,21), (25,486,18)]
pos = []
for (a, b, r) in runs:
    for k in range(r):
        pos.append((a+k, b+k))
print('n positions claimed:', len(pos))

for name, Lt, Rt in (('r6-frame', Lterms, Rterms), ('staircase-frame', LtermsS, RtermsS)):
    C = cor_of(Lt, Rt)
    pa = profile(C, 1000000007); pb = profile(C, 998244353)
    assert pa == pb, name + ': primes disagree -> reduction artefact'
    rkfull = pa[45][0]
    # corner-block positions only (i<45, 484+j)
    corner = [(i, j-484) for (i, j) in pos if i < 45]
    mid = [(i, j) for (i, j) in pos if i >= 45]
    bad = [t for t in corner if not ispiv(pa, t[0], t[1])]
    print(f'{name}: rank={rkfull}  corner-claimed={len(corner)}  corner-failures={len(bad)}  sample={bad[:8]}')
    # rank profile vs pc
    same = all(pa[X][Y] == sum(1 for r in range(X) if pc[r] >= Y) for X in range(46) for Y in range(46))
    print(f'   profile matches staircase pc: {same}')
    if not same:
        diffs = [(X, Y, pa[X][Y], sum(1 for r in range(X) if pc[r] >= Y))
                 for X in range(46) for Y in range(46)
                 if pa[X][Y] != sum(1 for r in range(X) if pc[r] >= Y)]
        print('   first diffs (X,Y,actual,pc-pred):', diffs[:10], 'total', len(diffs))
