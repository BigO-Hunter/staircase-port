"""Independent check that Defs4's qM at the staircase witness has its top-right 45x45
corner equal to the r6-frame `cor` (NOT the staircase frame), without using the platform
lemma qM_corner: build qM = (Tm*M*Ti).submatrix flagEquiv flagEquiv with a concrete
flagEquiv (aL on 0..44, bL on 484..528, rest arbitrary) and read the corner off it.

Fraction arithmetic (exact)."""
import json
from fractions import Fraction as F

d = json.load(open('extract/out/cert_data.json'))
L = d['labels']
n = 23
h = 19
x1, y1, x2, y2 = L['x1'], L['y1'], L['x2'], L['y2']

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

# Nm: u -> v when u.1 = h+3, u.2 < h+3, v = (u.2, h+3)
def Nm(u, v):
    (u1, u2), (v1, v2) = u, v
    return 1 if (u1 == h+3 and u2 < h+3 and v1 == u2 and v2 == h+3) else 0
Tm = lambda u, v: (1 if u == v else 0) - Nm(u, v)   # T = 1 - Nm
Ti = lambda u, v: (1 if u == v else 0) + Nm(u, v)   # T^-1 = 1 + Nm

pairs = [(a, b) for a in range(n) for b in range(n)]

# aL / bL (Defs4:853-864 at h=19)
def aL(i):
    if i < h+3: return (i, i)
    if i == h+3: return (h+3, 0)
    if i < 2*h+6: return (i-(h+4), i-(h+4)+1)
    return (h+3, 1)

def bL(j):
    if j < h+2: return (j+1, j)
    if j == h+2: return (0, h+2)
    if j < 2*h+6: return (j-(h+3), h+3)
    return (h+3, h+3)

print('aL injective:', len({aL(i) for i in range(45)}) == 45,
      ' bL injective:', len({bL(j) for j in range(45)}) == 45,
      ' aL disjoint bL:', not ({aL(i) for i in range(45)} & {bL(j) for j in range(45)}))

top = [aL(i) for i in range(45)]
bot = [bL(j) for j in range(45)]
mid = [p for p in pairs if p not in set(top) and p not in set(bot)]
flag = top + mid + bot          # concrete flagEquiv: position -> pair
assert len(flag) == 529 and len(set(flag)) == 529
print('|mid| =', len(mid))

# qM = (Tm * M * Ti) submatrix flagEquiv flagEquiv
# (Tm*M*Ti)[u][w] = sum_v sum_z Tm[u][v] M[v][z] Ti[z][w]; Nm is sparse so do it directly.
def mtimes(u, w):
    # rows of Tm: Tm[u][v] nonzero only v=u (1) and v where Nm(u,v)=1 (-1)
    vs = {u: F(1)}
    v2 = (u[1], h+3)
    if u[0] == h+3 and u[1] < h+3:
        vs[v2] = vs.get(v2, 0) - 1
    # (M * Ti)[v][w] = sum_z M[v][z] Ti[z][w]; Ti[z][w] nonzero at z=w (1), z with Nm(z,w)=1
    tot = F(0)
    for v, cf in vs.items():
        if cf == 0: continue
        # Ti[z][w]: z=w -> 1; Nm(z,w)=1 -> +1  (z.1=h+3, z.2<h+3, w=(z.2,h+3))
        acc = F(M[P(*v)][P(*w)])
        if w[1] == h+3 and w[0] < h+3:  # z = (h+3, w[0]) with Nm[z][w] = 1
            acc += F(M[P(*v)][P(h+3, w[0])])
        tot += cf * acc
    return tot

corner = [[mtimes(flag[i], flag[484+j]) for j in range(45)] for i in range(45)]

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

def cor(i, j):
    s = F(0)
    for cs, (a, b) in Lterms(i):
        for ct, (c, e) in Rterms(j):
            s += cs*ct*M[P(a, b)][P(c, e)]
    return s

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

def corS(i, j):
    s = F(0)
    for cs, (a, b) in LtermsS(i):
        for ct, (c, e) in RtermsS(j):
            s += cs*ct*M[P(a, b)][P(c, e)]
    return s

eq_r6 = all(corner[i][j] == cor(i, j) for i in range(45) for j in range(45))
diff_stair = [(i, j) for i in range(45) for j in range(45) if corner[i][j] != corS(i, j)]
print('qM corner == r6-frame cor (all 2025 entries):', eq_r6)
print('qM corner == staircase-frame corStairQ: ', len(diff_stair) == 0,
      ' differing entries:', len(diff_stair), ' first:', diff_stair[:6])
i0, j0 = diff_stair[0]
print(f'example: qM-corner[{i0}][{j0}] = {corner[i0][j0]}  vs  corStairQ = {corS(i0,j0)}')
print(f'cor_r6[{i0}][{j0}] = {cor(i0,j0)}')
