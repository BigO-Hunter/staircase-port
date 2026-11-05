"""N2c structure probe: compute the concrete 45x45 corner (mirroring Cert.lean
LtermsZStair/RtermsZStair/corZStair at stairMZ), verify the pc rank profile, and
report the structural facts the Lean proof could exploit (support pattern,
per-block rank increments, candidate factorization)."""
import json
from fractions import Fraction as F

d = json.load(open('extract/out/cert_data.json'))
P = d['certP']
L = d['labels']; C = d['coeffs']
h = 23
x1 = L['x1']; y1 = L['y1']; x2 = L['x2']; y2 = L['y2']
al = C['al']; be = C['be']; a = C['a']; b = C['b']
RC = d['RC']; CC = d['CC']

M = [[0]*h for _ in range(h)]
q1 = [[int(i == k) - x1[i]*y1[k] for k in range(h)] for i in range(h)]
q2 = [[int(i == k) - x2[i]*y2[k] for k in range(h)] for i in range(h)]
for i in range(h):
    for j in range(h):
        s = 0
        for k in range(h):
            if q1[i][k]:
                for l in range(h):
                    if q2[l][j]:
                        s += q1[i][k]*M[k][l]*q2[l][j]
        M[i][j] = s
# M[i][j] = (q1 M q2^T)[i][j]
M = [[sum(q1[i][k]*0 for k in range(h))]*h for _ in range(h)]
M = [[0]*h for _ in range(h)]
for i in range(h):
    for j in range(h):
        M[i][j] = sum(q1[i][k]*q2[j][l]*0 for k in range(h) for l in range(h))
# zero base matrix, so the product is zero; instead rebuild properly:
M = [[0]*h for _ in range(h)]
# the pair matrix entry (k,l) is delta_kl; the corner uses M[s.2][t.2] where s.2=(p,q) etc.
# follow Cert.lean exactly:
def Lterms(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(al, (22, 0)), (be, (0, 22))]
    if i == 23: return [(1, (0, 3))]
    if i < 45: return [(1, (i-22, i-24))]
    return []
def Rterms(j):
    if j < 20: return [(1, (j+1, j+3))]
    if j == 20: return [(1, (0, 20))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(a[j-22], (j-22, j-21)), (b[j-22], (j-21, j-22))]
    if j == 44: return [(1, (22, 22))]
    return []
# pair matrix MZ over Z: (1 - vecMulVec x1 y1) kron (1 - vecMulVec x2 y2)
# kron index: 23*a+b -> row a (first factor), etc. label s.2 = (u,v) in Pr 23 = Fin 23 x Fin 23
def vmv(x, y, r, c): return x[r]*y[c]
def MZ(u, v):
    # u, v : Pr 23 = Fin 23 x Fin 23 ; kron((1-x1y1),(1-x2y2))
    return (int(u[0] == v[0]) - x1[u[0]]*y1[v[0]]) * (int(u[1] == v[1]) - x2[u[1]]*y2[v[1]])
def corZ(i, j):
    s = 0
    for (cl, tt) in Rterms(j):
        inner = sum(sl * MZ(ss, tt) for (sl, ss) in Lterms(i))
        s += inner * cl
    return s

Q = [[corZ(i, j) for j in range(45)] for i in range(45)]
print('max abs entry', max(abs(v) for r in Q for v in r), 'digits',
      len(str(max(abs(v) for r in Q for v in r))))
print('nonzero entries', sum(1 for r in Q for v in r if v), 'of', 45*45)

def rank(mat):
    mat = [row[:] for row in mat]
    if not mat: return 0
    rows = len(mat); cols = len(mat[0]) if rows else 0
    r = 0
    for c in range(cols):
        p = None
        for i in range(r, rows):
            if mat[i][c]: p = i; break
        if p is None: continue
        mat[r], mat[p] = mat[p], mat[r]
        inv = F(1, 1)/F(mat[r][c])
        mat[r] = [F(v)*inv for v in mat[r]]
        for i in range(rows):
            if i != r and mat[i][c]:
                f = F(mat[i][c])
                mat[i] = [F(mat[i][k]) - f*mat[r][k] for k in range(cols)]
        r += 1
        if r == rows: break
    return r

def rk(X, Y):
    sub = [[F(Q[i][j]) for j in range(Y, 45)] for i in range(X)]
    if not sub or not sub[0]: return 0
    return rank(sub)

pc = []
for i in range(45):
    found = -1
    for j in range(44, -1, -1):
        if rk(i+1, j) > rk(i, j+1) + rk(i, j) - rk(i+1, j+1):
            pass
    # rightmost pivot: largest j with rk(i+1,j) = rk(i,j)+1
    for j in range(44, -1, -1):
        if rk(i+1, j) == rk(i, j) + 1:
            found = j; break
    pc.append(found)
print('pc computed =', pc)
print('pc extracted =', [44]+[22+k for k in range(1,22)]+[22,21,20]+[k for k in range(2,20)]+[1,0])
rho_ok = all(rk(X, Y) == sum(1 for r in range(X) if pc[r] >= Y) for X in range(46) for Y in range(46))
print('rho profile rk(X,Y)=#{r<X: pc_r>=Y} on all 46x46 pairs:', rho_ok)
# IsPiv check directly
def ispiv(i, j): return rk(i+1, j)+rk(i, j+1) == rk(i, j)+rk(i+1, j+1)+1
bad = [(i, pc[i]) for i in range(45) if pc[i] >= 0 and not ispiv(i, pc[i])]
print('non-IsPiv among (i,pc_i):', bad)
# support pattern per row
print('row support (min/max col, count):')
for i in range(45):
    nz = [j for j in range(45) if Q[i][j]]
    print(i, 'pc', pc[i], 'nz', len(nz), 'cols', (min(nz), max(nz)) if nz else None)
