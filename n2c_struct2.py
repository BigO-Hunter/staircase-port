"""N2c structure probe (fast, modular). Computes the concrete 45x45 corner exactly as
Cert.lean does (LtermsZStair/RtermsZStair/corZStair at stairMZ), then studies the rank
profile mod two large primes."""
import json

d = json.load(open('extract/out/cert_data.json'))
P0 = d['certP']; L = d['labels']; C = d['coeffs']
h = 23
x1 = L['x1']; y1 = L['y1']; x2 = L['x2']; y2 = L['y2']
al = C['al']; be = C['be']; a = C['a']; b = C['b']

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
def MZ(u, v):
    return ((int(u[0] == v[0]) - x1[u[0]]*y1[v[0]])
            * (int(u[1] == v[1]) - x2[u[1]]*y2[v[1]]))
Q = [[sum(sl_ * MZ(ss, tt) for (sl_, ss) in Lterms(i)) * cl_ if False else
      sum((sum(sl_ * MZ(ss, tt) for (sl_, ss) in Lterms(i))) * cl_ for (cl_, tt) in Rterms(j))
      for j in range(45)] for i in range(45)]
mx = max(abs(v) for r in Q for v in r)
print('max abs entry', mx, 'digits', len(str(mx)),
      'nonzero', sum(1 for r in Q for v in r if v), 'of 2025')

PRIMES = [18446744073709551557, 18446744073709551533]
def rank_mod(rows, p):
    rows = [r[:] for r in rows]; n = len(rows); m = len(rows[0]) if n else 0; rk = 0
    for c in range(m):
        piv = None
        for i in range(rk, n):
            if rows[i][c] % p: piv = i; break
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], p-2, p)
        rows[rk] = [(v*inv) % p for v in rows[rk]]
        for i in range(n):
            if i != rk and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(rows[i][k] - f*rows[rk][k]) % p for k in range(m)]
        rk += 1
        if rk == n: break
    return rk

def profiles(p):
    # R[X][Y] = rank of rows<X cols>=Y, via incremental reuse
    Qm = [[v % p for v in r] for r in Q]
    R = [[0]*46 for _ in range(46)]
    for Y in range(45, -1, -1):
        # rows for this Y: cols Y..44 ; build prefixes
        for X in range(46):
            if X == 0: R[X][Y] = 0; continue
            R[X][Y] = rank_mod([Qm[i][Y:] for i in range(X)], p)
    return R

for p in PRIMES:
    R = profiles(p)
    print('prime', p, 'rank full', R[45][0], 'rank(45,45)=', R[45][45])
    # rk(i+1,j) - rk(i,j) for the "pivot" positions: find per-row rightmost j
    pc = []
    for i in range(45):
        best = -1
        for j in range(44, -1, -1):
            if R[i+1][j] == R[i][j] + 1: best = j; break
        pc.append(best)
    print('pc =', pc)
    pcx = [44]+[22+k for k in range(1,22)]+[22,21,20]+[k for k in range(2,20)]+[1,0]
    print('pc == extracted:', pc == pcx)
    rho_ok = all(R[X][Y] == sum(1 for r in range(X) if pc[r] >= Y)
                 for X in range(46) for Y in range(46))
    print('rho profile holds on all 46x46:', rho_ok)
    print('IsPiv at all (i,pc_i):',
          all(R[i+1][pc[i]] + R[i][pc[i]+1] == R[i][pc[i]] + R[i+1][pc[i]+1] + 1
              for i in range(45) if pc[i] >= 0))
    # also: is the matrix a projector? product with itself?
    break
