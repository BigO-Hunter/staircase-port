"""N2c plan check:
 (1) for every IsPiv position (i, pc_i) with k = rho(i,pc_i), list the four blocks
     (i,j),(i+1,j),(i,j+1),(i+1,j+1) with targets, trivial bound, and whether
     stairNEBlocks carries a cut entry matching the target;
 (2) verify the covering claim: each position's B-block gets rank >= k+1 from one of the
     candidate minors, and its C-block gets rank >= k from one of them;
 (3) verify every candidate minor is invertible mod stairCertP.
"""
import json, re

P = 67108859

# ---- the concrete corner, mirroring Cert.lean exactly ----
d = json.load(open('extract/out/cert_data.json'))
L = d['labels']; C = d['coeffs']; h = 23
x1, y1, x2, y2 = L['x1'], L['y1'], L['x2'], L['y2']
al, be, a, b = C['al'], C['be'], C['a'], C['b']

def Lterms(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(al, (22, 0)), (be, (0, 22))]
    if i == 23: return [(1, (0, 3))]
    if i < 45: return [(1, (i - 22, i - 24))]
    return []
def Rterms(j):
    if j < 20: return [(1, (j + 1, j + 3))]
    if j == 20: return [(1, (0, 20))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(a[j - 22], (j - 22, j - 21)), (b[j - 22], (j - 21, j - 22))]
    if j == 44: return [(1, (22, 22))]
    return []
def MZ(u, v):
    return ((int(u[0] == v[0]) - x1[u[0]] * y1[v[0]])
            * (int(u[1] == v[1]) - x2[u[1]] * y2[v[1]]))
QZ = [[sum((sum(sl * MZ(ss, tt) for (sl, ss) in Lterms(i))) * cl
           for (cl, tt) in Rterms(j)) for j in range(45)] for i in range(45)]

pc = [44] + [22 + k for k in range(1, 22)] + [22, 21, 20] + [k for k in range(2, 20)] + [1, 0]
n = 45
assert sorted(pc) == list(range(n))

def rho(X, Y): return sum(1 for r in range(X) if pc[r] >= Y)

# stairNEBlocks from NEBlocks.lean
src = open('StaircasePort/NEBlocks.lean').read()
m = re.search(r'def stairNEBlocks\s*:\s*List\s*\([^)]*\)\s*:=\s*\[(.*?)\]\s*\n', src, re.S)
blk = set()
for t in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)', m.group(1)):
    blk.add((int(t[0]), int(t[1]), int(t[2]), int(t[3])))
print('stairNEBlocks entries:', len(blk))
byij = {(i, j): (r, c) for (i, j, r, c) in blk}

print('\n--- upper-bound coverage for the 4 blocks per position ---')
missing = []
for i in range(n):
    j = pc[i]; k = rho(i, j)
    cells = [('A', i, j, k), ('B', i + 1, j, k + 1), ('C', i, j + 1, k), ('D', i + 1, j + 1, k)]
    for nm, X, Y, tgt in cells:
        triv = min(X, n - Y)
        if triv == tgt: continue                      # trivial bound suffices
        e = byij.get((X - 1, Y))
        if e is None:
            missing.append((i, nm, X, Y, tgt, 'ABSENT'))
        elif e[1] != tgt:
            missing.append((i, nm, X, Y, tgt, 'cut=%d rho=%d' % e))
print('needed nontrivial upper bounds not covered by stairNEBlocks with cut==target:')
for x in missing: print('  ', x)
print('total', len(missing))

print('\n--- candidate minors (rows lo..hi, cols lo..hi) ---')
cands = {
    'M1x1':  ([0], [44]),
    'M2x2':  ([0, 1], [43, 44]),
    'M22':   (list(range(0, 22)), list(range(23, 45))),
    'M23':   (list(range(0, 23)), list(range(22, 45))),
    'M24':   (list(range(0, 24)), list(range(21, 45))),
    'M25':   (list(range(0, 25)), list(range(20, 45))),
    'M26':   (list(range(0, 26)), list(range(19, 45))),
    'M44':   (list(range(0, 44)), list(range(1, 45))),
}
def minor(R, Cc):
    return [[QZ[r][c] % P for c in Cc] for r in R]
def det_mod(S, p):
    S = [r[:] for r in S]; nn = len(S); det = 1
    for c in range(nn):
        piv = None
        for r in range(c, nn):
            if S[r][c] % p: piv = r; break
        if piv is None: return 0
        if piv != c: S[c], S[piv] = S[piv], S[c]; det = -det
        det = det * S[c][c] % p
        inv = pow(S[c][c], p - 2, p)
        for r in range(c + 1, nn):
            f = S[r][c] * inv % p
            if f: S[r] = [(S[r][k] - f * S[c][k]) % p for k in range(nn)]
    return det % p
info = {}
for nm, (R, Cc) in cands.items():
    S = minor(R, Cc)
    dt = det_mod(S, P)
    info[nm] = (len(R), R[-1], Cc[0], dt)
    print('%-6s size %2d rows ..%2d cols %2d..  det mod P = %s' % (nm, len(R), R[-1], Cc[0], dt))

print('\n--- covering: per position, which minor certifies B (size k+1) and C (size k) ---')
# minor (R,C) certifies rank(X,Y) >= |R| iff R[-1] < X and C[0] >= Y
nob = noc = 0
for i in range(n):
    j = pc[i]; k = rho(i, j)
    b = [nm for nm, (R, Cc) in cands.items() if len(R) == k + 1 and R[-1] < i + 1 and Cc[0] >= j]
    c = [nm for nm, (R, Cc) in cands.items() if len(R) == k and R[-1] < i and Cc[0] >= j + 1]
    if k + 1 == min(i + 1, n - j) and not b: b = ['trivial']
    if k == min(i, n - (j + 1)) and not c: c = ['trivial']
    if not b: nob += 1
    if not c: noc += 1
    print('i=%2d j=%2d k=%2d  B<=%s  C<=%s' % (i, j, k, b, c))
print('positions lacking B cert:', nob, ' lacking C cert:', noc)
