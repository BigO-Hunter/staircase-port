"""N2c generator: solve the certificate cover with CONTIGUOUS minors, verify every claim
in Python exactly as Lean will, and emit the Lean text.

Conventions mirrored from Cert.lean / Defs4:
  certChk rows cols k p  ==  (of fun i l => rows[i][l]) * (of fun l j => cols[j][l]) = 1
  so `cols` must be the TRANSPOSE of the inverse of `rows`'s matrix.
"""
import json, itertools, re

P = 67108859
d = json.load(open('extract/out/cert_data.json'))
L = d['labels']; C = d['coeffs']
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
def corZ(i, j):
    return sum((sum(sl * MZ(ss, tt) for (sl, ss) in Lterms(i))) * cl for (cl, tt) in Rterms(j))
Q = [[corZ(i, j) for j in range(45)] for i in range(45)]

pc = [44] + [22 + k for k in range(1, 22)] + [22, 21, 20] + [k for k in range(2, 20)] + [1, 0]
n = 45
assert sorted(pc) == list(range(n))
def rho(X, Y): return sum(1 for r in range(X) if pc[r] >= Y)

def det_inv_mod(S, p=P):
    """Gauss-Jordan over F_p; returns (det, inverse) or (0, None)."""
    nn = len(S)
    M = [[S[i][j] % p for j in range(nn)] + [1 if i == j else 0 for j in range(nn)] for i in range(nn)]
    det = 1
    for c in range(nn):
        piv = None
        for r in range(c, nn):
            if M[r][c] % p: piv = r; break
        if piv is None: return 0, None
        if piv != c: M[c], M[piv] = M[piv], M[c]; det = -det
        det = det * M[c][c] % p
        inv = pow(M[c][c], p - 2, p)
        M[c] = [(v * inv) % p for v in M[c]]
        for r in range(nn):
            if r != c and M[r][c] % p:
                f = M[r][c]
                M[r] = [(M[r][k] - f * M[c][k]) % p for k in range(2 * nn)]
    return det % p, [row[nn:] for row in M]

# ---- sanity check of the certChk convention against N3's landed data ----
src = open('StaircasePort/CertData.lean').read()
def getlist(name):
    m = re.search(r'def %s\s*:\s*List \(List ℕ\)\s*:=\s*\[(.*?)\]\s*\n\n' % name, src, re.S)
    if not m:
        m = re.search(r'def %s\s*:\s*List \(List ℕ\)\s*:=\s*\[(.*?)\]\n' % name, src, re.S)
    body = m.group(1)
    return [[int(v) for v in row.split(',') if v.strip()]
            for row in re.findall(r'\[([^\[\]]*)\]', body)]
CR = getlist('stairCertRows'); CC = getlist('stairCertCols')
print('N3 rows', len(CR), 'cols', len(CC))
ok = all(sum(CR[i][l] * CC[j][l] for l in range(45)) % P == (1 if i == j else 0)
         for i in range(45) for j in range(45))
print('CONVENTION CHECK: stairCertRows * stairCertCols^T = 1 mod P ?', ok)
assert ok, 'certChk convention check failed'

# ---- certificates ----
certs = {}   # (n, rlo, clo) -> dict(S=entries, T=cols-transposed-inverse)
def make(nn, rlo, clo):
    key = (nn, rlo, clo)
    if key in certs: return key
    S = [[Q[rlo + i][clo + j] % P for j in range(nn)] for i in range(nn)]
    det, inv = det_inv_mod(S)
    if det == 0: return None
    # cols[j][l] = (S^-1)[l][j]
    cols = [[inv[l][j] for l in range(nn)] for j in range(nn)]
    assert all(sum(S[i][l] * cols[j][l] for l in range(nn)) % P == (1 if i == j else 0)
               for i in range(nn) for j in range(nn))
    certs[key] = {'S': S, 'T': cols, 'det': det}
    return key

needB = [(i + 1, pc[i], rho(i, pc[i]) + 1) for i in range(n)]
needC = [(i, pc[i] + 1, rho(i, pc[i])) for i in range(n) if rho(i, pc[i]) > 0]

def cov(key, X, Y, t):
    nn, rlo, clo = key
    return nn == t and rlo + nn <= X and clo >= Y

def covers_for(key):
    out = []
    for kind, need in (('B', needB), ('C', needC)):
        for b in need:
            if cov(key, *b): out.append((kind,) + b)
    return out

# forced full-block certs
forced = [(22, 0, 23), (23, 0, 22), (24, 0, 21), (25, 0, 20), (43, 0, 2), (44, 0, 1), (1, 0, 44)]
chosen = []
for (nn, rlo, clo) in forced:
    k = make(nn, rlo, clo)
    if k is None:
        print('!! forced cert has det 0:', (nn, rlo, clo))
    else:
        chosen.append(k)
# FULL: (45,0,0) is N3's stair_data_cert - verify its det too (no new cert needed)
k45 = make(45, 0, 0)
print('full 45x45 det mod P =', certs[k45]['det'] if k45 else 0)

def allcovers(key):
    return set(covers_for(key))
covmap = {k: allcovers(k) for k in chosen}

covered = set()
for s in covmap.values(): covered |= s
missingB = [b for b in needB if ('B',) + b not in covered]
missingC = [b for b in needC if ('C',) + b not in covered]
print('\nafter forced certs: missing B', len(missingB), 'C', len(missingC))

# ---- greedy set cover for the remaining (2-family and 26-family) ----
def greedy(t, cand_shapes):
    rem = set((('B',) + b) for b in needB if b[2] == t and ('B',) + b not in covered) | \
          set((('C',) + b) for b in needC if b[2] == t and ('C',) + b not in covered)
    picked = []
    while rem:
        best = None
        for (nn, rlo, clo) in cand_shapes:
            k = make(nn, rlo, clo)
            if k is None: continue
            gained = allcovers(k) & rem
            if not gained: continue
            if best is None or len(gained) > len(best[1]): best = (k, gained)
        if best is None:
            print('  !! no cert covers', sorted(rem)[:5]); break
        picked.append(best[0]); rem -= best[1]
    return picked

shapes2 = [(2, rlo, clo) for rlo in range(0, 21) for clo in range(23, 44)]
shapes26 = [(26, rlo, clo) for rlo in range(0, 18) for clo in range(2, 20)]
for t, shapes in ((2, shapes2), (26, shapes26)):
    picked = greedy(t, shapes)
    print('family t=%d -> %d extra certs: %s' % (t, len(picked), picked))
    for k in picked:
        chosen.append(k)

# ---- final verification of the whole plan ----
allcov = set()
for k in chosen: allcov |= allcovers(k)
allcov |= {('B', 45, 0, 45)}                       # FULL (N3)
missing = [b for b in needB if ('B',) + b not in allcov] + \
          [b for b in needC if ('C',) + b not in allcov]
print('\nFINAL coverage: %d certs, missing = %s' % (len(chosen), missing))
assert not missing

# ---- upper-bound sources ----
blk = {}
ne = open('StaircasePort/NEBlocks.lean').read()
m = re.search(r'def stairNEBlocks\s*:\s*List\s*\([^)]*\)\s*:=\s*\[(.*?)\]\s*\n\ntheorem', ne, re.S)
for t4 in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)', m.group(1)):
    blk[(int(t4[0]), int(t4[1]))] = (int(t4[2]), int(t4[3]))
print('table entries', len(blk))

upper = {}    # (X,Y,target) -> ('trivial'|'table', cut)
for i in range(n):
    j = pc[i]; k = rho(i, j)
    for (X, Y, t) in ((i, j, k), (i + 1, j, k + 1), (i, j + 1, k), (i + 1, j + 1, k)):
        if (X, Y, t) in upper: continue
        if t == min(X, n - Y):
            upper[(X, Y, t)] = ('trivial', t)
        else:
            e = blk.get((X - 1, Y))
            assert e is not None and e[1] <= t, ('no upper bound', X, Y, t, e)
            upper[(X, Y, t)] = ('table', e[1])
print('upper bound sources:', len(upper),
      'table:', sum(1 for v in upper.values() if v[0] == 'table'))

json.dump({'certs': [{'n': k[0], 'rlo': k[1], 'clo': k[2], 'S': certs[k]['S'],
                      'T': certs[k]['T']} for k in chosen],
           'pc': pc,
           'upper': [{'X': X, 'Y': Y, 't': t, 'src': v[0], 'cut': v[1]}
                     for (X, Y, t), v in upper.items()],
           'covers': {('%d_%d_%d' % k): sorted(covers_for(k)) for k in chosen}},
          open('n2c_gerceva.json', 'w'), indent=1)
print('\nwrote n2c_gerceva.json')
