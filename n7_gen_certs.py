"""N7 cert generator: the 4 missing M2-shape certificates (t = 12,13,14,15) plus the
t->cert index map for all 18. Emits Lean defs + theorems in the N2c certChk convention."""
import json, re

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

def det_inv_mod(S, p=P):
    nn = len(S)
    M = [[S[i][j] % p for j in range(nn)] + [1 if i == j else 0 for j in range(nn)] for i in range(nn)]
    det = 1
    for c in range(nn):
        pivr = None
        for r in range(c, nn):
            if M[r][c] % p: pivr = r; break
        if pivr is None: return 0, None
        if pivr != c: M[c], M[pivr] = M[pivr], M[c]; det = -det
        det = det * M[c][c] % p
        inv = pow(M[c][c], p - 2, p)
        M[c] = [(v * inv) % p for v in M[c]]
        for r in range(nn):
            if r != c and M[r][c] % p:
                f = M[r][c]
                M[r] = [(M[r][k] - f * M[c][k]) % p for k in range(2 * nn)]
    return det % p, [row[nn:] for row in M]

out = []
idxmap = {}
for t in range(18):
    rl = list(range(25)) + [25 + t]
    cl = list(range(2 + t, 28 + t))
    S = [[Q[r][c] % P for c in cl] for r in rl]
    det, inv = det_inv_mod(S)
    assert det != 0, (t, 'singular')
    cols = [[inv[l][j] for l in range(26)] for j in range(26)]
    # verify convention: S . T^T = I  i.e. sum_l S[i][l]*cols[j][l] = delta_ij
    for i in range(26):
        for j in range(26):
            s = sum(S[i][l] * cols[j][l] for l in range(26)) % P
            assert s == (1 if i == j else 0), (t, i, j)
    idxmap[t] = det
    out.append((t, rl, cl, S, cols, det))

print("all 18 M2 certs verified (det != 0 mod P, S*T^T = I)")
# emit Lean for the 4 missing (t=12..15); name them n7Chk<t>
lines = []
for t, rl, cl, S, cols, det in out:
    if t not in (12, 13, 14, 15):
        continue
    R = '[' + ', '.join(str(v) for v in rl) + ']'
    Cl = '[' + ', '.join(str(v) for v in cl) + ']'
    Ss = '[\n' + ',\n'.join('   [' + ', '.join(str(v) for v in row) + ']' for row in S) + ']'
    Ts = '[\n' + ',\n'.join('   [' + ', '.join(str(v) for v in row) + ']' for row in cols) + ']'
    lines.append(f"""/-- N7 M2 minor certificate, t = {t}: rows {R}, cols {Cl} (det mod P = {det}). -/
def n7R{t} : List ℕ := {R}
def n7C{t} : List ℕ := {Cl}
def n7S{t} : List (List ℕ) := {Ss}
def n7T{t} : List (List ℕ) := {Ts}

theorem n7Chk{t} : certChk n7S{t} n7T{t} 26 stairCertP = true := by decide +kernel

theorem n7Ent{t} : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n7R{t}.getD i.val 0) (n7C{t}.getD j.val 0) % (stairCertP : ℤ) =
      (((n7S{t}.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel
""")
open('n7_certs_block.lean', 'w').write('\n'.join(lines))
print("wrote n7_certs_block.lean for t=12..15")
print("t->det map:", idxmap)
