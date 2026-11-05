#!/usr/bin/env python3
"""N7 pre-rewire measurement: staircase-frame aux/side corner patterns.

corStairQ M i j = sum over s in LtermsStair i, t in RtermsStair j of
                  s.coeff * M s.coord t.coord * t.coeff   (exact Fraction)

Checks at generic labels (y.x = 1):
  aux1: M1 = 1 x (1 - x y^T):  corStairQ M1 b (22+g) = 0 for b<g<23;
        diag b=g != 0  (23 diagonals, b = 0..22)
  aux2: M2 = (1 - x y^T) x 1:  same pattern
  side1 B-block rows: (TeStair*Cx x) b a  == sum over LtermsStair b, s.coord.1=a of s.coeff*x[s.coord.2]
  side1 A-block cols: (Ry y*TeStair') a (484+g) == sum over RtermsStair (22+g), t.coord.1=a of t.coeff*y[t.coord.2]
  side2 analogues with Cx2/Ry2 (x/y roles via second coordinate)
Reports the exact diag values (as symbolic label products) so the Lean label-fact
requirements can be read off.
"""
from fractions import Fraction as F
import itertools, random, json, sys

N = 23

# ---- staircase families (Cert.lean LtermsZStair/RtermsZStair) -----------------
def LtermsStair(i):
    if i < 22:  return [(F(1), (i, i))]
    if i == 22: return [(F(1717), (22, 0)), (F(-2054), (0, 22))]   # al, be (placeholder; overwritten below)
    if i == 23: return [(F(1), (0, 3))]
    if i < 45:  return [(F(1), (i - 22, i - 24))]
    return []

def RtermsStair(j):
    if j < 20:  return [(F(1), (j + 1, j + 3))]
    if j == 20: return [(F(1), (0, 20))]
    if j == 21: return [(F(1), (0, 21))]
    if j < 44:  return [(A[j - 22], (j - 22, j - 21)), (B[j - 22], (j - 21, j - 22))]
    if j == 44: return [(F(1), (22, 22))]
    return []

# real coefficients from CertData (stairAlZ/stairBeZ/stairAZL/stairBZL)
import re
def get_z(name):
    txt = open("StaircasePort/CertData.lean").read()
    m = re.search(name + r"\s*:?\s*(List\(Z\)|List Int|Z|Int)?\s*:=\s*\[(.*?)\]", txt, re.S)
    if m:
        vals = [int(x) for x in re.findall(r"-?\d+", m.group(2))]
        return vals
    return None

txt = open("StaircasePort/CertData.lean").read()
def find_scalar(name):
    m = re.search(re.escape(name) + r"[^\n]*?(-?\d+)\s*$", txt, re.M)
    return int(m.group(1)) if m else 0
def find_list(name):
    m = re.search(re.escape(name) + r"[\s\S]*?\[([^\]]*)\]", txt)
    return [int(x) for x in re.findall(r"-?\d+", m.group(1))] if m else None

al_v = find_scalar("stairAlZ")
be_v = find_scalar("stairBeZ")
A = find_list("stairAZL")[:22]
B = find_list("stairBZL")[:22]
sys.stderr.write(f"al={al_v} be={be_v} |A|={len(A)} |B|={len(B)}\n")
assert len(A) == 22 and len(B) == 22

def LtermsStair(i):
    if i < 22:  return [(F(1), (i, i))]
    if i == 22: return [(F(al_v), (22, 0)), (F(be_v), (0, 22))]
    if i == 23: return [(F(1), (0, 3))]
    if i < 45:  return [(F(1), (i - 22, i - 24))]
    return []

# ---- r6 families (Defs4 Lterms/Rterms) for control ---------------------------
def Lterms(i, h=19):
    n = h + 4
    if i < h + 3: return [(F(1), (i, i))]
    if i == h + 3: return [(F(1), (h + 3, 0)), (F(-1), (0, h + 3))]
    if i < 2 * h + 6: return [(F(1), (i - n, i - n + 1))]
    if i == 2 * h + 6: return [(F(1), (h + 3, 1)), (F(-1), (1, h + 3))]
    return []

def Rterms(j, h=19):
    n = h + 4
    if j < h + 2: return [(F(1), (j + 1, j))]
    if j == h + 2: return [(F(1), (0, h + 2))]
    if j < 2 * h + 6: return [(F(1), (j - (h + 3), h + 3)), (F(1), (h + 3, j - (h + 3)))]
    if j == 2 * h + 6: return [(F(1), (h + 3, h + 3))]
    return []

def cor_fun(L, R, M, i, j):
    tot = F(0)
    for tc, t in R(j):
        row = F(0)
        for sc, s in L(i):
            row += sc * M(s[0], s[1], t[0], t[1])
        tot += row * tc
    return tot

# ---- matrices ----------------------------------------------------------------
def kron(A, B):
    M = {}
    for (a, b) in itertools.product(range(N), repeat=2):
        for (c, d) in itertools.product(range(N), repeat=2):
            M[(a, b, c, d)] = A(a, c) * B(b, d)
    return M

def entry(M, u, v, w, z):
    return M.get((u, v, w, z), F(0))

def one(a, c): return F(1) if a == c else F(0)
def mvv(x, y, b, d): return (F(1) if b == d else F(0)) - x[b] * y[d]

def corS(M, i, j):
    tot = F(0)
    for tc, t in RtermsStair(j):
        row = F(0)
        for sc, s in LtermsStair(i):
            row += sc * entry(M, s[0], s[1], t[0], t[1])
        tot += row * tc
    return tot

def cor6(M, i, j):
    tot = F(0)
    for tc, t in Rterms(j):
        row = F(0)
        for sc, s in Lterms(i):
            row += sc * entry(M, s[0], s[1], t[0], t[1])
        tot += row * tc
    return tot

def check(M, name, cf):
    upper_ok, diags = True, []
    for b in range(23):
        for g in range(23):
            v = cf(M, b, 22 + g)
            if b < g and v != 0:
                upper_ok = False
            if b == g:
                diags.append(v)
    print(f"{name}: upper_zero_all={upper_ok}")
    for b, v in enumerate(diags):
        print(f"  diag[{b}] = {v}")
    return upper_ok, diags

# generic labels
random.seed(7)
while True:
    x = [F(random.randint(-9, 9)) for _ in range(N)]
    y = [F(random.randint(-9, 9)) for _ in range(N)]
    if all(v != 0 for v in x) and all(v != 0 for v in y):
        break
dot = sum(y[i] * x[i] for i in range(N))
y = [v / dot for v in y]
assert sum(y[i] * x[i] for i in range(N)) == 1
print(f"labels x={x}\n        y={y}")

M1 = kron(one, lambda b, d: mvv(x, y, b, d))   # 1 x (1 - xy^T)
M2 = kron(lambda b, d: mvv(x, y, b, d), one)   # (1 - xy^T) x 1

print("== STAIRCASE frame ==")
check(M1, "aux1 (1 x (1-xy^T))", corS)
check(M2, "aux2 ((1-xy^T) x 1)", corS)
print("== R6 frame control ==")
check(M1, "aux1", cor6)
check(M2, "aux2", cor6)

# ---- side blocks --------------------------------------------------------------
# side_B: (TeStair * Cx) b a = sum_{s in LtermsStair b, s.1coord = a} s.coeff * x[s.2coord]
def sideB_Stair(b, a, C):  # C : (u1,u2) -> a -> value, here Cx x / Cx2 x
    tot = F(0)
    for sc, s in LtermsStair(b):
        tot += sc * C(s[0], s[1], a)
    return tot

def Cx(x, u1, u2, a):  return x[u2] if u1 == a else F(0)
def Cx2(x, u1, u2, a): return x[u1] if u2 == a else F(0)

def sideA_Stair(a, g, R):  # R : a -> (v1,v2) -> value
    tot = F(0)
    for tc, t in RtermsStair(22 + g):
        tot += tc * R(a, t[0], t[1])
    return tot

def Ry(y, a, v1, v2):  return y[v2] if a == v1 else F(0)
def Ry2(y, a, v1, v2): return y[v1] if a == v2 else F(0)

for nm, C, R in [("side1 (A x xy^T)", lambda u1, u2, a: Cx(x, u1, u2, a), lambda a, v1, v2: Ry(y, a, v1, v2)),
                 ("side2 (xy^T x A)", lambda u1, u2, a: Cx2(x, u1, u2, a), lambda a, v1, v2: Ry2(y, a, v1, v2))]:
    print(f"== {nm}: B-block (TeStair*C) upper/diag ==")
    bup, bdiag = True, []
    for i in range(23):
        for j in range(23):
            v = sideB_Stair(i, j, C)
            if i < j and v != 0: bup = False
            if i == j: bdiag.append(v)
    print(f"  upper_zero={bup}; diags={bdiag}")
    print(f"  A-block (R*TeStair') upper/diag at col 484+g:")
    aup, adiag = True, []
    for i in range(23):
        for g in range(23):
            v = sideA_Stair(i, g, R)
            if i < g and v != 0: aup = False
            if i == g: adiag.append(v)
    print(f"  upper_zero={aup}; diags={adiag}")
    # r6 control
    print(f"  [r6 control] B-block:")
    def sideB6(b, a):
        tot = F(0)
        for sc, s in Lterms(b):
            tot += sc * C(s[0], s[1], a)
        return tot
    bup6 = all(sideB6(i, j) == 0 for i in range(23) for j in range(23) if i < j)
    bdiag6 = [sideB6(i, i) for i in range(23)]
    def sideA6(a, g):
        tot = F(0)
        for tc, t in Rterms(22 + g):
            tot += tc * R(a, t[0], t[1])
        return tot
    aup6 = all(sideA6(i, g) == 0 for i in range(23) for g in range(23) if i < g)
    adiag6 = [sideA6(i, i) for i in range(23)]
    print(f"  upper_zero={bup6}; diags={bdiag6}")
    print(f"  [r6] A-block upper_zero={aup6}; diags={adiag6}")
