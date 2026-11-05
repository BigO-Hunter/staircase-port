#!/usr/bin/env python3
"""Validate the corner implementation against BOTH known certificates, then test the
Defs4(r6)-family corner at the staircase witness (the shape flag_gen's hcert needs)."""
import re

H, N, K, P = 19, 23, 45, 67108859

WX1 = [3, 3, 4, 3, 4, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]
WY1 = [28894092, 2511921875, -2420579261, 28894092, 62448522, 28894092, 28894092, 28894092,
       28894092, 62448522, 28894092, 28894092, 28894092, 28894092, 28894092, 28894092,
       28894092, 28894092, 28894092, 28894092, 28894092, 28894092, 28894092]
WX2 = [3, 3, 3, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 3, 4, 3, 3, 3, 3, 3, 3, 3]
WY2 = [28894092, 28894092, 2511921875, -2420579261, 28894092, 28894092, 28894092, 28894092,
       28894092, 62448522, 28894092, 28894092, 28894092, 62448522, 28894092, 62448522,
       28894092, 28894092, 28894092, 28894092, 28894092, 28894092, 28894092]
AL, BE = 53462342, 62316488
AZL = [3934340, 51045714, 51018828, 13289971, 57895068, 63395776, 6125297, 37285333, 60565243,
       25320684, 52740592, 10752404, 27291811, 48451261, 25130434, 37864025, 43555413,
       51920448, 26905599, 52424189, 38393715, 13360127]
BZL = [40788302, 59003914, 3404024, 2056127, 49465139, 63708567, 47545717, 50118998, 61885946,
       33091653, 47978747, 47145763, 44008148, 41126317, 49466425, 62891067, 12585746,
       61010376, 33687163, 49229624, 60064437, 41039367]

R6X1 = [1] * 23
R6Y1 = [-21] + [1] * 22
R6X2 = [1] + [2] * 22
R6Y2 = [-41] + [1] * 21 + [0]


def Lz_r6(i):
    if i < H + 3: return [(1, (i, i))]
    if i == H + 3: return [(1, (H + 3, 0)), (-1, (0, H + 3))]
    if i < 2 * H + 6: return [(1, (i - (H + 4), i - (H + 4) + 1))]
    if i == 2 * H + 6: return [(1, (H + 3, 1)), (-1, (1, H + 3))]
    return []


def Rz_r6(j):
    if j < H + 2: return [(1, (j + 1, j))]
    if j == H + 2: return [(1, (0, H + 2))]
    if j < 2 * H + 6: return [(1, (j - (H + 3), H + 3)), (1, (H + 3, j - (H + 3)))]
    if j == 2 * H + 6: return [(1, (H + 3, H + 3))]
    return []


def Lz_stair(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(AL, (22, 0)), (BE, (0, 22))]
    if i == 23: return [(1, (0, 3))]
    if i < 45: return [(1, (i - 22, i - 24))]
    return []


def Rz_stair(j):
    if j < 20: return [(1, (j + 1, j + 3))]
    if j == 20: return [(1, (0, 20))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(AZL[j - 22], (j - 22, j - 21)), (BZL[j - 22], (j - 21, j - 22))]
    if j == 44: return [(1, (22, 22))]
    return []


def corner(x1, y1, x2, y2, Lz, Rz):
    M = {}
    for a1 in range(N):
        for a2 in range(N):
            for b1 in range(N):
                for b2 in range(N):
                    v = ((1 if a1 == b1 else 0) - x1[a1] * y1[b1]) * \
                        ((1 if a2 == b2 else 0) - x2[a2] * y2[b2])
                    if v:
                        M[(a1, a2, b1, b2)] = v
    C = []
    for i in range(K):
        Li = Lz(i); row = []
        for j in range(K):
            s = 0
            for (tc, (t1, t2)) in Rz(j):
                s += sum(sc * M.get((s1, s2, t1, t2), 0) for (sc, (s1, s2)) in Li) * tc
            row.append(s)
        C.append(row)
    return C


def det_mod(mat, p):
    n = len(mat); a = [[x % p for x in row] for row in mat]; det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if a[r][c] % p), None)
        if piv is None: return 0
        if piv != c: a[c], a[piv] = a[piv], a[c]; det = -det
        det = det * a[c][c] % p; inv = pow(a[c][c], -1, p)
        for r in range(c + 1, n):
            f = a[r][c] * inv % p
            if f:
                for cc in range(c, n): a[r][cc] = (a[r][cc] - f * a[c][cc]) % p
    return det % p


def parse_rows(txt, name):
    i0 = txt.index(f"def {name} : List (List ℕ) := [")
    body = txt[i0:].split("\n\n")[0]
    return [[int(x) for x in r.split(',') if x.strip()] for r in re.findall(r"\[([\-0-9, ]*)\]", body)]


def cmp(C, rows, tag):
    bad = [(i, j, C[i][j] % P, rows[i][j]) for i in range(45) for j in range(min(45, len(rows[i])))
           if rows[i][j] > 0 and (C[i][j] - rows[i][j]) % P != 0]
    print(f"  {tag}: rows={len(rows)} first-row-len={len(rows[0])} mismatches={len(bad)} {bad[:2]}")


d4 = open("Definitions/Def_IntMul_Kappa_R6_Defs4.lean").read()
cd = open("StaircasePort/CertData.lean").read()

print("[1] r6 witness, r6 family  (must match Defs4 certRows; data_cert says invertible)")
C = corner(R6X1, R6Y1, R6X2, R6Y2, Lz_r6, Rz_r6)
print("   det mod P =", det_mod(C, P))
cmp(C, parse_rows(d4, "certRows"), "vs Defs4 certRows")

print("[2] stair witness, staircase family  (must match CertData stairCertRows)")
C2 = corner(WX1, WY1, WX2, WY2, Lz_stair, Rz_stair)
print("   det mod P =", det_mod(C2, P))
cmp(C2, parse_rows(cd, "stairCertRows"), "vs stairCertRows")

print("[3] stair witness, r6/Defs4 family  (the shape flag_gen hcert needs)")
C3 = corner(WX1, WY1, WX2, WY2, Lz_r6, Rz_r6)
print("   det mod P =", det_mod(C3, P))
print("[4] r6 witness, staircase family (cross-check, expect singular/incoherent)")
C4 = corner(R6X1, R6Y1, R6X2, R6Y2, Lz_stair, Rz_stair)
print("   det mod P =", det_mod(C4, P))
