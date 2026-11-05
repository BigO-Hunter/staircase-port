#!/usr/bin/env python3
"""Check invertibility of the STAIRCASE witness corner in the Defs4 (r6) `cor` family.

Defs4 LtermsZ/RtermsZ at h=19 vs Cert.lean's staircase family (LtermsZStair/RtermsZStair).
Prints det mod p and exact det sign, for BOTH families, so the port knows which certificate
flag_gen's hcert needs.
"""
from fractions import Fraction

H = 19
N = H + 4        # 23
K = 2 * H + 7    # 45
P = 67108859

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


def Lz_r6(i):
    if i < H + 3:
        return [(1, (i, i))]
    if i == H + 3:
        return [(1, (H + 3, 0)), (-1, (0, H + 3))]
    if i < 2 * H + 6:
        return [(1, (i - (H + 4), i - (H + 4) + 1))]
    if i == 2 * H + 6:
        return [(1, (H + 3, 1)), (-1, (1, H + 3))]
    return []


def Rz_r6(j):
    if j < H + 2:
        return [(1, (j + 1, j))]
    if j == H + 2:
        return [(1, (0, H + 2))]
    if j < 2 * H + 6:
        return [(1, (j - (H + 3), H + 3)), (1, (H + 3, j - (H + 3)))]
    if j == 2 * H + 6:
        return [(1, (H + 3, H + 3))]
    return []


def Lz_stair(i):
    if i < 22:
        return [(1, (i, i))]
    if i == 22:
        return [(AL, (22, 0)), (BE, (0, 22))]
    if i == 23:
        return [(1, (0, 3))]
    if i < 45:
        return [(1, (i - 22, i - 24))]
    return []


def Rz_stair(j):
    if j < 20:
        return [(1, (j + 1, j + 3))]
    if j == 20:
        return [(1, (0, 20))]
    if j == 21:
        return [(1, (0, 21))]
    if j < 44:
        return [(AZL[j - 22], (j - 22, j - 21)), (BZL[j - 22], (j - 21, j - 22))]
    if j == 44:
        return [(1, (22, 22))]
    return []


def pair_mat():
    M = {}
    for a1 in range(N):
        for a2 in range(N):
            for b1 in range(N):
                for b2 in range(N):
                    v = ((1 if a1 == b1 else 0) - WX1[a1] * WY1[b1]) * \
                        ((1 if a2 == b2 else 0) - WX2[a2] * WY2[b2])
                    if v:
                        M[(a1, a2, b1, b2)] = v
    return M


def corner(Lz, Rz):
    M = pair_mat()
    C = []
    for i in range(K):
        Li = Lz(i)
        row = []
        for j in range(K):
            Rj = Rz(j)
            s = 0
            for (tc, (t1, t2)) in Rj:
                inner = 0
                for (sc, (s1, s2)) in Li:
                    inner += sc * M.get((s1, s2, t1, t2), 0)
                s += inner * tc
            row.append(s)
        C.append(row)
    return C


def det_mod(mat, p):
    n = len(mat)
    a = [[x % p for x in row] for row in mat]
    det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if a[r][c] % p), None)
        if piv is None:
            return 0
        if piv != c:
            a[c], a[piv] = a[piv], a[c]
            det = -det
        det = det * a[c][c] % p
        inv = pow(a[c][c], -1, p)
        for r in range(c + 1, n):
            f = a[r][c] * inv % p
            if f:
                for cc in range(c, n):
                    a[r][cc] = (a[r][cc] - f * a[c][cc]) % p
    return det % p


def rank_mod(mat, p):
    n = len(mat)
    a = [[x % p for x in row] for row in mat]
    rk = 0
    for c in range(n):
        piv = next((r for r in range(rk, n) if a[r][c] % p), None)
        if piv is None:
            continue
        a[rk], a[piv] = a[piv], a[rk]
        inv = pow(a[rk][c], -1, p)
        for r in range(n):
            if r != rk and a[r][c] % p:
                f = a[r][c] * inv % p
                for cc in range(c, n):
                    a[r][cc] = (a[r][cc] - f * a[rk][cc]) % p
        rk += 1
    return rk


for name, Lz, Rz in (("r6/Defs4 family", Lz_r6, Rz_r6), ("staircase family", Lz_stair, Rz_stair)):
    C = corner(Lz, Rz)
    print(f"{name}: det mod P = {det_mod(C, P)}  rank mod P = {rank_mod(C, P)}/{K}")
    flat = [x for row in C for x in row]
    print(f"   nonzero entries {sum(1 for x in flat if x)} / {len(flat)}")
