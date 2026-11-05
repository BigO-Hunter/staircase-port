#!/usr/bin/env python3
"""Focused check of the STATEMENT-SHAPE finding: the scaffold's arbitrary-M form of
stairNE_rk_le is false.  Block (1,24) has cut = 1; the two block rows (corner rows 0 and 1)
read DISJOINT sets of M-cells, so a 2x2 identity minor is realizable.

Exact rationals, no dependencies beyond stdlib.
"""
from fractions import Fraction as F
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                'jainroot', 'independent', 'deferred-readout'))
import check_stair as cs

H = 23


def lterms(i):
    if i < 22: return [(F(1), (i, i))]
    if i == 22: return [(F(3), (22, 0)), (F(5), (0, 22))]
    if i == 23: return [(F(1), (0, 3))]
    if i < 45: return [(F(1), (i - 22, i - 24))]
    return []


def rterms(j):
    if j < 20: return [(F(1), (j + 1, j + 3))]
    if j == 20: return [(F(1), (0, 20))]
    if j == 21: return [(F(1), (0, 21))]
    if j < 44: return [(F(7), (j - 22, j - 21)), (F(11), (j - 21, j - 22))]
    if j == 44: return [(F(1), (22, 22))]
    return []


def corner_entry(M, i, j):
    return sum(rt * sum(ls * M[(sc, tc)] for ls, sc in lterms(i)) for rt, tc in rterms(j))


def rank(A):
    A = [r[:] for r in A]; rows, cols = len(A), len(A[0]); rk = 0
    for c in range(cols):
        p = next((i for i in range(rk, rows) if A[i][c] != 0), None)
        if p is None: continue
        A[rk], A[p] = A[p], A[rk]
        pv = A[rk][c]; A[rk] = [x / pv for x in A[rk]]
        for i in range(rows):
            if i != rk and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f * b for a, b in zip(A[i], A[rk])]
        rk += 1
        if rk == rows: break
    return rk


# block (1,24): rows 0..1, cols 24..44 ; the pinned cut is 1
M = {}
# row 0 reads only ((0,0), .) cells; row 1 only ((1,1), .) cells.
# col 24 = a2 M[(0,0),(2,3)] + b2 M[(0,0),(3,2)] ; col 25 = a3 M[(0,0),(3,4)] + b3 M[(0,0),(4,3)]
M[((0, 0), (2, 3))] = F(1, 7)      # a2 = 7
M[((1, 1), (3, 4))] = F(1, 13)     # a3 = 13
for a in [(p, q) for p in range(H) for q in range(H)]:
    for b in [(p, q) for p in range(H) for q in range(H)]:
        M.setdefault((a, b), F(0))

block = [[corner_entry(M, r, c) for c in range(24, 45)] for r in range(2)]
r = rank(block)
print('block (1,24): block rows 0..1, cols 24..44 -> rank = %d, pinned cut = 1' % r)
print('2x2 minor on cols (24,25):', [[block[0][0], block[0][1]], [block[1][0], block[1][1]]])
print('VERDICT: arbitrary-M statement %s' % ('FALSE (rank > cut)' if r > 1 else 'not refuted here'))
