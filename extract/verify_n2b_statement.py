#!/usr/bin/env python3
"""N2b statement verification (exact Fractions, stdlib).

Three questions:
 (A) Is the CURRENT Pivot.lean statement -- `stairNE_rk_le (M : Matrix (Pr 23) (Pr 23) Q)`
     for an ARBITRARY M -- true?  Expect FALSE (the 47-term decomposition needs the
     pair-matrix form; corStairQ is merely bilinear in M).
 (B) Is the PAIR-MATRIX version -- M = (1 - x1 y1) (x)_k (1 - x2 y2) -- true at RANDOM
     labels (not just the extracted witness)?  Expect TRUE (structural certificate).
 (C) Does the 47-term decomposition
       corStairQ(pairM) i j = sum_t stairTermE t i j
     hold exactly, term by term (the identity the Lean proof must establish)?
"""
import sys, os, random
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'jainroot', 'independent', 'deferred-readout'))
import check_stair as cs

H = 23
N = 2 * H - 1


def lterms(i):
    """check_stair rows + coefficients -> list of (Fraction coeff, (a,b))."""
    if i < 22:
        return [(F(1), (i, i))]
    if i == 22:
        return [(F(3), (22, 0)), (F(5), (0, 22))]          # arbitrary nonzero coeffs
    if i == 23:
        return [(F(1), (0, 3))]
    if i < 45:
        return [(F(1), (i - 22, i - 24))]
    return []


def rterms(j):
    if j < 20:
        return [(F(1), (j + 1, j + 3))]
    if j == 20:
        return [(F(1), (0, 20))]
    if j == 21:
        return [(F(1), (0, 21))]
    if j < 44:
        return [(F(7), (j - 22, j - 21)), (F(11), (j - 21, j - 22))]
    if j == 44:
        return [(F(1), (22, 22))]
    return []


def corner(M, i, j):
    """corStairQ: sum_{t in Rterms j} t.1 * sum_{s in Lterms i} s.1 * M[s.cell][t.cell]."""
    return sum(rt * sum(ls * M[(sc, tc)] for ls, sc in lterms(i)) for rt, tc in rterms(j))


def rank(A):
    """exact rank over Q by fraction-free gaussian elimination."""
    A = [row[:] for row in A]
    rows, cols = len(A), len(A[0]) if A else 0
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
        if r == rows:
            break
    return r


def ne_rank(C, i, j):
    return rank([[C[r][c] for c in range(j, N)] for r in range(i + 1)])


# ---------- the 47-term decomposition (check_stair.structure grouping) ----------
def pairM(x1, y1, x2, y2):
    return {(a, b): ((1 if a[0] == b[0] else 0) - x1[a[0]] * y1[b[0]]) *
                     ((1 if a[1] == b[1] else 0) - x2[a[1]] * y2[b[1]])
            for a in [(p, q) for p in range(H) for q in range(H)]
            for b in [(p, q) for p in range(H) for q in range(H)]}


def term_parts(x1, y1, x2, y2, i, j):
    """the 47 term entries stairTermE t i j."""
    out = []
    L, R = lterms(i), rterms(j)
    for l in range(H):                        # l-groups: shared SECOND coord
        u = sum((ls * x1[sc[0]] for ls, sc in L if sc[1] == l), F(0))
        v = sum((rt * y1[tc[0]] for rt, tc in R if tc[1] == l), F(0))
        out.append(-u * v)
    for k in range(H):                        # k-groups: shared FIRST coord
        u = sum((ls * x2[sc[1]] for ls, sc in L if sc[0] == k), F(0))
        v = sum((rt * y2[tc[1]] for rt, tc in R if tc[0] == k), F(0))
        out.append(-u * v)
    pw = sum((ls * x1[sc[0]] * x2[sc[1]] for ls, sc in L), F(0))
    qw = sum((rt * y1[tc[0]] * y2[tc[1]] for rt, tc in R), F(0))
    out.append(pw * qw)                       # term 46: the whole term
    return out


def main():
    rng = random.Random(11)
    RC, CC = cs.design(H, 'stair')
    _, _, terms = cs.structure(H, RC, CC)
    with open(os.path.join(HERE, 'out', 'ne_cuts.json')) as f:
        import json
        blocks = json.load(f)['blocks']
    print('blocks:', len(blocks))

    # (A) arbitrary M
    Arb = {(a, b): F(rng.randrange(-50, 51), rng.randrange(1, 9))
           for a in [(p, q) for p in range(H) for q in range(H)]
           for b in [(p, q) for p in range(H) for q in range(H)]}
    CA = [[corner(Arb, i, j) for j in range(N)] for i in range(N)]
    bad = [(b['i'], b['j'], ne_rank(CA, b['i'], b['j']), b['cut']) for b in blocks
           if ne_rank(CA, b['i'], b['j']) > b['cut']]
    print('(A) arbitrary M: %d/%d blocks VIOLATE the current statement; first 3: %s'
          % (len(bad), len(blocks), bad[:3]))

    # (B) pair matrix at random labels, (C) decomposition
    for trial in range(2):
        x1 = [F(rng.randrange(-9, 10)) for _ in range(H)]
        y1 = [F(rng.randrange(-9, 10)) for _ in range(H)]
        x2 = [F(rng.randrange(-9, 10)) for _ in range(H)]
        y2 = [F(rng.randrange(-9, 10)) for _ in range(H)]
        M = pairM(x1, y1, x2, y2)
        C = [[corner(M, i, j) for j in range(N)] for i in range(N)]
        # (C) the decomposition, entrywise
        deco_bad = 0
        for i in range(N):
            for j in range(N):
                if sum(term_parts(x1, y1, x2, y2, i, j), F(0)) != C[i][j]:
                    deco_bad += 1
        viol = [(b['i'], b['j'], ne_rank(C, b['i'], b['j']), b['cut']) for b in blocks
                if ne_rank(C, b['i'], b['j']) > b['cut']]
        tight = sum(1 for b in blocks if ne_rank(C, b['i'], b['j']) == b['cut'])
        print('(B) pairM trial %d: %d/%d blocks violate; %d/%d tight (rank == cut)'
              % (trial, len(viol), len(blocks), tight, len(blocks)))
        print('(C) decomposition mismatches: %d / %d entries' % (deco_bad, N * N))

    # (D) the cut SETS are label-free certificates: re-derive and re-verify cut_bound on
    # every block against the STRUCTURAL term supports (independent of any M).
    struct_terms = cs.structure(H, RC, CC)[2]
    ok = all(cs.cut_bound(set(range(b['i'] + 1)), set(range(b['j'], N)), struct_terms) == b['cut']
             for b in blocks)
    print('(D) producer cut_bound reproduces all 689 pinned values:', ok)


if __name__ == '__main__':
    main()
