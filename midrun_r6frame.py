"""MIDRUN deliverable 1: the 439 middle-run positions of stairDataRuns at the extracted
witness, in the r6 frame (qM M).

Fixes n2d_refute.py's crashed middle section (its rk_pair enumerated 47 L-supports
instead of the 45 flag positions — aL must be ONE pair per L-index, Defs4:853-864 —
and its column-window arithmetic was off; both replaced by the exact pivot-profile
method of midrun_lib, which needs ONE 529x529 elimination to answer all blocks).

Outputs extract/out/midrun_r6frame.json:
  - hypothesis facts (rank, corner rank, hu/hv/hT),
  - per middle position (i,i), i in [45,484): A,B,C,D NE-block ranks + IsPiv verdict,
  - corner-run and singleton verdicts (validation arms vs the N2d refutation:
    old run 21/21 must hold, added run must fail 18),
  - pc profile (both primes, asserted identical).
"""
import json
import midrun_lib as L

x1, y1, x2, y2, d = L.witness()

print('hypotheses at the witness:')
h1 = sum(a * b for a, b in zip(y1, x1))
h2 = sum(a * b for a, b in zip(y2, x2))
hu = x1[0] * x2[0]
hv = y1[22] * y2[22]
hT = [(l, x1[l] * y1[22] + x2[l] * y2[22]) for l in range(1, 22)]
print('  y1.x1 =', h1, ' y2.x2 =', h2, ' hu =', hu, ' hv =', hv,
      ' hT min|.| =', min(abs(v) for _, v in hT), ' all nonzero:', all(v for _, v in hT))

Q = L.qM_pair_coords(x1, y1, x2, y2)
flag = L.flag_order('natural')

out = {'witness': 'extract/out/cert_data.json labels (exact ints)',
       'frame': 'r6: qM M = (Tm*M*Ti).submatrix flagEquiv flagEquiv, middle order = natural (row-major)',
       'method': 'rightmost-pivot profile pc of qM M; rk(X,Y) = #{r<X: pc_r>=Y}; IsPiv(i,j) <=> pc_i = j',
       'primes': [L.P1, L.P2]}

pcs = {}
for p in (L.P1, L.P2):
    pc, rank = L.rightmost_pivots(Q, p, flag)
    pcs[p] = pc
    print(f'prime {p}: rank(qM M) = {rank}')
assert pcs[L.P1] == pcs[L.P2], 'prime disagreement'
pc = pcs[L.P1]
rho = L.rho_table(pc)

out['rank_qM'] = sum(1 for c in pc if c >= 0)
out['pivot_rows'] = [r for r, c in enumerate(pc) if c >= 0]
out['nonpivot_rows'] = [r for r, c in enumerate(pc) if c < 0]
out['corner_rank_r6frame'] = L.rk_of(rho, 45, 484)   # rows<45 x cols>=484
out['sw_corner_rank'] = L.rk_of(rho, 45, 0)
print('corner rank (rows<45 x cols>=484) =', out['corner_rank_r6frame'],
      ' | SW-block rank (rows<45 x cols<45) =', out['sw_corner_rank'])

mid = []
fails = []
allpos = L.claimed_positions()
for t in allpos:
    i, j = t['pos']
    t['A'] = L.rk_of(rho, i, j)
    t['B'] = L.rk_of(rho, i + 1, j)
    t['C'] = L.rk_of(rho, i, j + 1)
    t['D'] = L.rk_of(rho, i + 1, j + 1)
    t['ispiv'] = L.ispiv(rho, i, j)
    t['pc'] = pc[i]
    if t['tag'] == 'middle':
        mid.append({'i': i, 'A': t['A'], 'B': t['B'], 'C': t['C'], 'D': t['D'],
                    'ispiv': t['ispiv'], 'pc_i': t['pc']})
        if not t['ispiv']:
            fails.append(i)
out['middle'] = mid
out['middle_fails'] = fails
out['middle_pivots'] = len(mid) - len(fails)
print(f'MIDDLE RUN: {out["middle_pivots"]}/{len(mid)} pivots; failures: {fails[:20]}',
      ('... total %d' % len(fails)) if len(fails) > 20 else '')

corner = [t for t in allpos if t['tag'] != 'middle']
for t in corner:
    i, j = t['pos']
    t['corner_ij'] = (i, j - 484)
out['corner_and_singles'] = corner
c21 = [t for t in corner if t['tag'] == 'corner21']
c18 = [t for t in corner if t['tag'] == 'corner18']
sg = [t for t in corner if t['tag'] == 'single']
print('validation vs N2d refutation: old run (1,507,21): %d/21 pivots (must be 21)' %
      sum(t['ispiv'] for t in c21))
print('  added run (25,486,18): %d/18 pivots; failing corner cols %s' %
      (sum(t['ispiv'] for t in c18), [t['corner_ij'] for t in c18 if not t['ispiv']][:20]))
print('  singles: %s' % [(t['pos'], t['ispiv']) for t in sg])

# where DO the corner rows pivot? (the graph of pc on rows 0..44)
out['pc_corner_rows'] = {r: pc[r] for r in range(45)}
print('  pc on corner rows 0..44:', [(r, pc[r]) for r in range(45)])
out['pc_mid_head'] = pc[45:60]
out['pc_mid_tail'] = pc[470:484]
json.dump(out, open('extract/out/midrun_r6frame.json', 'w'))
print('wrote extract/out/midrun_r6frame.json')
