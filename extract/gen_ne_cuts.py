#!/usr/bin/env python3
"""N2b Phase 2: append per-block cut SETS + term supports to StaircasePort/NEBlocks.lean.

Input:  extract/out/ne_cuts.json (from extract_cuts.py; cross-checked 689/689)
Output: StaircasePort/NEBlocks.lean -- the existing content kept BYTE-IDENTICAL up to the
        closing `end StaircasePort.Stair`; the new data appended before it.

New data (raw Nat lists; Finsets are built from them in Pivot.lean):
  structure StairNEBlock  (i, j, rho, cut, R0, C0, T0)
  stairNEBlocksX : List StairNEBlock          689 entries, zip-aligned with stairNEBlocks
  stairNESr / stairNESc : List (List Nat)     47 entries (structure()'s term supports)
Bulk pins (Nat/List data only -- decide-safe; NO Rat arithmetic, per the N4 landmine):
  stairNEBlocksX_map  : the (i,j,rho,cut) projection reproduces the existing value pins
  stairNE_cuts_card   : per block |R0|+|C0|+|T0| = cut, indices in range, nodup, elements
                        in range (the Finset-cardinality preconditions)
  stairNE_cuts_cover  : per block, every term t outside T0 is row- or col-covered -- exactly
                        cut_bound's certificate loop (check_stair.py:87-89)
"""
import json, os

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..', 'StaircasePort', 'NEBlocks.lean')


def fmt_l(l):
    return '[' + ', '.join(map(str, l)) + ']'


def fmt_ll(ll):
    return '[' + ', '.join(fmt_l(l) for l in ll) + ']'


def main():
    with open(os.path.join(HERE, 'out', 'ne_cuts.json')) as f:
        data = json.load(f)
    blocks, terms = data['blocks'], data['terms']
    assert len(blocks) == 689 and len(terms) == 47

    with open(LEAN) as f:
        old = f.read()
    marker = '\nend StaircasePort.Stair'
    idx = old.rindex(marker)
    head = old[:idx]

    for b in blocks:
        assert '(%d, %d, %d, %d)' % (b['i'], b['j'], b['rho'], b['cut']) in head, b
        for key in ('R0', 'C0', 'T0'):
            assert b[key] == sorted(set(b[key])), (b['i'], b['j'], key)
        assert len(b['R0']) + len(b['C0']) + len(b['T0']) == b['cut']
        assert all(0 <= x < 45 for x in b['R0'] + b['C0'])
        assert all(0 <= x < 47 for x in b['T0'])
    for sr, sc in terms:
        assert sr == sorted(set(sr)) and sc == sorted(set(sc))

    a = []
    A = a.append
    A('')
    A('/-! ## N2b cut SETS (generated 2026-11-05 by extract/gen_ne_cuts.py from')
    A('extract/out/ne_cuts.json; the extraction reproduces all 689 pinned cut VALUES above and')
    A('agrees with the producer check_stair.cut_bound 689/689). Raw Nat lists; the Lean Finsets')
    A('are built from them by `Finset.univ.filter` in Pivot.lean. -/')
    A('')
    A('/-- One nontrivial NE block of the 45x45 staircase corner, with its min vertex cut')
    A('`(R0, C0, T0)` of the rows-terms-cols graph (`R0` rows, `C0` cols, `T0` whole terms). -/')
    A('structure StairNEBlock where')
    A('  i : ℕ')
    A('  j : ℕ')
    A('  rho : ℕ')
    A('  cut : ℕ')
    A('  R0 : List ℕ')
    A('  C0 : List ℕ')
    A('  T0 : List ℕ')
    A('deriving DecidableEq, Repr')
    A('')
    A('/-- The 689 nontrivial NE blocks with their cut sets, zip-aligned with `stairNEBlocks`. -/')
    A('def stairNEBlocksX : List StairNEBlock := [')
    body = []
    for k, b in enumerate(blocks):
        sep = ',' if k + 1 < len(blocks) else ''
        body.append('  { i := %d, j := %d, rho := %d, cut := %d, R0 := %s, C0 := %s, T0 := %s }%s'
                    % (b['i'], b['j'], b['rho'], b['cut'], fmt_l(b['R0']), fmt_l(b['C0']),
                       fmt_l(b['T0']), sep))
    a.extend(body)
    A('  ]')
    A('')
    A('/-- Term row supports `sr_t` (check_stair.structure :49-53): the row-group indices of the')
    A('45x45 corner whose family cells reference term `t`\'s shared coordinate. -/')
    A('def stairNESr : List (List ℕ) :=')
    A(fmt_ll([t[0] for t in terms]))
    A('')
    A('/-- Term col supports `sc_t` (ditto, column groups). -/')
    A('def stairNESc : List (List ℕ) :=')
    A(fmt_ll([t[1] for t in terms]))
    A('')
    A('theorem stairNESr_length : stairNESr.length = 47 := rfl')
    A('')
    A('theorem stairNESc_length : stairNESc.length = 47 := rfl')
    A('')
    A('/-- The value-pin projection of the regenerated block list: the cut sets were extracted')
    A('for exactly the blocks (and values) pinned in `stairNEBlocks`. -/')
    A('theorem stairNEBlocksX_map :')
    A('    stairNEBlocksX.map (fun b => (b.i, b.j, b.rho, b.cut)) = stairNEBlocks := by rfl')
    A('')
    A('/-- Per-block cardinality/range side condition of the cut data (the Finset-cardinality')
    A('preconditions: nodup raw lists, elements in range, |R0|+|C0|+|T0| = cut). -/')
    A('def stairNEcardOK (b : StairNEBlock) : Bool :=')
    A('  decide (b.R0.length + b.C0.length + b.T0.length = b.cut) &&')
    A('  decide (b.i < 45) && decide (b.j < 45) &&')
    A('  b.R0.all (fun r => r < 45) && b.C0.all (fun c => c < 45) &&')
    A('  b.T0.all (fun t => t < 47) &&')
    A('  decide b.R0.Nodup && decide b.C0.Nodup && decide b.T0.Nodup')
    A('')
    A('set_option maxRecDepth 20000 in')
    A('set_option maxHeartbeats 0 in')
    A('theorem stairNE_cuts_card : stairNEBlocksX.all stairNEcardOK = true := by decide')
    A('')
    A('/-- Per-block cut-certificate condition (check_stair.py:87-89, reordered to iterate the')
    A('small support lists): every term outside `T0` has all of its row support inside the')
    A('block rows (`r <= i`) within `R0`, or all of its col support inside the block cols')
    A('(`j <= c`) within `C0`. -/')
    A('def stairNEcoverOK (b : StairNEBlock) : Bool :=')
    A('  (List.range 47).all fun t =>')
    A('    decide (t ∈ b.T0) ||')
    A('    (stairNESr.getD t []).all (fun r => !decide (r ≤ b.i) || decide (r ∈ b.R0)) ||')
    A('    (stairNESc.getD t []).all (fun c => !decide (b.j ≤ c) || decide (c ∈ b.C0))')
    A('')
    A('set_option maxRecDepth 20000 in')
    A('set_option maxHeartbeats 0 in')
    A('theorem stairNE_cuts_cover : stairNEBlocksX.all stairNEcoverOK = true := by decide')
    A('')

    out = head + '\n'.join(a) + marker + '\n'
    with open(LEAN, 'w') as f:
        f.write(out)
    print('regenerated NEBlocks.lean: %d bytes, %d lines, %d blocks'
          % (len(out), out.count('\n'), len(blocks)))


if __name__ == '__main__':
    main()
