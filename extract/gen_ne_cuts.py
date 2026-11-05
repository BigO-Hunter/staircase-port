#!/usr/bin/env python3
"""N2b Phase 2: regenerate StaircasePort/NEBlocks.lean with per-block cut SETS + term
supports alongside the existing (byte-identical) cut VALUE pins.

Input:  extract/out/ne_cuts.json (from extract_cuts.py; cross-checked 689/689)
Output: StaircasePort/NEBlocks.lean  (old content preserved verbatim; new section appended
        before the closing `end StaircasePort.Stair`)

New pinned data (all raw Nat lists; Finsets are built from them by filter in Lean):
  stairNECutR0/C0/T0 : List (List Nat), 689 entries each, zip-aligned with stairNEBlocks
  stairNESr/Sc       : List (List Nat), 47 entries (structure()'s term supports)
Bulk decide pins (Nat/List data only -- no Rat arithmetic, per N4 landmine notes):
  stairNE_cuts_len   : lengths = 689
  stairNE_cuts_card  : per block |R0|+|C0|+|T0| = the pinned cut value (column 4)
  stairNE_cuts_cover : per block, every term t not in T0 is row-covered (sr_t within
                       rows<=i is inside R0) or col-covered (sc_t within cols>=j inside C0)
                       -- exactly cut_bound's certificate loop (check_stair.py:87-89)
  stairNE_cuts_bound : per block i < 45 and j < 45
The sr/sc <-> LtermsStair/RtermsStair coherence pin lives in Pivot.lean (needs Cert.lean).
"""
import json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..', 'StaircasePort', 'NEBlocks.lean')

def fmt_ll(ll):
    return '[' + ', '.join('[' + ', '.join(map(str, l)) + ']' for l in ll) + ']'

def main():
    with open(os.path.join(HERE, 'out', 'ne_cuts.json')) as f:
        data = json.load(f)
    blocks = data['blocks']
    terms = data['terms']
    assert len(blocks) == 689 and len(terms) == 47

    with open(LEAN) as f:
        old = f.read()

    # preserve everything byte-identical up to the closing `end`
    marker = '\nend StaircasePort.Stair'
    assert old.endswith(marker + '\n') or old.rstrip().endswith('end StaircasePort.Stair')
    idx = old.rindex(marker)
    head = old[:idx]

    # sanity: the pinned values in head must match the JSON (i,j,rho,cut)
    for b in blocks:
        needle = '(%d, %d, %d, %d)' % (b['i'], b['j'], b['rho'], b['cut'])
        assert needle in head, 'pinned tuple missing: ' + needle
    # duplicate-free sorted sets (card = length)
    for b in blocks:
        for key in ('R0', 'C0', 'T0'):
            l = b[key]
            assert l == sorted(set(l)), (b['i'], b['j'], key)
            assert len(l) + 0 == len(l)
        assert len(b['R0']) + len(b['C0']) + len(b['T0']) == b['cut']
    for sr, sc in terms:
        assert sr == sorted(set(sr)) and sc == sorted(set(sc))

    R0 = [b['R0'] for b in blocks]
    C0 = [b['C0'] for b in blocks]
    T0 = [b['T0'] for b in blocks]
    SR = [t[0] for t in terms]
    SC = [t[1] for t in terms]

    new = []
    a = new.append
    a('')
    a('/-! ## N2b cut SETS (regenerated 2026-11-05 by extract/gen_ne_cuts.py from')
    a('extract/out/ne_cuts.json; extraction cross-checked 689/689 against the value pins')
    a('above AND against the producer check_stair.cut_bound). Raw Nat lists, zip-aligned')
    a('with stairNEBlocks; Lean Finsets are built from them by `Finset.univ.filter`. -/')
    a('')
    a('/-- Per-block row cut sets R0 (sorted, distinct; row-group indices < 45). -/')
    a('def stairNECutR0 : List (List ℕ) :='), a(fmt_ll(R0))
    a('')
    a('/-- Per-block col cut sets C0 (sorted, distinct; col-group indices < 45). -/')
    a('def stairNECutC0 : List (List ℕ) :='), a(fmt_ll(C0))
    a('')
    a('/-- Per-block term cut sets T0 (sorted, distinct; term indices < 47). -/')
    a('def stairNECutT0 : List (List ℕ) :='), a(fmt_ll(T0))
    a('')
    a('/-- Term row supports sr_t of check_stair.structure (:42-54): row-group indices of the')
    a('45x45 corner whose family cells reference the term\'s shared coordinate. -/')
    a('def stairNESr : List (List ℕ) :='), a(fmt_ll(SR))
    a('')
    a('/-- Term col supports sc_t (ditto, column groups). -/')
    a('def stairNESc : List (List ℕ) :='), a(fmt_ll(SC))
    a('')
    a('theorem stairNECutR0_length : stairNECutR0.length = 689 := rfl')
    a('')
    a('theorem stairNECutC0_length : stairNECutC0.length = 689 := rfl')
    a('')
    a('theorem stairNECutT0_length : stairNECutT0.length = 689 := rfl')
    a('')
    a('theorem stairNESr_length : stairNESr.length = 47 := rfl')
    a('')
    a('theorem stairNESc_length : stairNESc.length = 47 := rfl')
    a('')
    a('set_option maxRecDepth 20000 in')
    a('set_option maxHeartbeats 0 in')
    a('/-- Bulk pin: every block\'s cut-set cardinalities sum to the pinned cut VALUE, and the')
    a('block indices are in range. Nat/List data only (decide-safe per N3/N4 evidence). -/')
    a('theorem stairNE_cuts_card :')
    a('    ((stairNEBlocks.zip (stairNECutR0.zip (stairNECutC0.zip stairNECutT0))).all fun b =>')
    a('      decide ((b.2.1.length + b.2.2.1.length + b.2.2.2.length = b.1.2.2.2) ∧')
    a('        b.1.1 < 45 ∧ b.1.2.1 < 45)) = true := by decide')
    a('')
    a('set_option maxRecDepth 20000 in')
    a('set_option maxHeartbeats 0 in')
    a('/-- Bulk pin: cut_bound\'s certificate loop (check_stair.py:87-89) for all 689 blocks,')
    a('reordered to iterate the SMALL support lists (kernel-cheap): every term outside T0 has')
    a('every sr-member with r ≤ i inside R0, or every sc-member with j ≤ c inside C0. This is')
    a('exactly `sr_t ∩ {0..i} ⊆ R0 ∨ sc_t ∩ {j..44} ⊆ C0` (sr/sc elements are all < 45). -/')
    a('theorem stairNE_cuts_cover :')
    a('    ((stairNEBlocks.zip (stairNECutR0.zip (stairNECutC0.zip stairNECutT0))).all fun b =>')
    a('      decide (∀ t ∈ List.range 47, t ∉ b.2.2.2 →')
    a('        (∀ r ∈ stairNESr.getD t [], r ≤ b.1.1 → r ∈ b.2.1) ∨')
    a('        (∀ c ∈ stairNESc.getD t [], b.1.2.1 ≤ c → c ∈ b.2.2.1)))')
    a('      = true := by decide')
    a('')

    out = head + '\n'.join(new) + marker + '\n'
    with open(LEAN, 'w') as f:
        f.write(out)
    print('regenerated NEBlocks.lean: %d bytes, %d lines' % (len(out), out.count('\n')))

if __name__ == '__main__':
    main()
