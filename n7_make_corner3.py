scr = open('/Users/dmitri.arkhipov/bigo-campaign/sp-corner/n7_scratch.lean').read()
lines = scr.split('\n')

def seg(a, b):  # 1-based inclusive-exclusive line numbers
    return '\n'.join(lines[a - 1:b - 1])

part1 = seg(15, 236)          # list lemmas, E1-E4, cut wrapper, pins, defs, run1
run2crk = seg(370, 448)       # run2 + isPiv_stairCorner_rk (copy 1)
wit = open('/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/CornerData.lean').read()

# n7Fin edits on part1 (run1)
old_run1 = '''    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
        + stairRunB l * x₁ ⟨l, by omega⟩ * y₁ ⟨l + 1, by omega⟩ ≠ 0) :'''
new_run1 = '''    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ (n7Fin l) * y₂ (n7Fin (l + 1))
        + stairRunB l * x₁ (n7Fin l) * y₁ (n7Fin (l + 1)) ≠ 0) :'''
assert old_run1 in part1
part1 = part1.replace(old_run1, new_run1, 1)
old_hdev = '''  have hdev := hT l hl1 hl2
  refine isPiv_of_bounds (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) l (22 + l) 1 ?_ ?_ ?_ ?_ ?_ ?_'''
new_hdev = '''  have hdev0 := hT l hl1 hl2
  have hnF : n7Fin l = (⟨l, by omega⟩ : Fin 23) := by
    refine Fin.ext ?_
    rw [n7Fin]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hnF] at hdev0
  have hdev := hdev0
  refine isPiv_of_bounds (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) l (22 + l) 1 ?_ ?_ ?_ ?_ ?_ ?_'''
assert old_hdev in part1
part1 = part1.replace(old_hdev, new_hdev, 1)

# n7Fin edit on corner_rk (both hT-shaped hypotheses in run2? no: run2 has none; corner_rk has one)
old_rk = '''    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
        + stairRunB l * x₁ ⟨l, by omega⟩ * y₁ ⟨l + 1, by omega⟩ ≠ 0)
    (hM1 : 25 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) 25 20)'''
new_rk = '''    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ (n7Fin l) * y₂ (n7Fin (l + 1))
        + stairRunB l * x₁ (n7Fin l) * y₁ (n7Fin (l + 1)) ≠ 0)
    (hM1 : 25 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) 25 20)'''
assert old_rk in run2crk
run2crk = run2crk.replace(old_rk, new_rk, 1)

# move isPiv_stairCorner_rk_witness from CornerData into Corner (after corner_rk)
wstart = wit.index('/-- **The 39 corner positions at the witness, through the symbolic clause**')
wend = wit.index('\nlemma n7_rk_block')
witness_thm = wit[wstart:wend].rstrip()
wit = wit[:wstart].rstrip() + '\n\n' + wit[wend:]
open('/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/CornerData.lean', 'w').write(wit)

header = '''/-
# N7 — the symbolic 39-position CORNER CLAUSE (corner runs (1,507,21) + (25,486,18))

The corner clause for the staircase projector `qMStair`: the 39 corner-run positions of
`stairDataRuns 23 529` are pivots of `qMStair (stairPairM x₁ y₁ x₂ y₂)` for ARBITRARY
labels under the hypotheses documented at `isPiv_stairCorner` (Projector.lean).

## Route (measured `n7_probe.py`, proved here; see SCAFFOLD.md "## CORNER NOTES")
Both runs go through N2c's four-rank method (`isPiv_of_bounds`); the r6
`isPiv_rank1_lower` route is structurally impossible for run 2 (below-diagonal band).
* Run 1 (l, 22+l), k = 1: cut-table uppers; lowers from the 2x2 minor whose determinant
  is exactly `hu·hv·dev_l` (entries `n7_E1..E4`) and the entry `corner[0][44] = hu·hv`.
* Run 2 (25+t, 2+t), k = 25: cut-table uppers; lowers from `hM1` (top-25 rows
  independent on cols ≥ 20; N2c cert 1 at the witness) and `hM2` (row 25+t independent
  on cols ≥ 2+t; N2c's 18 26-certificates at the witness — `CornerData.lean`).
`n7_rk_block`/`n7_isPiv_block` port `isPiv_block`
(nb_data_edge_solution.lean:227-238) via two submatrix-composition rank inequalities
(they live in `CornerData.lean` for build economy; so do the kernel-decided pins and
the witness discharges).

NOTE (2026-11-05): this block was first spliced into Pivot.lean (commit "N7 SPLICE") —
but under host load 75-140 every `lake build` was killed inside Pivot's long rebuild,
so the block moved to these NEW modules importing Pivot.
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.CornerData

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

'''
out = header + part1.rstrip() + '\n\n' + run2crk.rstrip() + '\n\n' + witness_thm + '\n\nend StaircasePort.Stair\n'
open('/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/Corner.lean', 'w').write(out)
print('Corner.lean assembled:', len(out.splitlines()), 'lines')
