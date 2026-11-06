import subprocess
spliced = subprocess.run(['/usr/bin/git', 'show', 'aee0c5f:StaircasePort/Pivot.lean'],
                         capture_output=True, text=True, cwd='/Users/dmitri.arkhipov/bigo-campaign/sp-corner').stdout
start = spliced.index('/-! ### n7 part 1')
end = spliced.index('/-! #### block transfer')
block = spliced[start:end] + spliced[spliced.index('/-! #### block transfer'):spliced.index('end StaircasePort.Stair')].rstrip() + '\n'

# ---- split the block: witness section moves to CornerData (imported by Corner) ----
wstart = block.index('/-! #### witness discharges')
proofs = block[:wstart]
witness = block[wstart:]

data_header = '''/-
# N7 data — kernel-decided pins for the CORNER CLAUSE (the heavy `decide` payload)

Split from `Corner.lean` for build economy: every module here is banked independently,
so each `lake build` stage fits the host's kill window (see SCAFFOLD.md "## CORNER
RESUME"). Contents: the 8 cut-table membership pins (`n7_mem_*`, 148 kernel decides
over the 689-block list) and the witness discharges (`n7_hT_witness` 21 norm_num cases,
`n7_hM1_witness`/`n7_hM2_witness` N2c certificates verbatim, and the Pivot-level
integration check).
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Pivot

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

'''
open('/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/CornerData.lean', 'w').write(
    data_header + witness.rstrip() + '\n\nend StaircasePort.Stair\n')

corner_header = '''/-
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
(nb_data_edge_solution.lean:227-238) via two submatrix-composition rank inequalities.

NOTE (build economy, 2026-11-05): this block was first spliced into Pivot.lean (commit
"N7 SPLICE") — but under host load 75-140 every `lake build` was killed inside Pivot's
long rebuild, so the block moved to this NEW module; the kernel-decided pins/witnesses
live in `CornerData.lean` (banked independently).
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
open('/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/Corner.lean', 'w').write(
    corner_header + proofs.rstrip() + '\n\nend StaircasePort.Stair\n')

prj_path = '/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/Projector.lean'
prj = open(prj_path).read()
open(prj_path, 'w').write(prj)
print("CornerData.lean + Corner.lean written;", len(proofs.splitlines()), "+", len(witness.splitlines()), "lines")
