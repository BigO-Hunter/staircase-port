/- Stage 0 cross-tie: the REGENERATED dataset's histogram has the oracle's power sums
q = 0 and q = 1 (kernel-decided on both sides; the zero-axiom d2HIST_eq_bitR7 pin in
D2Data.lean transfers all 46 sums). Built EXPLICITLY (`lake build StaircasePort.MomOracleD2`),
not via the root import: it pulls the 13MB D2Data literal chain, which the host-memory
reaper kept killing during the stage-0 session — the 46 core pins (MomOracle.lean) build
on the Definitions closure alone. -/
import StaircasePort.D2Data
import StaircasePort.MomOracle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace StaircasePort.Mom

set_option maxRecDepth 20000

/-- The regenerated staircase histogram's childCount equals the oracle's S_0. -/
theorem d2S0 : powSum 0 StaircasePort.D2.d2HIST = bitR7PowSum 0 := by decide

/-- … and its rankSum equals the oracle's S_1. -/
theorem d2S1 : powSum 1 StaircasePort.D2.d2HIST = bitR7PowSum 1 := by decide

end StaircasePort.Mom
