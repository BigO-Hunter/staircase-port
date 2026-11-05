/- N3 timing ladder stage 4 (runs parallel to stage 1): decide +kernel on
stair_cert_chk — pure Nat list arithmetic (2025 dotL products of 45 terms with
8-digit entries + 90 length checks). Budget: 5 min. r6 precedent: cert_chk over
certP = 2^31-1 went through decide +kernel at the same magnitude. -/
import StaircasePort.Cert

open StaircasePort.Stair
open IntMul.Kappa.R6.Bit.NB (certChk)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem n3_t4_cert_chk : certChk stairCertRows stairCertCols 45 stairCertP = true := by
  decide +kernel

#print axioms n3_t4_cert_chk
