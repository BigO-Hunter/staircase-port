"""Splice the generated N2c block into StaircasePort/Pivot.lean, replacing the scaffolded
`stairCorner_pivots_witness` theorem (with its `/-- **N2c** ...` doc comment).

Idempotent-ish: re-running after a splice fails loudly (the scaffold theorem is gone).
"""
import re, sys

src = open('StaircasePort/Pivot.lean').read()
block = open('n2c_block.lean').read()

head = "/-- **N2c** — check_stair item 3 instantiated at the extracted witness"
i = src.index(head)
j = src.index("theorem stairCorner_pivots_witness :\n    ∀ x ∈ runPairs stairCornerRuns45, IsPiv stairCornerQ x.1 x.2 := by sorry")
end = j + len("theorem stairCorner_pivots_witness :\n    ∀ x ∈ runPairs stairCornerRuns45, IsPiv stairCornerQ x.1 x.2 := by sorry")

pre = "set_option maxHeartbeats 0\nset_option maxRecDepth 20000\n\n"
out = src[:i] + pre + block + src[end:]
open('StaircasePort/Pivot.lean', 'w').write(out)
print('spliced: removed %d chars, inserted %d' % (end - i, len(block)))
print('Pivot.lean now %d lines' % out.count('\n'))
