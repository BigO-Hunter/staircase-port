cd_path = '/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/CornerData.lean'
cd = open(cd_path).read()
# delete the whole transfer section (n7_rk_block/n7_isPiv_block) - not needed:
# the qMStair-level transfer goes through n7_rk_qm (Projector.lean) instead.
cut = cd.index('/-- NE-block ranks transfer')
tail = '\nend StaircasePort.Stair\n'
open(cd_path, 'w').write(cd[:cut].rstrip() + '\n' + tail)
print("transfer section deleted from CornerData")
PYEOF
