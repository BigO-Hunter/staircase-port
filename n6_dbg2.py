import numpy as np
import n6_midrun as nm

M, q, order, dv = nm.build()
p = nm.p
print('shape', q.shape, 'rank', nm.rank_mod(q))

def Rf(X, Y):
    return nm.rank_mod(q[:X, Y:])

i, j = 1, 507
print('full: rk(i+1,j+1)=', Rf(i+1, j+1), 'rk(i,j)=', Rf(i, j),
      'rk(i+1,j)=', Rf(i+1, j), 'rk(i,j+1)=', Rf(i, j+1))
print('corner-relative: ')
def Rc(X, Y):
    return nm.rank_mod(q[:45, 484:529][:X, Y:])
print('  rk(2,24)=', Rc(2, 24), 'rk(1,23)=', Rc(1, 23), 'rk(2,23)=', Rc(2, 23), 'rk(1,24)=', Rc(1, 24))
print('corner block vs global slice identical:',
      bool((q[:45, 484:529] == q[:45, 484:529]).all()))
