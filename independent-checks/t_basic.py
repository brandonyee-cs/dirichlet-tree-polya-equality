import sys; sys.path.insert(0,'.')
from ref import *
# sanity: interval, equilateral star
I=[(0,1,1.0)]
print([round(lamk(I,k)/PI**2,6) for k in range(1,5)])
S3=[('c',i,1.0) for i in range(3)]
print([round(lamk(S3,k)/PI**2*9/1,6) for k in range(1,6)], "(units pi^2/L^2 *?)")
# compare with FEM on irregular tree
T=[('a','b',0.7),('b',1,0.4),('b',2,1.3),('a',3,0.55),('a','c',0.9),('c',4,0.33),('c',5,0.81),('c',6,0.2)]
ex=[lamk(T,k) for k in range(1,9)]
for h in (0.01,0.005):
    print(h, np.max(np.abs(fem(T,8,h)/np.array(ex)-1)))
