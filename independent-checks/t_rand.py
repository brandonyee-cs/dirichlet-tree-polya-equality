import sys; sys.path.insert(0,'.')
from ref import *
from t_prufer import rand_tree, rng
from math import gcd
cnt=[0,0,0,0]
for trial in range(250):
    E=rand_tree(int(rng.integers(1,5)))
    E=[(u,v,float(rng.integers(1,4))*0.5) for u,v,l in E]
    L=sum(e[2] for e in E)
    for k in range(1,int(2*L)+3):
        w=PI*k/L
        eq = Nminus(E,(w*(1+1e-9))**2)>=k and Nminus(E,(w*(1-1e-9))**2)<k
        below = Nminus(E,(w*(1-1e-9))**2)>=k   # would violate (1.6)
        mult = all(abs(e[2]*k/L-round(e[2]*k/L))<1e-9 for e in E)
        cnt[0]+=1; cnt[1]+=eq; cnt[2]+=(eq!=mult); cnt[3]+=below
print('cases,eq,mismatch(eq vs multiples),bound violations:',cnt)
