import sys; sys.path.insert(0,'.')
from ref import *
from fractions import Fraction
def ratio(edges,k):
    L=sum(e[2] for e in edges); return lamk(edges,k)*L**2/(PI*k)**2
def multiples(edges,k,tol=1e-9):
    L=sum(e[2] for e in edges); return all(abs(e[2]*k/L-round(e[2]*k/L))<tol for e in edges)
fams={
 'star(1,1,x)':lambda x:[('c',1,1.),('c',2,1.),('c',3,x)],
 'star(1,2,x)':lambda x:[('c',1,1.),('c',2,2.),('c',3,x)],
 'star4(1,1,1,x)':lambda x:[('c',i,1.) for i in range(3)]+[('c',9,x)],
 'H(1,1,x,1,1)':lambda x:[('a',1,1.),('a',2,1.),('a','b',x),('b',3,1.),('b',4,1.)],
 'H(1,2,1,x,1)':lambda x:[('a',1,1.),('a',2,2.),('a','b',1.),('b',3,x),('b',4,1.)],
}
xs=np.linspace(0.05,4.0,791)
worst=1e9
for name,f in fams.items():
    for k in range(1,8):
        R=np.array([ratio(f(x),k) for x in xs])
        worst=min(worst,R.min())
        near=[(round(x,3),round(r,6)) for x,r in zip(xs,R) if r<1+1e-7]
        bad=[p for p in near if not multiples(f(p[0]),k,1e-6)]
        print(name,'k=%d'%k,'min R=%.8f'%R.min(),'eq pts:',near[:6],'BAD' if bad else '')
print('global min ratio',worst)
