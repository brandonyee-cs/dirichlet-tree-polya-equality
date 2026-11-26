"""Search for counterexamples to: lambda_k = pi^2 k^2/L^2  <=>  all edges multiples of L/k.
N(<=w^2) computed as N(<w'^2) at w'=w(1+eps) via DtN inertia in high precision (independent of the proof's Prufer recursion)."""
import random, math, sys
import mpmath as mp
from qg import degrees, count_dtn
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 7)
mp.mp.dps=60
def Nle(par,ln,w):
    for e in (mp.mpf('1e-25'),mp.mpf('3e-25'),mp.mpf('1e-24')):
        try: return count_dtn(par,ln,w*(1+e),60)[0]
        except ZeroDivisionError: pass
def gen(rng):
    # random tree, edges = integer multiples of unit 1 (L/k=1 when all are) , then perturb some
    from qg import random_shape
    par=random_shape(rng.randrange(2,10),rng); n=len(par)
    q=rng.choice([2,3,4,5,6])  # denominators
    ln=[None]+[mp.mpf(rng.randrange(1,3*q))/q for _ in range(1,n)]
    if rng.random()<0.5:
        # symmetrize: copy a random branch hanging at vertex 0 several times (eigenfunctions vanishing at vertices)
        kids=[v for v in range(1,n) if par[v]==0]
        b=rng.choice(kids)
        sub=[b]; 
        for v in range(1,n):
            if par[v] in sub and v not in sub: sub.append(v)
        for rep in range(rng.randrange(1,3)):
            mp_={}
            for v in sub:
                mp_[v]=len(par); par.append(0 if v==b else mp_[par[v]]); ln.append(ln[v])
        if rng.random()<0.5:  # perturb one edge so not all multiples but keep rational
            e=rng.randrange(1,len(par)); ln[e]=ln[e]+mp.mpf(1)/(2*q+1)
    return par,ln
stats={"pert":0,"eq_allmult":0,"eq_notmult":0,"tested":0}
for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 2000):
    par,ln=gen(rng)
    if any(x==2 for x in degrees(par)): continue   # degree-2 vertices are suppressed in the statement
    L=sum(ln[1:])
    for k in range(1,7):
        w=mp.pi*k/L
        N=Nle(par,ln,w); stats["tested"]+=1
        allm=all(abs(l*k/L-mp.nint(l*k/L))<mp.mpf('1e-40') for l in ln[1:])
        Nlt=count_dtn(par,ln,w*(1-mp.mpf('1e-25')),60)[0]
        assert Nlt<=k-1, ("bound violated",par,ln,k)
        if N>=k:
            if allm: stats["eq_allmult"]+=1
            else: stats["eq_notmult"]+=1; print("COUNTEREXAMPLE?",par,[str(x) for x in ln],k,N)
        elif allm: print("IF-direction fails?",par,ln,k,N)
print(stats)
