import random, math
from qg import *
rng=random.Random(1)
bad=0
for trial in range(300):
    n=rng.randrange(2,12); par,ln=random_tree(n,rng)
    w=rng.uniform(0.5,25)
    Nd,_=count_dtn(par,ln,w,30); Np,D=count_prufer(par,ln,w)
    L=sum(ln[1:]); K=w*L/math.pi
    if Nd!=Np or abs(K-Np-D)>1e-8 or D<=0 or Nd>math.ceil(K)-1: bad+=1; print("BAD",par,ln,w,Nd,Np,K,D)
print("prufer/dtn trials bad:",bad)
# FEM sanity on a few
for trial in range(8):
    n=rng.randrange(3,8); par,ln=random_tree(n,rng)
    w=rng.uniform(1,12)
    Nd,_=count_dtn(par,ln,w,30); Nf=count_fem(par,ln,w*w,h=4e-3)
    print("dtn",Nd,"fem",Nf)
# paper example: equilateral m-star, edges pi
for m in (3,4,5):
    par=[None]+[0]*m; ln=[None]+[math.pi]*m; L=m*math.pi
    # lambda_m = pi^2 m^2/L^2 = 1 ; lambda_{m+1}=9/4
    e=1e-7
    print(m, count_dtn(par,ln,1-e)[0], count_dtn(par,ln,1+e)[0], count_dtn(par,ln,1.5-e)[0], count_dtn(par,ln,1.5+e)[0])
