"""Dirichlet trees: eigenvalue counting by three independent methods.
Tree given as parent array: vertices 0..n-1, parent[v] for v>=1, length[v] = length of edge (v,parent[v]).
Leaves (degree 1) carry Dirichlet conditions, other vertices Kirchhoff."""
import numpy as np, math, random
import mpmath as mp

def degrees(par):
    n=len(par); d=[0]*n
    for v in range(1,n): d[v]+=1; d[par[v]]+=1
    return d

def count_dtn(par, ln, w, prec=50):
    """N(<w^2) = sum_e #{j: j pi < w l_e} + n_-(M(w)); requires sin(w l_e) != 0."""
    mp.mp.dps=prec
    n=len(par); d=degrees(par)
    inner=[v for v in range(n) if d[v]>=2]; idx={v:i for i,v in enumerate(inner)}
    M=mp.zeros(len(inner))
    w=mp.mpf(w); ND=0
    for v in range(1,n):
        u=par[v]; t=w*mp.mpf(ln[v])
        ND+= int(mp.ceil(t/mp.pi))-1
        c=mp.cot(t)*w; s=w/mp.sin(t)
        for a in (u,v):
            if a in idx: M[idx[a],idx[a]]+=c
        if u in idx and v in idx:
            M[idx[u],idx[v]]-=s; M[idx[v],idx[u]]-=s
    if len(inner)==0: return ND, []
    ev=mp.eigsy(M,eigvals_only=True)
    ev=[ev[i] for i in range(len(inner))]
    return ND+sum(1 for x in ev if x<0), ev

def count_fem(par, ln, lam, h=2e-3):
    """Approximate N(<lam) via P1 FEM (upper bounds of eigenvalues) -- sanity only."""
    import scipy.sparse as sp, scipy.linalg as sl
    n=len(par); d=degrees(par)
    nodes={}; cnt=0
    for v in range(n):
        if d[v]>=2: nodes[v]=cnt; cnt+=1
    I=[];J=[];K=[];Mv=[]
    def add(i,j,k,m):
        if i is None or j is None: return
        I.append(i);J.append(j);K.append(k);Mv.append(m)
    for v in range(1,n):
        u=par[v]; m=max(4,int(math.ceil(ln[v]/h))); hh=ln[v]/m
        ids=[nodes.get(u)]+[None]*(m-1)+[nodes.get(v)]
        for q in range(1,m): ids[q]=cnt; cnt+=1
        for q in range(m):
            a,b=ids[q],ids[q+1]
            for (x,y,k,mm) in ((a,a,1/hh,hh/3),(b,b,1/hh,hh/3),(a,b,-1/hh,hh/6),(b,a,-1/hh,hh/6)):
                add(x,y,k,mm)
    A=sp.coo_matrix((K,(I,J)),shape=(cnt,cnt)).toarray(); B=sp.coo_matrix((Mv,(I,J)),shape=(cnt,cnt)).toarray()
    ev=sl.eigh(A,B,eigvals_only=True,subset_by_value=(-1,lam))
    return len(ev)

def count_prufer(par, ln, w):
    """Generic-case oscillation count: root at a leaf; N(<w^2) = sum_e floor(t_e/pi) (t_root non-integer multiple)."""
    n=len(par); d=degrees(par)
    ch=[[] for _ in range(n)]
    for v in range(1,n): ch[par[v]].append(v)
    # reroot at a leaf r
    adj=[[] for _ in range(n)]
    for v in range(1,n): adj[v].append((par[v],ln[v])); adj[par[v]].append((v,ln[v]))
    r=[v for v in range(n) if d[v]==1][0]
    order=[];P={r:None};L={};st=[r]
    while st:
        x=st.pop(); order.append(x)
        for y,l in adj[x]:
            if y not in P: P[y]=x; L[y]=l; st.append(y)
    t={}; s={}; total=0.0; D=0.0
    for x in reversed(order):
        if x==r: continue
        kids=[y for y,_ in adj[x] if P.get(y)==x]
        if not kids: s[x]=0.0
        else:
            c=sum(1/math.tan(t[y]) for y in kids)
            s[x]=math.atan2(1,c)  # in (0,pi)
            D+= sum(t[y]-math.pi*math.floor(t[y]/math.pi) for y in kids)-s[x]
        t[x]=s[x]+w*L[x]
        total+=math.floor(t[x]/math.pi)
    root_edge=[y for y,_ in adj[r]][0]
    D+= t[root_edge]-math.pi*math.floor(t[root_edge]/math.pi)
    return total, D/math.pi

def random_shape(n, rng):
    # random tree without degree-2 vertices: grow by attaching 2 new leaves to an existing leaf or 1 leaf to a vertex of degree>=3
    par=[None,0]
    while len(par)<n:
        d=degrees(par)
        leaves=[v for v in range(len(par)) if d[v]==1]
        big=[v for v in range(len(par)) if d[v]>=3]
        if big and rng.random()<0.4: par.append(rng.choice(big))
        else:
            v=rng.choice(leaves); par+= [v,v]
    return par

def random_tree(n, rng, maxlen=1.0):
    par=random_shape(n,rng); n=len(par)
    ln=[None]+[rng.uniform(0.05,maxlen) for _ in range(1,n)]
    return par, ln
