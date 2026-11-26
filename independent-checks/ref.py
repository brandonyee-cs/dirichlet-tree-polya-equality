import numpy as np, sys
from scipy.sparse import lil_matrix
from scipy.sparse.linalg import eigsh
PI=np.pi
def degs(edges):
    d={}
    for u,v,l in edges: d[u]=d.get(u,0)+1; d[v]=d.get(v,0)+1
    return d
def Nminus(edges,lam):
    """# eigenvalues < lam, via edge Dirichlet counts + inertia of DtN (generic lam)."""
    w=np.sqrt(lam); d=degs(edges)
    inner=[x for x in d if d[x]>1]; idx={x:i for i,x in enumerate(inner)}
    M=np.zeros((len(inner),)*2); cnt=0
    for u,v,l in edges:
        c=np.cos(w*l); s=np.sin(w*l); cnt+=int(np.floor(w*l/PI))
        for a in (u,v):
            if a in idx: M[idx[a],idx[a]]+=w*c/s
        if u in idx and v in idx:
            M[idx[u],idx[v]]-=w/s; M[idx[v],idx[u]]-=w/s
    if len(inner): cnt+=int(np.sum(np.linalg.eigvalsh(M)<0))
    return cnt
def lamk(edges,k,iters=60):
    L=sum(e[2] for e in edges); lo=0.0; hi=(PI*(k+len(edges))/min(e[2] for e in edges))**2*4
    rng=np.random.default_rng(0)
    for _ in range(iters):
        mid=(lo+hi)/2*(1+1e-13*rng.standard_normal())
        if Nminus(edges,mid)<k: lo=mid
        else: hi=mid
    return (lo+hi)/2
def fem(edges,nev,h):
    d=degs(edges); nodes={}; n=0
    for x in d:
        if d[x]>1: nodes[x]=n; n+=1
    els=[]
    for u,v,l in edges:
        m=max(2,int(np.ceil(l/h))); hh=l/m
        ids=[nodes.get(u,-1)]+list(range(n,n+m-1))+[nodes.get(v,-1)]; n+=m-1
        for i in range(m): els.append((ids[i],ids[i+1],hh))
    K=lil_matrix((n,n)); Mm=lil_matrix((n,n))
    for a,b,hh in els:
        ke=np.array([[1,-1],[-1,1]])/hh; me=np.array([[2,1],[1,2]])*hh/6
        for i,p in enumerate((a,b)):
            for j,q in enumerate((a,b)):
                if p>=0 and q>=0: K[p,q]+=ke[i,j]; Mm[p,q]+=me[i,j]
    vals=eigsh(K.tocsc(),k=nev,M=Mm.tocsc(),sigma=0,which='LM',return_eigenvectors=False)
    return np.sort(vals)
