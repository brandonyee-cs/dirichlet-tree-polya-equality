import sys; sys.path.insert(0,'.')
from ref import *
rng=np.random.default_rng(5)
def rand_tree(n):
    # random tree on interior vertices then attach leaves so interior degree>=3
    par={0:None}; ch={0:[]}
    for i in range(1,n): p=int(rng.integers(0,i)); par[i]=p; ch[i]=[]; ch[p].append(i)
    edges=[]; leaf=1000
    for v in range(n):
        if par[v] is not None: edges.append((v,par[v],rng.uniform(0.1,2)))
        deg=len(ch[v])+(par[v] is not None)
        extra=max(0,3-deg)+int(rng.integers(0,3))
        for _ in range(extra): edges.append((leaf,v,rng.uniform(0.1,2))); leaf+=1
    return edges
def prufer(edges,w,root):
    adj={}
    for u,v,l in edges: adj.setdefault(u,[]).append((v,l)); adj.setdefault(v,[]).append((u,l))
    tot=0; D=0
    def go(x,p,l):  # edge from x up to p of length l; returns t
        nonlocal tot,D
        kids=[(y,ll) for y,ll in adj[x] if y!=p]
        if not kids: s=0.0
        else:
            ts=[go(y,x,ll) for y,ll in kids]
            c=sum(1/np.tan(t) for t in ts); s=np.arctan2(1,c)  # in (0,pi)
            D+=sum(t-PI*np.floor(t/PI) for t in ts)-s
        t=s+w*l; tot+=int(np.floor(t/PI)); return t
    (y,l),=adj[root]; t=go(y,root,l); D+=t-PI*np.floor(t/PI)
    return tot,D
bad=0;minD=9
for trial in range(400):
    E=rand_tree(int(rng.integers(1,7)))
    root=E[-1][0]; w=rng.uniform(0.1,15); L=sum(e[2] for e in E)
    N1=Nminus(E,w*w); N2,D=prufer(E,w,root)
    if N1!=N2 or abs(w*L/PI-N2-D/PI)>1e-8: bad+=1
    minD=min(minD,D)
print('mismatches',bad,'min D',minD)
