"""Symbolic checks of the algebraic identities used in the proof (README Steps 1-3)."""
import sympy as sp
w,l,s,a,b,x,y=sp.symbols('omega ell s a b x y',positive=True)
# Step 1: edge form for h solving h''=-w^2 h, h(0)=x, h(l)=y:  int h'^2 - w^2 h^2 = w[(x^2+y^2)cot(wl) - 2xy/sin(wl)]
t=sp.symbols('t')
h=x*sp.cos(w*t)+(y-x*sp.cos(w*l))/sp.sin(w*l)*sp.sin(w*t)
I=sp.integrate(sp.diff(h,t)**2-w**2*h**2,(t,0,l))
print("edge form:",sp.simplify(sp.expand_trig(I-w*((x**2+y**2)*sp.cot(w*l)-2*x*y/sp.sin(w*l)))))
# Step 2: Schur complement: cot(wl) - 1/(sin^2(wl)(cot s + cot wl)) == cot(s+wl)
e=sp.cot(w*l)-1/(sp.sin(w*l)**2*(sp.cot(s)+sp.cot(w*l)))-sp.cot(s+w*l)
print("schur:",sp.simplify(sp.expand_trig(e)))
# pivot: cot s + cot wl == sin(s+wl)/(sin s sin wl)
print("pivot:",sp.simplify(sp.expand_trig(sp.cot(s)+sp.cot(w*l)-sp.sin(s+w*l)/(sp.sin(s)*sp.sin(w*l)))))
# Step 3: for a+b<pi: cot a+cot b - cot(a+b) = (c1^2+c1c2+c2^2+1)/(c1+c2)
c1,c2=sp.symbols('c1 c2')
cotsum=(c1*c2-1)/(c1+c2)
print("vertex:",sp.simplify(c1+c2-cotsum-(c1**2+c1*c2+c2**2+1)/(c1+c2)))
# numeric: g(a,b)=a+b-s>0 on a grid, g(0+,b)->b
import mpmath as mp
mn=1e9
for i in range(1,200):
    for j in range(1,200):
        A=mp.pi*i/200; B=mp.pi*j/200
        S=mp.atan2(1,mp.cot(A)+mp.cot(B))
        mn=min(mn,(A+B-S)/max(A,B))
print("min of g/max(a,b) on grid:",mn)
