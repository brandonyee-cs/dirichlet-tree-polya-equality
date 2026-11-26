# Independent audit

The proof was audited by a separate AI agent (Claude), working from the source paper and the proof only, with its own code (`independent-checks/`, sharing no code with `scripts/`). Its report, lightly edited only to fix file paths:

---


**(1) The problem statement matches the paper.** I downloaded the paper and extracted its text myself.
- **Dirichlet tree:** no cycles, Dirichlet at degree-one vertices, Kirchhoff elsewhere. Degree-2 vertices are suppressed throughout.
- **Indexing:** λ_k starts at k=1 and counts multiplicity.
- **Open Problem 1.12(3):** is there equality in λ_k ≥ π²k²/L² for all k ≥ 1 if and only if every edge is an integer multiple of L/k? The README's theorem answers exactly this, for every k.

**(2) Each step checks out.**
- **Counting formula:** correct. N⁻ is the strict count (eigenvalues < ω'², with multiplicity). Non-generic ω' are only ever approached from above.
- **Elimination:** I re-derived the pivot and the parent update. The gaps to add:
  - The link to the count is not spelled out. Writing ω'ℓ = nπ + r, a pivot is negative exactly when r + s > π, so ⌊ω'ℓ_e/π⌋ + [pivot < 0] = ⌊t_e/π⌋.
  - The claim that only a discrete set of ω' is excluded needs a short induction from the leaves.
- **Vertex lemma:** it extends from two children to m children through f_v = g(τ₁, s′) + f′. The induction must start at d = 2, since one child gives f ≡ 0. The limit function stays continuous on [0,π)^d.
- **Limit step:** correct. The angles τ_e and s_e increase on (ω, ω+ε), which is easy but unproved in the README. So the right-hand limits lie in [0,π). Every vertex has at least two children, so every child τ tends to 0, and τ_root tends to 0 directly. That forces ωℓ_e ∈ πℤ on every edge: root, internal and leaf edges.

**(3) Independent numerics** (my own code: a Dirichlet-to-Neumann eigenvalue counter plus a finite-element check):
- Scans of stars (1,1,x), (1,2,x), (1,1,1,x) and H-shaped trees for k = 1..7: equality only where every edge is a multiple of L/k. The bound held everywhere. These families include eigenfunctions that vanish on whole arms.
- 400 random trees (vertices up to degree 5): the Prüfer count matched mine every time, and the key identity held.
- 4641 random (tree, k) cases with 253 equalities: equality exactly when all edges are multiples of L/k, with no violations of the bound.

Files are in `independent-checks/`:
- ref.py
- t_basic.py
- t_scan.py
- t_prufer.py
- t_rand.py

---

The write-up gaps (a)–(d) the audit lists are addressed in PROOF.md (marked "referee gap a" etc.).
