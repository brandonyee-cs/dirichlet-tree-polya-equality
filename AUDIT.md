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

# Adversarial reviews (round 2)

Two further reviewers (Claude), each instructed to assume the proof is wrong and hunt for an error, each
given only the paper and PROOF.md (not the audit above), each writing fresh numerical code. One focused on
the analytic steps, one on the combinatorial steps. Their code is not included here; their reports are
summarized faithfully below.

## Review A (analytic steps): verdict CORRECT

- **Setup vs paper §2:** form domain and Laplacian match the paper's H¹₀(Γ, V_D); Kirchhoff conditions at all
  interior vertices; degree-2 suppression matches the paper's convention.
- **H = H_harm ⊕ H_0:** direct (a function in both has zero vertex values, hence is 0 since sin(ω′ℓ_e) ≠ 0)
  and spanning; Q-orthogonal by integration by parts; edge form re-derived by hand.
- **Index additivity:** valid even if Q has a kernel on a summand. The Dirichlet count ⌊ω′ℓ/π⌋ is right.
- **Elimination and genericity:** Schur and pivot identities, Sylvester count and floor link checked by hand;
  D_c is entire and not identically zero; off E all pivots are nonzero, which forces sin t_e ≠ 0.
- **Steps 3–4:** vertex lemma, continuous extension, monotonicity, one-sided limit, N⁻(ω′²) = N(ω²) ≥ k all
  fine. Multiplicities and eigenfunctions vanishing at vertices never enter.
- **Cosmetic gaps (fixed in PROOF.md):** the ≥ direction of index additivity; "f > g" should be "f ≥ g"
  for d = 2; "nondecreasing" vs "strictly increasing" wording in §3.4; scope remark about interior Dirichlet
  conditions.
- **Numerics (own P1-FEM with Richardson extrapolation and dense eigensolver; multiplicities by 30-digit SVD
  of the secular matrix):** equilateral stars with 3–8 arms, k ≤ 17 (equality exactly when the arm count
  divides k); 1875 random-tree cases with near-lattice shifts, multiplicities up to 3 and eigenfunctions on
  sub-branches, k ≤ 10 (112 equality cases, all lattice, 0 mismatches); 16384 symmetric two-level trees,
  k ≤ 8 (nothing flagged); Nelder–Mead minimisation of λ_k/ω² − 1 over star edge lengths (minimisers only at
  lattice points or degenerate boundaries). No counterexample.

## Review B (combinatorial steps): verdict CORRECT

- **Step 2:** every interior vertex has ≥ 2 children without degree-2 vertices; single-edge tree also fine.
  Pivot and Schur identities re-derived. Floor link: the (−1)ⁿ factors cancel, valid for n even, odd and 0.
- **Discreteness of the non-generic set** and the pivot/determinant induction: correct.
- **Identity (3):** the bookkeeping is a bijection between interior vertices c and edges e_c; leaf-start edges
  have s = 0; the root edge's τ stands alone; cot-periodicity valid.
- **Vertex lemma:** d = 2 and the induction to general d are correct; continuous extension valid.
- **Equality case:** τ_e strictly increases and stays below π, so the right limit lies in [0, π) and cannot
  be π; ⌊t_e/π⌋ is constant on J; each summand tends to 0; m_e ≥ 1; root edge handled.
- **Interpretation:** the answer "yes" needs degree-2 suppression, which is the paper's stated convention;
  without it an interval with a dummy vertex at a generic point is a counterexample.
- **Minor points (fixed in PROOF.md):** same wording points as Review A, plus "closed span" in §3.1.
- **Numerics (fresh code):** Prüfer count vs independent P1-FEM count: 590/590 matches on 150 random trees;
  identity (3) to 1e-8, min(K − N⁻) = 0.258; vertex lemma on 20,000 random points, d = 2..5; equality search
  over 2000 (tree, k) cases, k ≤ 8, multiplicity from 40-digit SVD: 55 equality cases, all lattice, none
  otherwise; limit check: τ, s → 0 linearly at equality trees, jump to π after a 1e-3 perturbation.
