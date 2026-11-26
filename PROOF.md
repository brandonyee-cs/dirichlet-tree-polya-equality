# Equality in the Pólya-type bound λ_k ≥ π²k²/L² for Dirichlet trees

**Status: PROVED** for all k ≥ 1. The answer to Harrell–Kennedy–Ramos Open Problem 1.12(3) is *yes*.
Found and checked with AI assistance (see README); independently refereed by a separate AI agent (see AUDIT.md). Not yet checked by a human expert.

---

## 1. Problem

**Source.** E. M. Harrell II, J. B. Kennedy, G. J. Ramos, *Bounds on eigenvalue ratios of quantum graph
Laplacians*, arXiv:2603.26172v1 (27 Mar 2026). See Remark 1.7, eq. (1.6), and Open Problem 1.12(3).

> **Open Problem 1.12 (3).** Characterize the case of equality in the Pólya-type bound (1.6),
> λ_k(Γ) ≥ π²k²/L², for all k ≥ 1 and all Dirichlet trees Γ of total length L. Is it true that there is
> equality if and only if all edges of Γ have length equal to an integer multiple of L/k?

Remark 1.7 adds: *"Certainly, the 'if' direction is immediate, and the 'only if' direction is not hard to
show for k = 1, 2."* The bound (1.6) is a special case of [BKKM, Thm 4.7], cited in the paper.

**Definitions (paper, §1–2).**
- A *compact Dirichlet tree* Γ is a compact metric graph with no cycles. Every degree-one vertex carries a
  Dirichlet condition (a "Dirichlet leaf"). Every other vertex carries the standard (Kirchhoff) condition:
  continuity, plus the outgoing derivatives sum to zero.
- Degree-2 vertices with Kirchhoff conditions are invisible to the operator, so we suppress them. "Edge"
  in the conclusion means an edge after suppression.
- L = |Γ| = Σ_e ℓ_e is the total length.
- λ_1 ≤ λ_2 ≤ … are the eigenvalues of the Laplacian −d²/dx², counted with multiplicity. The form domain
  is H = {f ∈ H¹(Γ) : f continuous on Γ, f = 0 at the leaves}, and the form is a(f) = ∫_Γ |f′|².
- All eigenvalues are positive.

## 2. Main result

**Theorem.** Let Γ be a compact Dirichlet tree of total length L, with no degree-2 vertices, and let k ≥ 1.
Put ω = πk/L. Then λ_k(Γ) = ω² if and only if every edge length ℓ_e is a positive integer multiple of L/k.

The proof also gives a self-contained proof of the bound (1.6) (§3.3).

## 3. Proof

Notation:
- N(μ) is the number of eigenvalues ≤ μ, and N⁻(μ) is the number of eigenvalues < μ.
- Q_μ(f) = a(f) − μ‖f‖²_{L²}.
- By min-max, N⁻(μ) = n₋(Q_μ), the maximal dimension of a subspace of H on which Q_μ is negative definite.

### 3.0 "If" direction

Write ℓ_e = m_e L/k with m_e ≥ 1. Then Σ m_e = k. Cut every edge e into m_e segments of length h = L/k.

On each of the k segments J take φ_J(x) = sin(π(x − x_J)/h), extended by 0 to the rest of Γ. Each φ_J:
- is continuous and vanishes at every vertex, so φ_J ∈ H;
- has Rayleigh quotient (π/h)² = ω².

The φ_J have disjoint supports, so they are orthogonal both in L² and for a. Their span is therefore a
k-dimensional subspace on which a(f) ≤ ω²‖f‖². By min-max, λ_k ≤ ω². Combined with (1.6) (or §3.3)
this gives equality.

### 3.1 Step 1: index formula

Fix ω′ > 0 with sin(ω′ℓ_e) ≠ 0 for every e, and put μ = ω′². Let V_int be the set of interior vertices.
Decompose H = H_harm ⊕ H_0:
- H_0 = {f ∈ H : f(v) = 0 at every vertex} = ⊕_e H¹_0(e).
- H_harm is the space of functions h with h″ = −μh on every edge. Each such h is determined uniquely by
  its values x ∈ ℝ^{V_int} at the interior vertices (it is 0 at the leaves). Uniqueness uses
  sin(ω′ℓ_e) ≠ 0.

Every f ∈ H splits as f = h + (f − h), where h ∈ H_harm interpolates the vertex values of f. Integrating by
parts edgewise, for h ∈ H_harm and g ∈ H_0 we get

  ∫ h′g′ − μ∫ hg = Σ_e [h′g]_∂e − ∫ (h″ + μh) g = 0,

since g vanishes at all edge endpoints. So the splitting is Q_μ-orthogonal.

Negative indices add over a Q-orthogonal sum. To see this, each summand has a Q-nonnegative complement of
codimension equal to its index:
- in H_0, the span of the Dirichlet eigenfunctions with eigenvalue ≥ μ;
- in H_harm, which is finite-dimensional, linear algebra.

The sum of these complements is Q-nonnegative and has codimension n₋(Q|H_0) + n₋(Q|H_harm).

On H_0 the index counts the Dirichlet eigenvalues (jπ/ℓ_e)² < μ on each edge, which is ⌊ω′ℓ_e/π⌋. The
case of equality jπ = ω′ℓ_e is excluded by the choice of ω′. On H_harm, Q_μ(h) = xᵀMx. An edge with end
values a, b contributes

  ω′[(a² + b²) cot(ω′ℓ_e) − 2ab / sin(ω′ℓ_e)],

and an end at a leaf has value 0. (This integral identity was verified symbolically; see §4.) Therefore

  **N⁻(ω′²) = Σ_e ⌊ω′ℓ_e/π⌋ + n₋(M).**   (1)

### 3.2 Step 2: tree elimination with Prüfer angles

Root Γ at a leaf ρ and orient every edge toward ρ. Every interior vertex c then has a parent edge e_c and
d_c ≥ 2 child edges. There are at least 2 because deg c ≥ 3. Every edge except the root edge (the edge at ρ)
is a child edge of exactly one interior vertex, namely its upper end.

**Angles.** Define, from the leaves upward:
- s_e = 0 if the lower end of e is a leaf;
- t_e = s_e + ω′ℓ_e for every edge;
- if the lower end of e is an interior vertex c with child edges i, then s_e is the unique element of
  (0, π) with cot s_e = Σ_i cot t_i.

**Genericity.** Call ω′ *generic* if sin(ω′ℓ_e) ≠ 0 and sin t_e ≠ 0 for every edge e. At a generic ω′
all the cotangents above are finite.

**Elimination.** Eliminate the interior vertices leaf-first, by symmetric Gaussian elimination (LDLᵀ).
We claim, by induction, that when c is eliminated its current diagonal entry is

  p_c = ω′(Σ_i cot t_i + cot ω′ℓ_{e_c}) = ω′(cot s_{e_c} + cot ω′ℓ_{e_c}) = ω′ sin t_{e_c} / (sin s_{e_c} sin ω′ℓ_{e_c}).

The last equality is the *pivot identity*.

- Initially, the diagonal entry of M at c is Σ_{e ∋ c} ω′ cot(ω′ℓ_e).
- A child edge i whose lower end is a leaf contributes ω′ cot ω′ℓ_i = ω′ cot t_i.
- If the lower end of i is an interior vertex c_i, eliminating c_i changes only c's diagonal entry,
  because Γ is a tree. It subtracts (ω′/sin ω′ℓ_i)² / p_{c_i}. By the *Schur identity*

    cot x − 1/(sin²x (cot s + cot x)) = cot(s + x)   (x = ω′ℓ_i, s = s_i),

  child i then contributes ω′ cot t_i.

The off-diagonal entry from c to its parent is −ω′/sin ω′ℓ_{e_c}. The last vertex eliminated is the lower
end of the root edge; its parent ρ is a leaf, so ρ is not a variable. All pivots are nonzero exactly when
ω′ is generic. In that case Sylvester's law of inertia gives n₋(M) = #{c : p_c < 0}.

**Link to the floor function (referee gap a).** Let e = e_c and write ω′ℓ_e = nπ + r with
n = ⌊ω′ℓ_e/π⌋ and r ∈ (0, π). Then:
- sin ω′ℓ_e = (−1)ⁿ sin r and sin t_e = (−1)ⁿ sin(s_e + r);
- sin s_e > 0, and s_e + r ∈ (0, 2π) ∖ {π}.

Hence p_c < 0 ⇔ sin(s_e + r) < 0 ⇔ s_e + r > π ⇔ ⌊t_e/π⌋ = n + 1. Otherwise ⌊t_e/π⌋ = n. So

  ⌊ω′ℓ_e/π⌋ + [p_c < 0] = ⌊t_e/π⌋.

For leaf-start edges t_e = ω′ℓ_e, so the same formula holds trivially. Substituting into (1):

  **N⁻(ω′²) = Σ_e ⌊t_e/π⌋ for every generic ω′.**   (2)

**The non-generic set is discrete (referee gap b).** For an interior vertex c, let M_c be the principal
submatrix of M on c and its descendants. Gaussian elimination inside the subtree is the same process, so
det M_c = (product of the pivots of c and its descendants).

Let D_c(ω′) = det M_c · Π sin²(ω′ℓ_e), with the product over the edges of the subtree together with e_c.
Every entry of M_c has a denominator sin(ω′ℓ_e) for an incident edge e, and each edge's sine occurs to the
power at most 2 in any term of the determinant expansion. So D_c extends to a real-analytic (indeed entire)
function of ω′.

D_c is not identically zero. As ω′ ↓ 0 we have ω′ cot(ω′ℓ) → 1/ℓ and ω′/sin(ω′ℓ) → 1/ℓ. So M_c tends
to a weighted graph Laplacian grounded at the parent vertex and at the leaves, which is positive definite.
Hence det M_c > 0 for small ω′.

The set E = ∪_e {ω′ : sin(ω′ℓ_e) = 0} ∪ ∪_c {ω′ : D_c(ω′) = 0} is therefore discrete in (0, ∞). Off E,
induction from the leaves shows that every pivot is defined and nonzero, because p_c = det M_c / Π(det
M_{c′}) over the children c′. So every ω′ ∉ E is generic.

### 3.3 Step 3: the key identity and the vertex lemma

Put K(ω′) = ω′L/π = Σ_e (t_e − s_e)/π. Let τ_e = t_e − π⌊t_e/π⌋ ∈ (0, π) at a generic ω′. By (2),

  π(K − N⁻) = Σ_e τ_e − Σ_e s_e = Σ_{c ∈ V_int} f_c + τ_root,   f_c := Σ_{i child of c} τ_i − s_{e_c}.   (3)

The grouping works because each non-root edge is a child of exactly one interior vertex, and s_e = 0 when
the lower end of e is a leaf. Since cot has period π, cot s_{e_c} = Σ_i cot τ_i. So f_c depends only on
the child angles τ_i ∈ (0, π).

**Vertex lemma.** Let d ≥ 2, τ ∈ (0, π)^d, and let s ∈ (0, π) be defined by cot s = Σ cot τ_i. Put
f(τ) = Σ τ_i − s. Then f(τ) > 0.

*Proof.*
1. *Case d = 2, τ = (a, b).* If a + b ≥ π, then s < π ≤ a + b. Suppose instead a + b < π. Put c₁ = cot a
   and c₂ = cot b.
   - Then c₁ + c₂ = sin(a + b)/(sin a sin b) > 0.
   - The cotangent addition formula gives
     cot a + cot b − cot(a + b) = (c₁² + c₁c₂ + c₂² + 1)/(c₁ + c₂).
     The numerator equals (c₁ + c₂/2)² + 3c₂²/4 + 1 > 0, so the whole expression is positive.
   - Hence sin(a + b − s) = sin s · sin(a + b) · (cot s − cot(a + b)) > 0.
   - Since a + b − s ∈ (−π, π), this forces a + b − s > 0.
2. *General d (referee gap c).* Let s′ be defined by cot s′ = Σ_{i≥2} cot τ_i, with s′ = τ₂ when d = 2.
   Then cot s = cot τ₁ + cot s′, and

     f(τ) = g(τ₁, s′) + (Σ_{i≥2} τ_i − s′),   g(a, b) := a + b − s(a, b).

   For d − 1 = 1 the bracket is 0. Otherwise it is f for d − 1 angles, which is positive by induction.
   So f > g(τ₁, s′) > 0 by step 1.

   The induction must start at d = 2: with a single child, f ≡ 0. That is exactly why degree-2 vertices
   are suppressed. ∎

**Continuous extension.** Extend s, and hence f, to [0, π)^d by setting s = 0 whenever some τ_i = 0. This
extension is continuous: as τ_j → 0⁺, cot τ_j → +∞, while the other cot τ_i stay bounded below because
τ_i < π − δ. So Σ cot τ_i → +∞ and s → 0.

On the boundary f = Σ τ_i. Hence **on [0, π)^d, f(τ) = 0 iff τ = 0.**

**Consequence (re-proof of (1.6)).** By (3) and the lemma, K(ω′) > N⁻(ω′²) for every generic ω′. Suppose
λ_k < (πk/L)². Pick a generic ω′ with λ_k < ω′² < (πk/L)². Then N⁻(ω′²) ≥ k > K(ω′), a contradiction.

### 3.4 Step 4: the equality case

Let ω = πk/L and suppose λ_k = ω². Then N(ω²) ≥ k. Choose ε > 0 so that two conditions hold: (ω, ω + ε)
contains no point of E, and no eigenvalue lies in (ω², (ω + ε)²).

**Monotonicity (referee gap d).** On J = (ω, ω + ε) every s_e and t_e is continuous. We show by induction
from the leaves that t_e is strictly increasing and s_e is nondecreasing on J.
- For leaf-start edges, s_e ≡ 0 and t_e = ω′ℓ_e.
- At an interior vertex, each child t_i is continuous and never meets πℤ on J. So it stays in one
  interval (mπ, (m+1)π). There cot t_i is strictly decreasing, so Σ cot t_i is strictly decreasing.
  Since arccot: ℝ → (0, π) is decreasing, s_e is strictly increasing, and so is t_e = s_e + ω′ℓ_e.

Since ⌊t_e/π⌋ = m_e is constant on J, τ_e = t_e − πm_e is strictly increasing. Both s_e and τ_e take
values in [0, π). So the right limits s_e⁺ and τ_e⁺ at ω′ ↓ ω exist and lie in [0, π).

**Limit.** For ω′ ∈ J we have N⁻(ω′²) = N(ω²) ≥ k. By (3),

  Σ_c f_c + τ_root = π(K(ω′) − N⁻(ω′²)) ≤ π(K(ω′) − k) = (ω′ − ω)L → 0.

Every summand is ≥ 0, so each one tends to 0. Since f_c is continuous on [0, π)^{d_c}, we get
f_c(τ⁺) = 0, so every child angle has τ_i⁺ = 0. Every non-root edge is a child edge, and τ_root⁺ = 0
directly, so **τ_e⁺ = 0 for every edge**.

Next, s_e⁺ = 0 for every edge. For leaf-start edges this holds trivially. For the others, the child τ_i
decrease to 0 as ω′ ↓ ω, so Σ cot τ_i → +∞.

Finally, take the limit in τ_e = s_e + ω′ℓ_e − πm_e. This gives 0 = ωℓ_e − πm_e, that is,
ℓ_e = m_e π/ω = m_e L/k, with m_e ≥ 1 because ℓ_e > 0. ∎

**Remarks.**
- The argument does not assume that eigenvalues are simple, nor that eigenfunctions avoid the vertices.
  All degenerate situations are absorbed by taking the one-sided limit ω′ ↓ ω through generic values.
- With degree-2 vertices present (f ≡ 0 there), the conclusion applies to the merged edges, which is the
  intended reading of the problem.

## 4. Verification

All paths below are relative to this repository. Python ≥ 3.12 with the packages in `requirements.txt`
(`pip install -r requirements.txt`).

| Script | Certifies |
|---|---|
| `scripts/check_identities.py` (log `logs/identities.log`) | sympy: the edge-form integral, the Schur identity, the pivot identity and the algebraic vertex identity all reduce to 0. A grid check confirms g > 0. |
| `scripts/test1.py` (log `logs/test1.log`) | For 300 random trees at random ω′, the Prüfer count (2) equals an independent DtN-inertia count (mpmath, 30 digits). The identity (3) holds and K − N⁻ > 0. A P1-FEM count agrees on samples. It reproduces the paper's equilateral-star values. |
| `scripts/test2.py 11 <trials>` (log `logs/test2_seed11.log`) | A counterexample search over rational-length trees for k = 1..6, using DtN inertia at 60 digits: 16008 (tree, k) cases and 1339 equality cases. Every equality case had all edges multiples of L/k (0 others), and the bound held throughout. |
| `independent-checks/{t_basic,t_scan,t_prufer,t_rand}.py` | The referee's own DtN counter plus an FEM check, sharing no code with the above. Scans of star families and H-shaped trees for k = 1..7; 400 random trees for the Prüfer identity; 4641 random (tree, k) cases with 253 equalities. Equality held exactly when all edges are multiples of L/k. |

These computations are evidence for the ingredients and the statement. They are not part of the proof.
The only proof steps that were machine-checked are the identities listed above, which are also proved in
Lean (§5).

## 5. Lean status

File: `lean/DirichletTreePolya/QuantumGraphEquality.lean`. It compiles; the
only warnings are for the `sorry`s.

- **Definitions.**
  - `DirichletTree`: a `SimpleGraph.IsTree` on `Fin n` with n ≥ 2, positive lengths and no degree-2
    vertices.
  - `Admissible`: edgewise Lipschitz functions, continuous at vertices and zero at leaves.
  - `energy`, `mass`, and `lam k`, the Courant–Fischer min-max value.
  - `PolyaBound` and `OpenProblem_1_12_3` as `Prop`s.
- **Simplification, stated in the file.** The min-max runs over Lipschitz functions rather than over H¹.
  This gives the same values because Lipschitz functions form a form core, but that identification is
  not formalised. Mathlib has no spectral theory of quantum graphs.
- **Proved:**
  - `pivot_identity`, `schur_identity`, `cot_add'`, `vertex_identity` and `vertex_numerator_pos`;
  - **`vertex_lemma`**: the d = 2 vertex lemma s < a + b, which is the analytic heart of Step 3.
- **`sorry`:**
  - `polyaBound` (1.6);
  - `openProblem_1_12_3`, the main theorem. Formalising it needs H¹ on metric graphs, min-max for the
    self-adjoint realisation, and inertia additivity.

## 6. Prior work / novelty

Searched (26 Nov 2026): arXiv (the source is still v1), Semantic Scholar citations of arXiv:2603.26172
(none), Zenodo, and the main public repositories of AI-assisted conjecture resolutions. No prior resolution of
Open Problem 1.12(3) was found. The Prüfer-angle and Dirichlet-to-Neumann techniques used here are standard for
quantum graphs (see e.g. [BKKM] and the nodal-count literature), so an equivalent argument may exist in the
surgery literature; pointers are welcome.

## 7. Open follow-ups

- Equality cases of the more general bound [BKKM, Thm 4.7], which allows Neumann leaves and cycles:
  λ_k ≥ (k − N + β/2)²π²/L² (paper, after Remark 1.7).
- A Lean formalisation of Steps 3–4 in the purely finite-dimensional "angle" form, taking (2) as an
  axiom, looks feasible and would isolate the analytic input.
