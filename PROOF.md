# Equality in the Pólya-type bound for Dirichlet trees

*Draft, November 2026. Written with AI assistance (Claude) and not yet checked by a human expert;
see [CHECKS.md](CHECKS.md) for how it has been checked so far.*

## 1. Introduction

Let Γ be a compact Dirichlet tree of total length L, that is, a metric tree with Dirichlet conditions at
the leaves and Kirchhoff conditions at the other vertices. In Remark 1.7 of [HKR], Harrell, Kennedy and
Ramos observe that a theorem of Berkolaiko, Kennedy, Kurasov and Mugnolo [BKKM17, Thm 4.7] contains, as a
special case, the bound

  λ_k(Γ) ≥ π²k²/L²  for every k ≥ 1,   (1.6)

which says that the leading Weyl term bounds λ_k from below, in analogy with Pólya's conjecture for
Dirichlet domains. They ask when equality holds:

> **Open Problem 1.12(3)** [HKR]. Characterize the case of equality in the Pólya-type bound (1.6),
> λ_k(Γ) ≥ π²k²/L², for all k ≥ 1 and all Dirichlet trees Γ of total length L. Is it true that there is
> equality if and only if all edges of Γ have length equal to an integer multiple of L/k?

They add that the "if" direction is immediate and that the "only if" direction is not hard for k = 1, 2.
We show that the answer is yes for every k.

**Theorem.** Let Γ be a compact Dirichlet tree of total length L with no vertices of degree 2, and let
k ≥ 1. Then λ_k(Γ) = π²k²/L² if and only if every edge length is a positive integer multiple of L/k.

*Idea of the proof.* For a frequency ω′ outside a discrete exceptional set, we count the eigenvalues below
ω′² by Prüfer-type angles. Root the tree at a leaf, start each edge at a leaf with angle 0, add ω′ℓ_e along
the edge, and at each interior vertex combine the incoming angles t_i into one outgoing angle s by
cot s = Σ cot t_i. The number of eigenvalues below ω′² is then Σ_e ⌊t_e/π⌋. Since ω′L/π = Σ_e (t_e − s_e)/π,
the difference ω′L/π − N⁻(ω′²) splits into one term per interior vertex, and an elementary inequality
for the cotangent shows that each term is positive when the vertex has at least two children. This gives
(1.6) again. If equality holds in (1.6), the sum of the vertex terms tends to 0 as ω′ decreases to πk/L, so
every angle tends to 0 modulo π, and this says exactly that every edge length is a multiple of L/k.

*What is standard and what is new.* The variational setting and min-max are standard [BK13, Ku24]. The
reduction of the eigenvalue count to a finite matrix of vertex values (Step 1) and the recursion of angles
from the leaves of a tree (Step 2) are standard techniques; compare the Riccati-variable recursion on
trees in [Be08, §3.2]. As far as we know, the vertex inequality (Step 3), the identity that turns
ω′L/π − N⁻ into a sum of vertex terms, and the limit argument for the equality case (Step 4) are new. As a
by-product the argument gives a proof of (1.6) for trees that does not use [BKKM17].

*Outline.* Section 2 fixes conventions. Section 3 proves the "if" direction, and Section 4 proves (1.6) and
the "only if" direction in four steps. Section 5 discusses the hypotheses and the degenerate cases.
Section 6 describes the computer checks, Section 7 the Lean formalization of Steps 3–4, and Section 8 the
literature search.

## 2. Setting and conventions

We follow [HKR, §1–2].

- A *compact Dirichlet tree* Γ is a compact metric graph without cycles. Every vertex of degree 1 (a
  *leaf*) carries a Dirichlet condition. Every other vertex carries the Kirchhoff condition: continuity,
  and the outgoing derivatives sum to zero.
- A Kirchhoff vertex of degree 2 does not affect the operator, and, as in [HKR] ("Vertices of degree two
  are understood to be suppressed in all theorems of this article"), we assume there are none. So "edge"
  in the Theorem means an edge after such vertices are removed. Remark 5.1 shows the Theorem is false
  without this convention.
- We do not allow Dirichlet conditions at interior vertices (Remark 5.4).
- ℓ_e is the length of the edge e, and L = Σ_e ℓ_e.
- The form domain is H = {f ∈ H¹(Γ) : f continuous on Γ, f = 0 at the leaves}, with form a(f) = ∫_Γ |f′|².
  The Laplacian −d²/dx² associated with a has discrete spectrum 0 < λ_1 ≤ λ_2 ≤ …, listed with
  multiplicity [BK13, Ku24].
- N(μ) is the number of eigenvalues ≤ μ and N⁻(μ) the number of eigenvalues < μ, both with multiplicity.
- Q_μ(f) = a(f) − μ‖f‖²_{L²}. By min-max, N⁻(μ) = n₋(Q_μ), the largest dimension of a subspace of H on
  which Q_μ is negative definite.

## 3. The "if" direction

Write ℓ_e = m_e L/k with integers m_e ≥ 1, so that Σ m_e = k. Cut each edge e into m_e segments of length
h = L/k. On each of the k segments J let φ_J(x) = sin(π(x − x_J)/h), where x_J is the left end of J, and
extend φ_J by 0 to the rest of Γ. Each φ_J is continuous and vanishes at every vertex, so φ_J ∈ H, and its
Rayleigh quotient is (π/h)² = (πk/L)².

The φ_J have disjoint supports, so they are orthogonal both in L² and for a. Their span is a k-dimensional
subspace on which a(f) ≤ (πk/L)²‖f‖², and min-max gives λ_k ≤ (πk/L)². Together with (1.6), which we
reprove in Step 3, this gives equality.

## 4. Proof of the bound and of the "only if" direction

The proof has four steps. Step 1 expresses N⁻(ω′²) through the inertia of a finite matrix M on the
interior vertices. Step 2 computes that inertia by eliminating vertices from the leaves upward, which
gives the angle formula (2). Step 3 rewrites ω′L/π − N⁻(ω′²) as a sum of vertex terms (3) and proves each
term positive, which gives (1.6). Step 4 takes the limit ω′ ↓ πk/L in (3) when equality holds.

### 4.1 Step 1: counting eigenvalues through vertex values

Fix ω′ > 0 with sin(ω′ℓ_e) ≠ 0 for every edge e, and put μ = ω′². Let V_int be the set of interior
vertices. We split H into two pieces:

- H_0 = {f ∈ H : f(v) = 0 at every vertex} = ⊕_e H¹_0(e);
- H_harm, the functions h with h″ = −μh on every edge. Such an h is determined by its values
  x ∈ ℝ^{V_int} at the interior vertices (it is 0 at the leaves); uniqueness uses sin(ω′ℓ_e) ≠ 0.

Every f ∈ H can be written as f = h + (f − h), where h ∈ H_harm takes the same vertex values as f, and
f − h ∈ H_0. The two pieces are Q_μ-orthogonal: for h ∈ H_harm and g ∈ H_0, integration by parts on each
edge gives

  ∫ h′g′ − μ∫ hg = Σ_e [h′g]_∂e − ∫ (h″ + μh) g = 0,

because g vanishes at the ends of every edge.

Negative indices add over a Q-orthogonal sum. For the inequality ≤, each summand has a Q-nonnegative
subspace whose codimension equals its index: in H_0 the closed span of the Dirichlet eigenfunctions with
eigenvalue ≥ μ, and in the finite-dimensional space H_harm one obtained by linear algebra. Their sum is
Q-nonnegative and has codimension n₋(Q|H_0) + n₋(Q|H_harm), so n₋(Q) ≤ n₋(Q|H_0) + n₋(Q|H_harm). For ≥,
if U_0 ⊂ H_0 and U_h ⊂ H_harm are Q-negative, then Q(u_0 + u_h) = Q(u_0) + Q(u_h) < 0 for
(u_0, u_h) ≠ 0, so U_0 ⊕ U_h is Q-negative.

On H_0 the index counts the Dirichlet eigenvalues (jπ/ℓ_e)² < μ of each edge, which number ⌊ω′ℓ_e/π⌋; the
case jπ = ω′ℓ_e is excluded by the choice of ω′. On H_harm we have Q_μ(h) = xᵀMx, where an edge with end
values a, b contributes

  ω′[(a² + b²) cot(ω′ℓ_e) − 2ab / sin(ω′ℓ_e)],

and the value at a leaf is 0. (We checked this integral symbolically; see Section 6.) Therefore

  **N⁻(ω′²) = Σ_e ⌊ω′ℓ_e/π⌋ + n₋(M).**   (1)

The remaining task is to compute n₋(M), the number of negative eigenvalues of M.

### 4.2 Step 2: elimination along the tree

Root Γ at a leaf ρ and orient every edge toward ρ. Each interior vertex c then has one parent edge e_c
and d_c child edges, with d_c ≥ 2 because deg c ≥ 3. Every edge except the *root edge* (the edge at ρ) is
a child edge of exactly one interior vertex, namely its upper end.

**Angles.** Define, from the leaves upward:
- s_e = 0 if the lower end of e is a leaf;
- t_e = s_e + ω′ℓ_e for every edge;
- if the lower end of e is an interior vertex c with child edges i, then s_e is the unique number in
  (0, π) with cot s_e = Σ_i cot t_i.

We call ω′ *generic* if sin(ω′ℓ_e) ≠ 0 and sin t_e ≠ 0 for every edge e. At a generic ω′ all the
cotangents above are finite.

**Elimination.** We eliminate the interior vertices from the leaves upward by symmetric Gaussian
elimination (LDLᵀ). We claim, by induction, that when c is eliminated its current diagonal entry is

  p_c = ω′(Σ_i cot t_i + cot ω′ℓ_{e_c}) = ω′(cot s_{e_c} + cot ω′ℓ_{e_c}) = ω′ sin t_{e_c} / (sin s_{e_c} sin ω′ℓ_{e_c}).

The last equality is the *pivot identity* cot s + cot x = sin(s + x)/(sin s sin x).

- Initially the diagonal entry of M at c is Σ_{e ∋ c} ω′ cot(ω′ℓ_e).
- A child edge i whose lower end is a leaf contributes ω′ cot ω′ℓ_i = ω′ cot t_i.
- If the lower end of i is an interior vertex c_i, eliminating c_i changes only the diagonal entry of c,
  because Γ is a tree. It subtracts (ω′/sin ω′ℓ_i)² / p_{c_i}. By the *Schur identity*

    cot x − 1/(sin²x (cot s + cot x)) = cot(s + x)   (x = ω′ℓ_i, s = s_i),

  child i then contributes ω′ cot t_i.

The off-diagonal entry from c to its parent is −ω′/sin ω′ℓ_{e_c}. The last vertex eliminated is the lower
end of the root edge; its parent ρ is a leaf and so is not a variable. All pivots are nonzero exactly when
ω′ is generic, and in that case Sylvester's law of inertia gives n₋(M) = #{c : p_c < 0}.

**From negative pivots to floors.** Let e = e_c and write ω′ℓ_e = nπ + r with n = ⌊ω′ℓ_e/π⌋ and
r ∈ (0, π). Then sin ω′ℓ_e = (−1)ⁿ sin r and sin t_e = (−1)ⁿ sin(s_e + r), while sin s_e > 0 and
s_e + r ∈ (0, 2π) ∖ {π}. The signs (−1)ⁿ cancel in p_c, so

  p_c < 0 ⇔ sin(s_e + r) < 0 ⇔ s_e + r > π ⇔ ⌊t_e/π⌋ = n + 1,

and otherwise ⌊t_e/π⌋ = n. Hence ⌊ω′ℓ_e/π⌋ + [p_c < 0] = ⌊t_e/π⌋. For an edge starting at a leaf,
t_e = ω′ℓ_e and the same formula holds with no pivot. Substituting into (1):

  **N⁻(ω′²) = Σ_e ⌊t_e/π⌋ for every generic ω′.**   (2)

**The exceptional set is discrete.** Steps 3 and 4 use (2) on whole intervals, so we need the
non-generic frequencies to be isolated. For an interior vertex c, let M_c be the principal submatrix of M
on c and its descendants. Elimination inside the subtree is the same process, so det M_c is the product of
the pivots of c and its descendants.

Let D_c(ω′) = det M_c · Π sin²(ω′ℓ_e), with the product over the edges of the subtree together with e_c.
Each entry of M_c has denominator sin(ω′ℓ_e) for an edge e at that vertex, and each such sine occurs to at
most the second power in any term of the determinant expansion. So D_c extends to a real-analytic (indeed
entire) function of ω′.

D_c is not identically zero. As ω′ ↓ 0 we have ω′ cot(ω′ℓ) → 1/ℓ and ω′/sin(ω′ℓ) → 1/ℓ, so M_c tends to a
weighted graph Laplacian grounded at the parent vertex and at the leaves, which is positive definite.
Hence det M_c > 0 for small ω′.

The set E = ∪_e {ω′ : sin(ω′ℓ_e) = 0} ∪ ∪_c {ω′ : D_c(ω′) = 0} is therefore discrete in (0, ∞). Off E,
induction from the leaves shows that every pivot is defined and nonzero, since p_c = det M_c / Π det M_{c′}
over the children c′ of c. So every ω′ ∉ E is generic.

### 4.3 Step 3: the vertex terms and the bound (1.6)

Put K(ω′) = ω′L/π = Σ_e (t_e − s_e)/π, and for generic ω′ let τ_e = t_e − π⌊t_e/π⌋ ∈ (0, π) be the angle
t_e reduced modulo π. By (2),

  π(K − N⁻) = Σ_e τ_e − Σ_e s_e = Σ_{c ∈ V_int} f_c + τ_root,   f_c := Σ_{i child of c} τ_i − s_{e_c}.   (3)

To group the terms this way we use that each edge other than the root edge is a child of exactly one
interior vertex, and that s_e = 0 when the lower end of e is a leaf. Since cot has period π,
cot s_{e_c} = Σ_i cot τ_i, so f_c depends only on the reduced child angles τ_i ∈ (0, π). It remains to show
f_c > 0.

**Vertex lemma.** Let d ≥ 2, τ ∈ (0, π)^d, and let s ∈ (0, π) be defined by cot s = Σ cot τ_i. Put
f(τ) = Σ τ_i − s. Then f(τ) > 0.

*Proof.* First let d = 2 and τ = (a, b). If a + b ≥ π, then s < π ≤ a + b. Suppose a + b < π, and put
c₁ = cot a, c₂ = cot b. Then c₁ + c₂ = sin(a + b)/(sin a sin b) > 0, and the addition formula for the
cotangent gives

  cot a + cot b − cot(a + b) = (c₁² + c₁c₂ + c₂² + 1)/(c₁ + c₂).

The numerator equals (c₁ + c₂/2)² + 3c₂²/4 + 1 > 0, so cot s = cot a + cot b > cot(a + b). Hence
sin(a + b − s) = sin s · sin(a + b) · (cot s − cot(a + b)) > 0, and since a + b − s ∈ (−π, π), this forces
a + b − s > 0.

For d ≥ 3, let s′ ∈ (0, π) be defined by cot s′ = Σ_{i≥2} cot τ_i. Then cot s = cot τ₁ + cot s′, and

  f(τ) = g(τ₁, s′) + (Σ_{i≥2} τ_i − s′),   g(a, b) := a + b − s(a, b),

where s(a, b) is the angle the case d = 2 assigns to (a, b). The bracket is f for the d − 1 ≥ 2 angles
τ₂, …, τ_d, which is positive by induction, and g(τ₁, s′) > 0 by the case d = 2. So f > 0. ∎

The induction has to start at d = 2: with a single child, s = τ₁ and f ≡ 0. This is where the absence of
degree-2 vertices is used (Remark 5.1).

**Proof of (1.6).** By (3) and the lemma, K(ω′) > N⁻(ω′²) for every generic ω′. Suppose λ_k < (πk/L)².
Choose a generic ω′ with λ_k < ω′² < (πk/L)²; this is possible because E is discrete. Then
N⁻(ω′²) ≥ k > K(ω′), a contradiction.

For Step 4 we also need f on the boundary of the cube. Extend s, and hence f, to [0, π)^d by setting
s = 0 whenever some τ_i = 0. The extension is continuous: as τ_j → 0⁺, cot τ_j → +∞ while the other
cot τ_i stay bounded below (because τ_i < π − δ near the limit point), so Σ cot τ_i → +∞ and s → 0. On the
boundary f = Σ τ_i. Together with the lemma this shows

  **on [0, π)^d, f(τ) = 0 if and only if τ = 0.**   (4)

### 4.4 Step 4: the equality case

Let ω = πk/L and suppose λ_k = ω². Then N(ω²) ≥ k. Choose ε > 0 so that the interval J = (ω, ω + ε)
contains no point of E and no eigenvalue lies in (ω², (ω + ε)²).

**The angles are monotone on J.** Every s_e and t_e is continuous on J. We show by induction from the
leaves that t_e is strictly increasing on J and that s_e is nondecreasing (identically 0 for an edge
starting at a leaf, strictly increasing otherwise). For an edge starting at a leaf, s_e ≡ 0 and
t_e = ω′ℓ_e. At an interior vertex, each child angle t_i is continuous and never meets πℤ on J, so it stays
in one interval (mπ, (m+1)π). There cot t_i is strictly decreasing, so Σ cot t_i is strictly decreasing.
Since arccot: ℝ → (0, π) is decreasing, s_e is strictly increasing, and so is t_e = s_e + ω′ℓ_e.

Consequently ⌊t_e/π⌋ = m_e is constant on J and τ_e = t_e − πm_e is strictly increasing. Since s_e and
τ_e take values in [0, π), their right limits s_e⁺ and τ_e⁺ as ω′ ↓ ω exist and lie in [0, π).

**Passing to the limit.** For ω′ ∈ J we have N⁻(ω′²) = N(ω²) ≥ k, so by (3)

  Σ_c f_c + τ_root = π(K(ω′) − N⁻(ω′²)) ≤ π(K(ω′) − k) = (ω′ − ω)L → 0.

Every term on the left is ≥ 0, so each tends to 0. By continuity of f_c on [0, π)^{d_c}, f_c(τ⁺) = 0, and
(4) gives τ_i⁺ = 0 for every child edge i. Every edge other than the root edge is a child edge, and
τ_root⁺ = 0 directly, so τ_e⁺ = 0 for every edge.

Next, s_e⁺ = 0 for every edge. This is immediate for edges starting at a leaf. For the others, the child
angles τ_i decrease to 0 as ω′ ↓ ω, so Σ cot τ_i → +∞ and s_e → 0.

Finally, letting ω′ ↓ ω in τ_e = s_e + ω′ℓ_e − πm_e gives 0 = ωℓ_e − πm_e, that is,
ℓ_e = m_e π/ω = m_e L/k, and m_e ≥ 1 because ℓ_e > 0. This proves the Theorem. ∎

## 5. Remarks on the hypotheses

**5.1 Degree-2 vertices.** The convention of Section 2 is necessary. Put a degree-2 vertex at a point x
of the interval [0, L] with x/L irrational. The operator does not change, so λ_k = (πk/L)² for every k,
but the two edges have lengths x and L − x, which are not multiples of L/k for any k. In the proof a
degree-2 vertex has one child, so its term in (3) is f ≡ 0 and Step 4 gives no information at that
vertex. The Theorem applies to the tree obtained by merging the two edges at each such vertex, which is the
reading in [HKR].

**5.2 Multiple eigenvalues and eigenfunctions vanishing at vertices.** Many arguments on quantum graphs,
for example nodal counts [Be08, Ba14], assume that the eigenvalue is simple and that its eigenfunction
does not vanish at any vertex. Such an assumption would be useless here, because the trees with equality
are far from generic: on an equilateral star with d ≥ 3 edges of length h, the eigenvalue (π/h)² has
multiplicity d − 1 and its eigenfunctions vanish at the centre. The proof avoids the issue because it never
looks at eigenfunctions. It uses only the counting function N⁻, which counts multiplicity, and evaluates
it at frequencies ω′ where formula (2) holds.

**5.3 Why only generic ω′ are used.** At a non-generic ω′ some pivot vanishes or some angle is
undefined, and (2) need not hold. Since πk/L itself is usually non-generic in the equality case, we never
evaluate at it. We use (2) on an interval J to the right of πk/L and take a one-sided limit. The limit
is taken from the right because there N⁻(ω′²) = N(ω²) counts the eigenvalue ω² = λ_k; from the left it
would not.

**5.4 Dirichlet conditions at interior vertices.** [HKR, Prop. 1.9] also considers Dirichlet conditions
at interior vertices. Such graphs are outside the class of the Theorem: a Dirichlet vertex decouples
the graph into pieces, each of which is a Dirichlet tree.

**5.5 The interval.** If Γ is a single edge, there are no interior vertices, (2) is the classical count
N⁻(ω′²) = ⌊ω′L/π⌋, and (3) reduces to π(K − N⁻) = τ_root. The Theorem then says that λ_k = (πk/L)² for every
k, which is true, since L is a multiple of L/k.

## 6. Computer checks

The checks below test individual steps of the proof and the statement of the Theorem. They are evidence,
not part of the proof. Paths are relative to this repository; the scripts need Python ≥ 3.12 and the
packages in `requirements.txt`.

**Table 1. Computer checks and the steps they test.**

| Script (log) | What it computes | Step it tests | Outcome |
|---|---|---|---|
| `scripts/check_identities.py` (`logs/identities.log`) | Symbolic simplification (sympy) of the edge-form integral, the Schur and pivot identities and the algebraic identity in the vertex lemma; a grid evaluation of g | Steps 1–3 | All four identities reduce to 0; g > 0 on the grid |
| `scripts/test1.py` (`logs/test1.log`) | For 300 random trees at random ω′, the angle count Σ⌊t_e/π⌋ against an eigenvalue count computed independently from the inertia of the Dirichlet-to-Neumann matrix (mpmath, 30 digits); also identity (3), a finite-element count on samples, and the equilateral-star values in [HKR] | Formula (2), identity (3) | No disagreements; K − N⁻ > 0 throughout |
| `scripts/test2.py 11 <trials>` (`logs/test2_seed11.log`) | Search for counterexamples among trees with rational edge lengths, k = 1, …, 6, eigenvalues counted at 60 digits | The Theorem | 16,008 cases, 1,339 with equality, all with every edge a multiple of L/k; (1.6) never failed |
| `independent-checks/*.py` | A separate implementation (first check in [CHECKS.md](CHECKS.md)) sharing no code with `scripts/`: star families, H-shaped trees, random trees | Formula (2) and the Theorem | Agrees with the above; equality exactly when all edges are multiples of L/k |

The symbolic checks confirm the algebra used in Steps 1–3; the pivot, Schur and vertex identities are
also proved in Lean (Section 7). The numerical checks test formula (2), which rests on the standard facts
in Step 1 and the elimination in Step 2, against an eigenvalue count that does not use angles at all.

## 7. Lean formalization

The directory `lean/` contains a Lean 4 (v4.37.0-rc1) and Mathlib formalization of Steps 3–4 in two files.

**`DirichletTreeCore.lean`** proves Steps 3–4 in their finite-dimensional form, with no `sorry`, no
`native_decide` and no added axioms.

- A rooted tree is modelled by `RTree`: an edge together with the subtree below it, where the leaves are
  Dirichlet leaves. `WF` says that lengths are positive and every interior vertex has at least two
  children, so there are no degree-2 vertices. The angles `sAng`, `tAng` are those of Section 4.2, with
  `arccot y := π/2 − arctan y`; `Generic` and `floorSum` = Σ_e ⌊t_e/π⌋ are as in the text.
- Proved: `vertex_lemma` (any d ≥ 2), `key_identity` (identity (3)), `key_inequality`
  (Σ_e ⌊t_e/π⌋ < ωL/π for generic ω), and `equality_core` (Step 4: if every ω in (πk/L, πk/L + ε) is
  generic and Σ_e ⌊t_e/π⌋ ≥ k there, then every edge is a positive integer multiple of L/k).
- The spectral facts enter as an explicit hypothesis `SpectralInput T lam` on a sequence `lam`: it is
  monotone, has finitely many terms below any level, satisfies the counting formula (2) at generic ω, and
  every ω₀ ≥ 0 has an interval of generic frequencies to its right (the discreteness of E). From this Lean
  derives `SpectralInput.polya_bound`, which is (1.6), and `SpectralInput.equality_iff`, which is the
  Theorem in both directions.
- `#print axioms` for the five main results gives `[propext, Classical.choice, Quot.sound]`.

Not formalized: the content of `SpectralInput`, that is, min-max on H¹ of a metric graph, Step 1, the
inertia argument of Step 2, and the correspondence between `RTree` and a graph model. Mathlib has no
spectral theory of quantum graphs. These facts are proved in Sections 4.1–4.2, and formula (2) was tested
numerically against independent eigenvalue counts (Section 6).

**`QuantumGraphEquality.lean`** is an earlier and more literal statement of the problem on `SimpleGraph`
trees, with λ_k defined by min-max over edgewise Lipschitz functions. It proves the pivot, Schur and
cotangent identities and the two-child vertex lemma; its main theorem is left as `sorry` and is superseded
by the file above.

## 8. Prior work and open questions

On 26 November 2026 we searched arXiv (the source paper is still at version 1), the citations of
arXiv:2603.26172 in Semantic Scholar (there were none), Zenodo, and the main public collections of
AI-assisted solutions of open problems. We found no earlier solution of Open Problem 1.12(3). The
techniques used here are standard for quantum graphs, so an equivalent argument may already exist, for
instance in work on surgery principles [BKKM19] or nodal counts [Be08]; we would be grateful for
references.

A natural next question is the case of equality in the general bound of [BKKM17, Thm 4.7], which allows
Neumann leaves and cycles: λ_k ≥ (k − N + β/2)²π²/L², where N is the number of Neumann leaves and β the
number of independent cycles [HKR, after Remark 1.7].

## References

- [Ba14] R. Band, The nodal count {0, 1, 2, 3, …} implies the graph is a tree, *Phil. Trans. R. Soc. A* 372
  (2014), 20120504.
- [Be08] G. Berkolaiko, A lower bound for nodal count on discrete and metric graphs, *Comm. Math. Phys.* 278
  (2008), 803–819.
- [BK13] G. Berkolaiko and P. Kuchment, *Introduction to Quantum Graphs*, Mathematical Surveys and
  Monographs 186, AMS, 2013.
- [BKKM17] G. Berkolaiko, J. B. Kennedy, P. Kurasov and D. Mugnolo, Edge connectivity and the spectral gap
  of combinatorial and quantum graphs, *J. Phys. A* 50 (2017), 365201.
- [BKKM19] G. Berkolaiko, J. B. Kennedy, P. Kurasov and D. Mugnolo, Surgery principles for the spectral
  analysis of quantum graphs, *Trans. Amer. Math. Soc.* 372 (2019), 5153–5197.
- [HKR] E. M. Harrell II, J. B. Kennedy and G. J. Ramos, Bounds on eigenvalue ratios of quantum graph
  Laplacians, arXiv:2603.26172v1 (2026).
- [Ku24] P. Kurasov, *Spectral Geometry of Graphs*, Operator Theory: Advances and Applications 293,
  Birkhäuser, 2024.
