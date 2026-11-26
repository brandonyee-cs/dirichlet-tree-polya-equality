import Mathlib

/-!
# Equality in the Pólya-type bound for Dirichlet trees (Harrell–Kennedy–Ramos, Open Problem 1.12(3))

Source: E. M. Harrell II, J. B. Kennedy, G. J. Ramos, *Bounds on eigenvalue ratios of quantum
graph Laplacians*, arXiv:2603.26172v1 (2026), Remark 1.7, eq. (1.6), and Open Problem 1.12(3):

> Characterize the case of equality in the Pólya-type bound (1.6), `λ_k(Γ) ≥ π²k²/L²`, for all
> `k ≥ 1` and all Dirichlet trees `Γ` of total length `L`. Is it true that there is equality if and
> only if all edges of `Γ` have length equal to an integer multiple of `L/k`?

## Modelling choices (Mathlib has no spectral theory of quantum graphs)

* A Dirichlet tree is a finite combinatorial tree (`SimpleGraph.IsTree` on `Fin n`, `n ≥ 2`) with
  positive edge lengths, Dirichlet conditions at the degree-one vertices and (implicitly, through
  the variational formulation) Kirchhoff conditions elsewhere. As in the paper, degree-2 vertices
  are suppressed (`no_deg_two`); otherwise "edge" in the conclusion would refer to the merged edges.
* Each edge `{u,v}` with `u < v` is the interval `[0, ℓ]`, `0 ↦ u`, `ℓ ↦ v`; a function on `Γ` is a
  family `f e : ℝ → ℝ`, set to `0` outside `[0, ℓ_e]`.
* **Simplification:** instead of the form domain `H¹` we use edgewise *Lipschitz* functions
  (`W^{1,∞}`), continuous at vertices (common vertex values `φ`) and vanishing at leaves. Lipschitz
  functions are dense in `H¹` for the form norm, i.e. form a *form core*, so the min-max values
  below coincide with the eigenvalues of the self-adjoint Laplacian; this identification is standard
  but is **not** proved here. The derivative is Mathlib's `deriv` (equal a.e. to the weak derivative
  by Rademacher's theorem).
* `lam Γ k` is the Courant–Fischer min-max value
  `inf_{dim V = k} sup_{0 ≠ f ∈ V} (∫|f'|²)/(∫|f|²)`, written without division.

## Contents
* Definitions, the Pólya bound (1.6) (`PolyaBound`, left as `sorry`; see [BKKM17, Thm 4.7] or
  PROOF.md, Section 4.3), and the open problem `OpenProblem_1_12_3` as a `Prop`; the theorem
  `openProblem_1_12_3` (left as `sorry`; `DirichletTreeCore.lean` proves Steps 3–4).
* **Proved:** the elementary identities used in the proof (pivot identity, Schur-complement
  identity, cotangent addition, the algebraic vertex identity and its positivity) and the
  **two-child vertex lemma** `vertex_lemma` (`a + b > s` when `cot s = cot a + cot b`).
-/

open Real

namespace QuantumGraphEquality

open Classical in
/-- A compact Dirichlet tree with suppressed degree-2 vertices. -/
structure DirichletTree where
  /-- number of vertices -/
  n : ℕ
  /-- the underlying combinatorial tree -/
  G : SimpleGraph (Fin n)
  isTree : G.IsTree
  two_le : 2 ≤ n
  /-- edge lengths, read on ordered pairs `(u, v)` with `u < v` adjacent -/
  len : Fin n × Fin n → ℝ
  len_pos : ∀ u v, G.Adj u v → u < v → 0 < len (u, v)
  /-- degree-2 vertices are suppressed -/
  no_deg_two : ∀ v, (Finset.univ.filter (G.Adj v)).card ≠ 2

namespace DirichletTree

variable (Γ : DirichletTree)

/-- Edges of `Γ`, each oriented from its smaller to its larger endpoint. -/
def Edge : Type := {p : Fin Γ.n × Fin Γ.n // Γ.G.Adj p.1 p.2 ∧ p.1 < p.2}

noncomputable instance : Fintype Γ.Edge := by unfold Edge; classical infer_instance

/-- Length of an edge. -/
def ℓ (e : Γ.Edge) : ℝ := Γ.len e.1

open Classical in
/-- Leaves (degree-one vertices), which carry the Dirichlet condition. -/
def IsLeaf (v : Fin Γ.n) : Prop := (Finset.univ.filter (Γ.G.Adj v)).card = 1

/-- Total length `L = |Γ|`. -/
noncomputable def L : ℝ := ∑ e, Γ.ℓ e

/-- Functions on `Γ`: one real function per edge (parametrised on `[0, ℓ_e]`). -/
abbrev Fn : Type := Γ.Edge → ℝ → ℝ

/-- Admissible functions (a form core of the Dirichlet–Kirchhoff Laplacian): edgewise Lipschitz,
zero outside `[0, ℓ_e]`, continuous at every vertex, zero at the leaves. -/
def Admissible (f : Γ.Fn) : Prop :=
  (∀ e, ∃ K, LipschitzOnWith K (f e) (Set.Icc 0 (Γ.ℓ e))) ∧
  (∀ e x, x ∉ Set.Icc 0 (Γ.ℓ e) → f e x = 0) ∧
  ∃ φ : Fin Γ.n → ℝ, (∀ v, Γ.IsLeaf v → φ v = 0) ∧
    ∀ e, f e 0 = φ e.1.1 ∧ f e (Γ.ℓ e) = φ e.1.2

/-- Dirichlet energy `∫_Γ |f'|²`. -/
noncomputable def energy (f : Γ.Fn) : ℝ := ∑ e, ∫ x in (0)..(Γ.ℓ e), (deriv (f e) x) ^ 2

/-- `∫_Γ |f|²`. -/
noncomputable def mass (f : Γ.Fn) : ℝ := ∑ e, ∫ x in (0)..(Γ.ℓ e), (f e x) ^ 2

/-- The `k`-th eigenvalue (with multiplicity, `k ≥ 1`) via Courant–Fischer min-max. -/
noncomputable def lam (k : ℕ) : ℝ :=
  sInf {Λ : ℝ | ∃ V : Submodule ℝ Γ.Fn, (∀ f ∈ V, Γ.Admissible f) ∧ Module.finrank ℝ V = k ∧
    ∀ f ∈ V, f ≠ 0 → Γ.energy f ≤ Λ * Γ.mass f}

end DirichletTree

open DirichletTree

/-- The Pólya-type bound (1.6) of HKR, Remark 1.7: `λ_k(Γ) ≥ π² k² / L²`. -/
def PolyaBound : Prop := ∀ (Γ : DirichletTree) (k : ℕ), 1 ≤ k → (π * k / Γ.L) ^ 2 ≤ Γ.lam k

/-- **HKR Open Problem 1.12(3)** (with the conjectured answer): equality in (1.6) holds iff every
edge length is a (positive) integer multiple of `L/k`. -/
def OpenProblem_1_12_3 : Prop :=
  ∀ (Γ : DirichletTree) (k : ℕ), 1 ≤ k →
    (Γ.lam k = (π * k / Γ.L) ^ 2 ↔ ∀ e : Γ.Edge, ∃ m : ℕ, 0 < m ∧ Γ.ℓ e = m * (Γ.L / k))

/-- (1.6). `sorry`: needs the identification of `lam` with the spectrum and the Prüfer-angle
argument of PROOF.md, Section 4.3 (or [BKKM17, Thm 4.7]); not formalised. -/
theorem polyaBound : PolyaBound := by
  sorry

/-- **Main theorem** (PROOF.md, Section 1): the answer to Open Problem 1.12(3) is yes, for every `k ≥ 1`.
`sorry`: the proof uses the Dirichlet-to-Neumann index formula, tree elimination with Prüfer
angles, the vertex lemma below, and a one-sided limit argument; formalising it needs Sobolev
spaces on metric graphs, min-max for unbounded self-adjoint operators and Sylvester's law of
inertia for the resulting forms, none of which is available for quantum graphs in Mathlib. -/
theorem openProblem_1_12_3 : OpenProblem_1_12_3 := by
  sorry

/-! ## Elementary lemmas used in the proof (all proved) -/

/-- Pivot identity: `cot s + cot x = sin (s + x) / (sin s · sin x)`. -/
theorem pivot_identity (s x : ℝ) (hs : sin s ≠ 0) (hx : sin x ≠ 0) :
    cot s + cot x = sin (s + x) / (sin s * sin x) := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_add]
  field_simp
  ring

/-- Schur-complement identity: eliminating a vertex whose subtree carries the angle `s` turns
`cot x` (`x = ω ℓ`) into `cot (s + x)`:
`cot x - 1 / (sin² x · (cot s + cot x)) = cot (s + x)`. -/
theorem schur_identity (s x : ℝ) (hs : sin s ≠ 0) (hx : sin x ≠ 0) (hsx : sin (s + x) ≠ 0) :
    cot x - 1 / (sin x ^ 2 * (cot s + cot x)) = cot (s + x) := by
  rw [pivot_identity s x hs hx, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
  have h1 : sin (s + x) = sin s * cos x + cos s * sin x := sin_add s x
  have h2 : cos (s + x) = cos s * cos x - sin s * sin x := cos_add s x
  field_simp
  rw [h1, h2]
  have := sin_sq_add_cos_sq x
  linear_combination (sin s) * this

/-- Cotangent addition: `cot (a + b) = (cot a cot b - 1) / (cot a + cot b)`. -/
theorem cot_add' (a b : ℝ) (ha : sin a ≠ 0) (hb : sin b ≠ 0) (hab : sin (a + b) ≠ 0) :
    cot (a + b) = (cot a * cot b - 1) / (cot a + cot b) := by
  have hsum : cot a + cot b ≠ 0 := by
    rw [pivot_identity a b ha hb]; exact div_ne_zero hab (mul_ne_zero ha hb)
  rw [eq_div_iff hsum, pivot_identity a b ha hb, cot_eq_cos_div_sin, cot_eq_cos_div_sin,
    cot_eq_cos_div_sin, cos_add]
  field_simp

/-- Algebraic vertex identity: with `c₁ = cot a`, `c₂ = cot b`,
`c₁ + c₂ - (c₁c₂ - 1)/(c₁ + c₂) = (c₁² + c₁c₂ + c₂² + 1)/(c₁ + c₂)`. -/
theorem vertex_identity (c₁ c₂ : ℝ) (h : c₁ + c₂ ≠ 0) :
    c₁ + c₂ - (c₁ * c₂ - 1) / (c₁ + c₂) = (c₁ ^ 2 + c₁ * c₂ + c₂ ^ 2 + 1) / (c₁ + c₂) := by
  field_simp
  ring

theorem vertex_numerator_pos (c₁ c₂ : ℝ) : 0 < c₁ ^ 2 + c₁ * c₂ + c₂ ^ 2 + 1 := by
  nlinarith [sq_nonneg (c₁ + c₂), sq_nonneg c₁, sq_nonneg c₂]

/-- **Vertex lemma (two children).** If `a, b, s ∈ (0, π)` and `cot s = cot a + cot b`, then
`s < a + b`, i.e. `g(a,b) = a + b - s > 0`. -/
theorem vertex_lemma (a b s : ℝ) (ha : 0 < a) (ha' : a < π) (hb : 0 < b) (hb' : b < π)
    (hs : 0 < s) (hs' : s < π) (hcot : cot s = cot a + cot b) : s < a + b := by
  by_cases hab : π ≤ a + b
  · linarith
  push Not at hab
  have sa : 0 < sin a := sin_pos_of_pos_of_lt_pi ha ha'
  have sb : 0 < sin b := sin_pos_of_pos_of_lt_pi hb hb'
  have ss : 0 < sin s := sin_pos_of_pos_of_lt_pi hs hs'
  have sab : 0 < sin (a + b) := sin_pos_of_pos_of_lt_pi (by linarith) hab
  -- `cot a + cot b > 0` and `cot (a+b) < cot a + cot b`
  have hsum : cot a + cot b = sin (a + b) / (sin a * sin b) := pivot_identity a b sa.ne' sb.ne'
  have hsum_pos : 0 < cot a + cot b := by rw [hsum]; positivity
  have hlt : cot (a + b) < cot a + cot b := by
    rw [cot_add' a b sa.ne' sb.ne' sab.ne']
    have key := vertex_identity (cot a) (cot b) hsum_pos.ne'
    have hpos : 0 < (cot a ^ 2 + cot a * cot b + cot b ^ 2 + 1) / (cot a + cot b) :=
      div_pos (vertex_numerator_pos _ _) hsum_pos
    linarith
  -- `sin (a + b - s) = sin s · sin (a+b) · (cot s - cot (a+b)) > 0`
  have hsin : sin (a + b - s) = sin s * sin (a + b) * (cot s - cot (a + b)) := by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_sub]
    field_simp
  have hpos : 0 < sin (a + b - s) := by
    rw [hsin]; apply mul_pos (mul_pos ss sab); linarith
  by_contra hle
  push Not at hle
  have := sin_nonpos_of_nonpos_of_neg_pi_le (x := a + b - s) (by linarith) (by linarith)
  linarith

end QuantumGraphEquality
