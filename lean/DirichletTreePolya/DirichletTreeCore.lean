import Mathlib

/-!
# Dirichlet trees: the elementary core of the equality case in λ_k ≥ (πk/L)²

Formalizes Steps 2–4 of `publish/dirichlet-tree-polya-equality/PROOF.md` (Harrell–Kennedy–Ramos,
Open Problem 1.12(3)) in the finite-dimensional "Prüfer angle" form. Everything is proved
(no `sorry`); the spectral input is an explicit hypothesis `SpectralInput` (Part 6).

* `RTree`: finite tree rooted at a Dirichlet leaf; `WF`: lengths `> 0`, interior vertices have
  `≥ 2` children (no degree-2 vertices). `sAng`, `tAng`: angles `s_e`, `t_e = s_e + ωℓ_e`,
  with `s_e = arccot (Σ cot t_i)` at interior vertices. `Generic`: `sin (ωℓ_e) ≠ 0 ≠ sin t_e`.
* (a) `vertex_lemma`: `d ≥ 2`, `τ ∈ (0,π)^d` ⇒ `Σ τ_i - arccot (Σ cot τ_i) > 0`.
* `key_identity`: identity (3), `ωL - π Σ_e ⌊t_e/π⌋ = τ_root + Σ_c f_c`.
* (b) `key_inequality`: generic `ω` ⇒ `Σ_e ⌊t_e/π⌋ < ωL/π`.
* (c) `equality_core`: if `(πk/L, πk/L + ε)` is generic and `Σ_e ⌊t_e/π⌋ ≥ k` there, every
  `ℓ_e` is a positive integer multiple of `L/k`.
* (b') `SpectralInput.polya_bound`, (c') `SpectralInput.equality_iff` (both directions).
-/

open Real Set Filter Topology

namespace DirichletTreeCore

/-! ## Part 0. `arccot`, reduced angles, cotangent facts -/

/-- `arccot : ℝ → (0, π)`, the inverse of `cot` on `(0, π)`. -/
noncomputable def arccot (y : ℝ) : ℝ := π / 2 - arctan y

theorem arccot_pos (y : ℝ) : 0 < arccot y := by
  unfold arccot; linarith [arctan_lt_pi_div_two y]

theorem arccot_lt_pi (y : ℝ) : arccot y < π := by
  unfold arccot; linarith [neg_pi_div_two_lt_arctan y]

theorem arccot_strictAnti : StrictAnti arccot := by
  intro a b h; unfold arccot; linarith [arctan_strictMono h]

theorem continuous_arccot : Continuous arccot := continuous_const.sub continuous_arctan

theorem cot_eq_neg_tan (x : ℝ) : cot x = -tan (x - π / 2) := by
  rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, sin_sub_pi_div_two, cos_sub_pi_div_two]
  ring

theorem cot_arccot (y : ℝ) : cot (arccot y) = y := by
  rw [cot_eq_neg_tan]; unfold arccot
  rw [show π / 2 - arctan y - π / 2 = -arctan y by ring, tan_neg, tan_arctan, neg_neg]

theorem arccot_cot {x : ℝ} (h0 : 0 < x) (h1 : x < π) : arccot (cot x) = x := by
  rw [cot_eq_neg_tan]; unfold arccot
  rw [arctan_neg, arctan_tan (by linarith) (by linarith)]; ring

theorem cot_strictAntiOn : StrictAntiOn cot (Ioo 0 π) := by
  intro x hx y hy hxy
  rw [cot_eq_neg_tan, cot_eq_neg_tan, neg_lt_neg_iff]
  exact strictMonoOn_tan ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)

theorem cot_sub_int_mul_pi (x : ℝ) (n : ℤ) : cot (x - n * π) = cot x := by
  rw [cot_eq_neg_tan, cot_eq_neg_tan,
    show x - n * π - π / 2 = (x - π / 2) - n * π by ring, tan_periodic.sub_int_mul_eq]

theorem continuousAt_cot {x : ℝ} (hx : sin x ≠ 0) : ContinuousAt cot x := by
  have : cot = fun y => cos y / sin y := funext fun y => cot_eq_cos_div_sin y
  rw [this]; exact continuous_cos.continuousAt.div continuous_sin.continuousAt hx

/-- Reduced angle `τ(x) = x - π ⌊x/π⌋ ∈ [0, π)`. -/
noncomputable def red (x : ℝ) : ℝ := x - π * ⌊x / π⌋

theorem red_nonneg (x : ℝ) : 0 ≤ red x := by
  unfold red
  have h := Int.floor_le (x / π)
  have : (⌊x / π⌋ : ℝ) * π ≤ x := by rwa [le_div_iff₀ pi_pos] at h
  linarith

theorem red_lt_pi (x : ℝ) : red x < π := by
  unfold red
  have h := Int.lt_floor_add_one (x / π)
  have : x < ((⌊x / π⌋ : ℝ) + 1) * π := by rwa [div_lt_iff₀ pi_pos] at h
  linarith

theorem red_pos {x : ℝ} (hx : sin x ≠ 0) : 0 < red x := by
  rcases (red_nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso; apply hx
    have : x = (⌊x / π⌋ : ℤ) * π := by unfold red at h; linarith
    rw [this, sin_int_mul_pi]

theorem cot_red (x : ℝ) : cot (red x) = cot x := by
  unfold red; rw [show x - π * ⌊x / π⌋ = x - (⌊x / π⌋ : ℤ) * π by ring, cot_sub_int_mul_pi]

/-! ## Part 1. Vertex lemma -/

/-- Pivot identity: `cot s + cot x = sin (s + x) / (sin s · sin x)`. -/
theorem pivot_identity (s x : ℝ) (hs : sin s ≠ 0) (hx : sin x ≠ 0) :
    cot s + cot x = sin (s + x) / (sin s * sin x) := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_add]
  field_simp
  ring

/-- Cotangent addition: `cot (a + b) = (cot a cot b - 1) / (cot a + cot b)`. -/
theorem cot_add' (a b : ℝ) (ha : sin a ≠ 0) (hb : sin b ≠ 0) (hab : sin (a + b) ≠ 0) :
    cot (a + b) = (cot a * cot b - 1) / (cot a + cot b) := by
  have hsum : cot a + cot b ≠ 0 := by
    rw [pivot_identity a b ha hb]; exact div_ne_zero hab (mul_ne_zero ha hb)
  rw [eq_div_iff hsum, pivot_identity a b ha hb, cot_eq_cos_div_sin, cot_eq_cos_div_sin,
    cot_eq_cos_div_sin, cos_add]
  field_simp

theorem vertex_identity (c₁ c₂ : ℝ) (h : c₁ + c₂ ≠ 0) :
    c₁ + c₂ - (c₁ * c₂ - 1) / (c₁ + c₂) = (c₁ ^ 2 + c₁ * c₂ + c₂ ^ 2 + 1) / (c₁ + c₂) := by
  field_simp
  ring

theorem vertex_numerator_pos (c₁ c₂ : ℝ) : 0 < c₁ ^ 2 + c₁ * c₂ + c₂ ^ 2 + 1 := by
  nlinarith [sq_nonneg (c₁ + c₂), sq_nonneg c₁, sq_nonneg c₂]

/-- **Vertex lemma, two children** (copied from `QuantumGraphEquality.lean`). -/
theorem vertex_lemma2 (a b s : ℝ) (ha : 0 < a) (ha' : a < π) (hb : 0 < b) (hb' : b < π)
    (hs : 0 < s) (hs' : s < π) (hcot : cot s = cot a + cot b) : s < a + b := by
  by_cases hab : π ≤ a + b
  · linarith
  push Not at hab
  have sa : 0 < sin a := sin_pos_of_pos_of_lt_pi ha ha'
  have sb : 0 < sin b := sin_pos_of_pos_of_lt_pi hb hb'
  have ss : 0 < sin s := sin_pos_of_pos_of_lt_pi hs hs'
  have sab : 0 < sin (a + b) := sin_pos_of_pos_of_lt_pi (by linarith) hab
  have hsum : cot a + cot b = sin (a + b) / (sin a * sin b) := pivot_identity a b sa.ne' sb.ne'
  have hsum_pos : 0 < cot a + cot b := by rw [hsum]; positivity
  have hlt : cot (a + b) < cot a + cot b := by
    rw [cot_add' a b sa.ne' sb.ne' sab.ne']
    have key := vertex_identity (cot a) (cot b) hsum_pos.ne'
    have hpos : 0 < (cot a ^ 2 + cot a * cot b + cot b ^ 2 + 1) / (cot a + cot b) :=
      div_pos (vertex_numerator_pos _ _) hsum_pos
    linarith
  have hsin : sin (a + b - s) = sin s * sin (a + b) * (cot s - cot (a + b)) := by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_sub]
    field_simp
  have hpos : 0 < sin (a + b - s) := by
    rw [hsin]; apply mul_pos (mul_pos ss sab); linarith
  by_contra hle
  push Not at hle
  have := sin_nonpos_of_nonpos_of_neg_pi_le (x := a + b - s) (by linarith) (by linarith)
  linarith

theorem vertex_lemma_aux (n : ℕ) (τ : Fin (n + 2) → ℝ) (h0 : ∀ i, 0 < τ i) (h1 : ∀ i, τ i < π) :
    arccot (∑ i, cot (τ i)) < ∑ i, τ i := by
  induction n with
  | zero =>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    exact vertex_lemma2 _ _ _ (h0 0) (h1 0) (h0 _) (h1 _) (arccot_pos _) (arccot_lt_pi _)
      (cot_arccot _)
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := τ)]
    set s' := arccot (∑ i : Fin (n + 2), cot (τ i.succ))
    have hs' : cot s' = ∑ i : Fin (n + 2), cot (τ i.succ) := cot_arccot _
    have h2 := vertex_lemma2 (τ 0) s' (arccot (cot (τ 0) + ∑ i : Fin (n + 2), cot (τ i.succ)))
      (h0 0) (h1 0) (arccot_pos _) (arccot_lt_pi _) (arccot_pos _) (arccot_lt_pi _)
      (by rw [cot_arccot, hs'])
    have h3 := ih (fun i => τ i.succ) (fun i => h0 _) (fun i => h1 _)
    linarith

/-- **(a) General-`d` vertex lemma.** For `d ≥ 2` and `τ ∈ (0, π)^d`,
`Σ τ_i - arccot (Σ cot τ_i) > 0`. -/
theorem vertex_lemma {d : ℕ} (hd : 2 ≤ d) (τ : Fin d → ℝ) (h0 : ∀ i, 0 < τ i)
    (h1 : ∀ i, τ i < π) : 0 < ∑ i, τ i - arccot (∑ i, cot (τ i)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  linarith [vertex_lemma_aux n τ h0 h1]

/-! ## Part 2. Rooted trees and Prüfer angles -/

/-- A finite tree rooted at a Dirichlet leaf `ρ`, described edge-by-edge from the root edge down.
A term `T : RTree` represents an edge (its *top edge*, of length `T.len`) together with
everything hanging below it:
* `leaf ℓ`: an edge of length `ℓ` whose lower end is a Dirichlet leaf;
* `node ℓ d cs`: an edge of length `ℓ` whose lower end is an interior (Kirchhoff) vertex with `d`
  child edges/subtrees `cs i`.
The whole Dirichlet tree is a `T : RTree` whose top edge is the edge at the root leaf `ρ`. -/
inductive RTree : Type
  | leaf (ℓ : ℝ) : RTree
  | node (ℓ : ℝ) (d : ℕ) (cs : Fin d → RTree) : RTree

namespace RTree

/-- Length of the top edge. -/
def len : RTree → ℝ
  | leaf ℓ => ℓ
  | node ℓ _ _ => ℓ

/-- Sum of `g` over all edges (each edge is identified with the subtree it is the top edge of). -/
noncomputable def esum (g : RTree → ℝ) : RTree → ℝ
  | leaf ℓ => g (leaf ℓ)
  | node ℓ d cs => g (node ℓ d cs) + ∑ i, esum g (cs i)

/-- Sum of `g` over all interior vertices (identified with the subtree whose top edge is the
vertex's parent edge). -/
noncomputable def vsum (g : RTree → ℝ) : RTree → ℝ
  | leaf _ => 0
  | node ℓ d cs => g (node ℓ d cs) + ∑ i, vsum g (cs i)

/-- `P` holds for every edge. -/
def eall (P : RTree → Prop) : RTree → Prop
  | leaf ℓ => P (leaf ℓ)
  | node ℓ d cs => P (node ℓ d cs) ∧ ∀ i, eall P (cs i)

/-- Local well-formedness: positive length; interior vertices have `≥ 2` children
(i.e. degree `≥ 3`; degree-2 vertices are suppressed). -/
def LocOK : RTree → Prop
  | leaf ℓ => 0 < ℓ
  | node ℓ d _ => 0 < ℓ ∧ 2 ≤ d

/-- A well-formed Dirichlet tree. -/
def WF (T : RTree) : Prop := eall LocOK T

/-- Total length `L = Σ_e ℓ_e`. -/
noncomputable def totalLen (T : RTree) : ℝ := esum len T

/-- Prüfer angle at the lower end of the top edge: `s = 0` at a leaf, and at an interior vertex
`s = arccot (Σ_i cot t_i) ∈ (0, π)` where `t_i` are the child top-angles. -/
noncomputable def sAng : RTree → ℝ → ℝ
  | leaf _, _ => 0
  | node _ _ cs, ω => arccot (∑ i, cot (sAng (cs i) ω + ω * len (cs i)))

/-- Prüfer angle at the upper end of the top edge: `t = s + ω ℓ`. -/
noncomputable def tAng (T : RTree) (ω : ℝ) : ℝ := sAng T ω + ω * len T

theorem sAng_node (ℓ : ℝ) (d : ℕ) (cs : Fin d → RTree) (ω : ℝ) :
    sAng (node ℓ d cs) ω = arccot (∑ i, cot (tAng (cs i) ω)) := by
  simp [sAng, tAng]

theorem sAng_leaf (ℓ ω : ℝ) : sAng (leaf ℓ) ω = 0 := rfl

theorem sAng_nonneg (T : RTree) (ω : ℝ) : 0 ≤ sAng T ω := by
  cases T with
  | leaf ℓ => exact le_rfl
  | node ℓ d cs => rw [sAng_node]; exact (arccot_pos _).le

theorem sAng_lt_pi (T : RTree) (ω : ℝ) : sAng T ω < π := by
  cases T with
  | leaf ℓ => exact pi_pos
  | node ℓ d cs => rw [sAng_node]; exact arccot_lt_pi _

/-- Genericity of `ω` for every edge: `sin (ω ℓ_e) ≠ 0` and `sin t_e ≠ 0`. -/
def Generic (T : RTree) (ω : ℝ) : Prop :=
  eall (fun S => sin (ω * len S) ≠ 0 ∧ sin (tAng S ω) ≠ 0) T

/-- `Σ_e ⌊t_e(ω)/π⌋` (as a real number). -/
noncomputable def floorSum (T : RTree) (ω : ℝ) : ℝ := esum (fun S => (⌊tAng S ω / π⌋ : ℝ)) T

/-- The vertex defect `f_c = Σ_{i child of c} τ_i - s_{e_c}` (zero for a leaf-start edge). -/
noncomputable def fvert (ω : ℝ) : RTree → ℝ
  | leaf _ => 0
  | node ℓ d cs => ∑ i, red (tAng (cs i) ω) - sAng (node ℓ d cs) ω

theorem esum_sub (f g : RTree → ℝ) (T : RTree) :
    esum (fun S => f S - g S) T = esum f T - esum g T := by
  induction T with
  | leaf ℓ => rfl
  | node ℓ d cs ih => simp only [esum, ih, Finset.sum_sub_distrib]; ring

theorem esum_mul (c : ℝ) (f : RTree → ℝ) (T : RTree) :
    esum (fun S => c * f S) T = c * esum f T := by
  induction T with
  | leaf ℓ => rfl
  | node ℓ d cs ih => simp only [esum, ih, ← Finset.mul_sum]; ring

/-- **Identity (3) of PROOF.md**: `ω L - π Σ_e ⌊t_e/π⌋ = τ_root + Σ_c f_c`. -/
theorem key_identity (T : RTree) (ω : ℝ) :
    ω * totalLen T - π * floorSum T ω = red (tAng T ω) + vsum (fvert ω) T := by
  have h1 : ∀ T : RTree, esum (fun S => red (tAng S ω) - sAng S ω) T
      = red (tAng T ω) + vsum (fvert ω) T := by
    intro T
    induction T with
    | leaf ℓ => simp [esum, vsum, sAng_leaf]
    | node ℓ d cs ih =>
      simp only [esum, vsum, ih, fvert, Finset.sum_add_distrib]; ring
  rw [← h1, totalLen, floorSum, ← esum_mul, ← esum_mul, ← esum_sub]
  congr 1; funext S; unfold red tAng; ring

theorem eall_top {P : RTree → Prop} {T : RTree} (h : eall P T) : P T := by
  cases T with
  | leaf ℓ => exact h
  | node ℓ d cs => exact h.1

theorem fvert_node_pos {ω ℓ : ℝ} {d : ℕ} {cs : Fin d → RTree} (hd : 2 ≤ d)
    (hgen : ∀ i, sin (tAng (cs i) ω) ≠ 0) : 0 < fvert ω (node ℓ d cs) := by
  simp only [fvert, sAng_node]
  have := vertex_lemma hd (fun i => red (tAng (cs i) ω)) (fun i => red_pos (hgen i))
    (fun i => red_lt_pi _)
  simpa only [cot_red] using this

theorem vsum_fvert_nonneg {ω : ℝ} {T : RTree} (hwf : WF T) (hgen : Generic T ω) :
    0 ≤ vsum (fvert ω) T := by
  induction T with
  | leaf ℓ => exact le_rfl
  | node ℓ d cs ih =>
    simp only [vsum]
    have h1 := fvert_node_pos (ℓ := ℓ) hwf.1.2 (fun i => (eall_top (hgen.2 i)).2)
    have h2 : 0 ≤ ∑ i, vsum (fvert ω) (cs i) :=
      Finset.sum_nonneg fun i _ => ih i (hwf.2 i) (hgen.2 i)
    linarith

/-- **(b) Key inequality.** For generic `ω` (any `ω`, in fact; positivity of `ω` is not
needed), `Σ_e ⌊t_e(ω)/π⌋ < ω L / π`. -/
theorem key_inequality {T : RTree} (hwf : WF T) {ω : ℝ} (hgen : Generic T ω) :
    floorSum T ω < ω * totalLen T / π := by
  have h := key_identity T ω
  have h1 := red_pos (eall_top hgen).2
  have h2 := vsum_fvert_nonneg hwf hgen
  rw [lt_div_iff₀ pi_pos]
  nlinarith

/-! ## Part 3. Monotonicity of the angles on a generic interval (PROOF.md §3.4, gap d) -/

/-- A continuous strictly increasing function on an interval that never meets `πℤ` stays in one
strip `(nπ, (n+1)π)`. -/
theorem floor_const {g : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected) (hc : ContinuousOn g J)
    (hm : StrictMonoOn g J) (hs : ∀ x ∈ J, sin (g x) ≠ 0) :
    ∀ x ∈ J, ∀ y ∈ J, ⌊g x / π⌋ = ⌊g y / π⌋ := by
  have key : ∀ x ∈ J, ∀ y ∈ J, x ≤ y → ⌊g x / π⌋ = ⌊g y / π⌋ := by
    intro x hx y hy hxy
    have hle : g x ≤ g y := hm.monotoneOn hx hy hxy
    apply le_antisymm (Int.floor_le_floor (div_le_div_of_nonneg_right hle pi_pos.le))
    by_contra hlt
    push Not at hlt
    set n := ⌊g x / π⌋
    have h1 : g x < ((n : ℝ) + 1) * π := by
      have := Int.lt_floor_add_one (g x / π); rwa [div_lt_iff₀ pi_pos] at this
    have h2 : ((n : ℝ) + 1) * π ≤ g y := by
      have h3 : ((n + 1 : ℤ) : ℝ) ≤ g y / π := by
        have : n + 1 ≤ ⌊g y / π⌋ := hlt
        exact (Int.cast_le.2 this).trans (Int.floor_le _)
      rw [le_div_iff₀ pi_pos] at h3; push_cast at h3; exact h3
    have hsub : Icc x y ⊆ J := hJ.out hx hy
    obtain ⟨z, hz, hgz⟩ := intermediate_value_Icc hxy (hc.mono hsub) ⟨h1.le, h2⟩
    apply hs z (hsub hz)
    rw [hgz, show ((n : ℝ) + 1) * π = ((n + 1 : ℤ) : ℝ) * π by push_cast; ring, sin_int_mul_pi]
  intro x hx y hy
  rcases le_total x y with h | h
  · exact key x hx y hy h
  · exact (key y hy x hx h).symm

theorem red_eq_of_floor {x : ℝ} {n : ℤ} (h : ⌊x / π⌋ = n) : red x = x - π * n := by
  unfold red; rw [h]

/-- On a generic interval the reduced angle `τ = t - π⌊t/π⌋` is strictly increasing and
`cot ∘ t` is strictly decreasing and continuous. -/
theorem strip_facts {g : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected) (hc : ContinuousOn g J)
    (hm : StrictMonoOn g J) (hs : ∀ x ∈ J, sin (g x) ≠ 0) :
    StrictMonoOn (fun x => red (g x)) J ∧ StrictAntiOn (fun x => cot (g x)) J ∧
      ContinuousOn (fun x => cot (g x)) J := by
  have hf := floor_const hJ hc hm hs
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only
    rw [red_eq_of_floor (hf x hx y hy), red_eq_of_floor rfl]
    linarith [hm hx hy hxy]
  · intro x hx y hy hxy
    simp only
    rw [← cot_red (g x), ← cot_red (g y)]
    have hmono : red (g x) < red (g y) := by
      rw [red_eq_of_floor (hf x hx y hy), red_eq_of_floor rfl]
      linarith [hm hx hy hxy]
    exact cot_strictAntiOn ⟨red_pos (hs x hx), red_lt_pi _⟩ ⟨red_pos (hs y hy), red_lt_pi _⟩ hmono
  · intro x hx
    exact (continuousAt_cot (hs x hx)).comp_continuousWithinAt (hc x hx)

/-- **Monotonicity lemma** (by induction from the leaves): on an interval `J ⊆ (0,∞)` of generic
frequencies, every `t_e` is continuous and strictly increasing and every `s_e` is continuous and
nondecreasing. -/
theorem angles_mono {J : Set ℝ} (hJ : J.OrdConnected) :
    ∀ T : RTree, WF T → (∀ ω ∈ J, Generic T ω) →
      ContinuousOn (tAng T) J ∧ StrictMonoOn (tAng T) J ∧
        ContinuousOn (sAng T) J ∧ MonotoneOn (sAng T) J := by
  have lin : ∀ ℓ : ℝ, 0 < ℓ → ContinuousOn (fun ω : ℝ => ω * ℓ) J ∧
      StrictMonoOn (fun ω : ℝ => ω * ℓ) J := fun ℓ hℓ =>
    ⟨(continuous_id.mul continuous_const).continuousOn,
      fun x _ y _ hxy => mul_lt_mul_of_pos_right hxy hℓ⟩
  intro T
  induction T with
  | leaf ℓ =>
    intro hwf _
    have hs : sAng (leaf ℓ) = fun _ => 0 := funext fun _ => rfl
    have ht : tAng (leaf ℓ) = fun ω => ω * ℓ := by
      funext ω; simp [tAng, sAng_leaf, len]
    rw [ht, hs]
    exact ⟨(lin ℓ hwf).1, (lin ℓ hwf).2, continuousOn_const, monotoneOn_const⟩
  | node ℓ d cs ih =>
    intro hwf hgen
    have hch : ∀ i, StrictAntiOn (fun x => cot (tAng (cs i) x)) J ∧
        ContinuousOn (fun x => cot (tAng (cs i) x)) J := by
      intro i
      obtain ⟨h1, h2, -, -⟩ := ih i (hwf.2 i) (fun ω hω => (hgen ω hω).2 i)
      have := strip_facts hJ h1 h2 (fun ω hω => (eall_top ((hgen ω hω).2 i)).2)
      exact ⟨this.2.1, this.2.2⟩
    have hsf : sAng (node ℓ d cs) = fun ω => arccot (∑ i, cot (tAng (cs i) ω)) :=
      funext fun ω => sAng_node ℓ d cs ω
    have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, by have := hwf.1.2; omega⟩,
      Finset.mem_univ _⟩
    have hsmono : StrictMonoOn (sAng (node ℓ d cs)) J := by
      intro x hx y hy hxy
      rw [hsf]
      apply arccot_strictAnti
      exact Finset.sum_lt_sum_of_nonempty hne fun i _ => (hch i).1 hx hy hxy
    have hscont : ContinuousOn (sAng (node ℓ d cs)) J := by
      rw [hsf]
      exact continuous_arccot.comp_continuousOn (continuousOn_finsetSum _ fun i _ => (hch i).2)
    have ht : tAng (node ℓ d cs) = fun ω => sAng (node ℓ d cs) ω + ω * ℓ := by
      funext ω; simp [tAng, len]
    have hl := lin ℓ hwf.1.1
    rw [ht]
    exact ⟨hscont.add hl.1, fun x hx y hy hxy => add_lt_add (hsmono hx hy hxy) (hl.2 hx hy hxy),
      hscont, hsmono.monotoneOn⟩

/-! ## Part 4. The one-sided limit at a vertex (PROOF.md §3.4, "Limit") -/

theorem tendsto_cot_nhdsGT_zero : Tendsto cot (𝓝[>] 0) atTop := by
  have hsin : Tendsto sin (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := continuous_sin.continuousAt (x := 0)
      rw [ContinuousAt, sin_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT pi_pos] with x hx
      exact sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hcos : Tendsto cos (𝓝[>] 0) (𝓝 1) := by
    have := continuous_cos.continuousAt (x := 0)
    rw [ContinuousAt, cos_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := hcos.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp hsin)
  refine h.congr fun x => ?_
  simp [cot_eq_cos_div_sin, div_eq_mul_inv]

theorem tendsto_arccot_atTop : Tendsto arccot atTop (𝓝 0) := by
  have := (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_sub (π / 2)
  have e : arccot = fun x => π / 2 - arctan x := rfl
  rw [e]; simpa using this

/-- **Vertex limit lemma.** At an interior vertex with `d ≥ 2` children whose reduced angles
`τ_i(ω) ∈ (0, π)` are nondecreasing on `(a, b)`, if the vertex defect
`Σ τ_i - arccot (Σ cot τ_i)` tends to `0` as `ω ↓ a`, then every `τ_i → 0` and the parent angle
`s → 0`. (This replaces the continuous extension of `f` to `[0, π)^d` in PROOF.md.) -/
theorem vertex_limit {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (hab : a < b) (τ : Fin d → ℝ → ℝ)
    (σ : ℝ → ℝ) (hmono : ∀ i, MonotoneOn (τ i) (Ioo a b))
    (hpos : ∀ i, ∀ ω ∈ Ioo a b, 0 < τ i ω) (hlt : ∀ i, ∀ ω ∈ Ioo a b, τ i ω < π)
    (hσ : ∀ ω ∈ Ioo a b, σ ω = arccot (∑ i, cot (τ i ω)))
    (hlim : Tendsto (fun ω => ∑ i, τ i ω - σ ω) (𝓝[>] a) (𝓝 0)) :
    (∀ i, Tendsto (τ i) (𝓝[>] a) (𝓝 0)) ∧ Tendsto σ (𝓝[>] a) (𝓝 0) := by
  have hJ : Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  set A : Fin d → ℝ := fun i => sInf (τ i '' Ioo a b) with hA
  have hbdd : ∀ i, BddBelow (τ i '' Ioo a b) := fun i =>
    ⟨0, by rintro _ ⟨ω, hω, rfl⟩; exact (hpos i ω hω).le⟩
  have hT : ∀ i, Tendsto (τ i) (𝓝[>] a) (𝓝 (A i)) := fun i =>
    (hmono i).tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hab) (hbdd i)
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hA0 : ∀ i, 0 ≤ A i := fun i =>
    ge_of_tendsto (hT i) (Filter.mem_of_superset hJ fun ω hω => (hpos i ω hω).le)
  have hAπ : ∀ i, A i < π := fun i =>
    (csInf_le (hbdd i) (mem_image_of_mem _ hm)).trans_lt (hlt i m hm)
  have hσev : σ =ᶠ[𝓝[>] a] fun ω => arccot (∑ i, cot (τ i ω)) :=
    Filter.mem_of_superset hJ fun ω hω => hσ ω hω
  by_cases hall : ∀ i, 0 < A i
  · exfalso
    have hcot : ∀ i, Tendsto (fun ω => cot (τ i ω)) (𝓝[>] a) (𝓝 (cot (A i))) := fun i =>
      (continuousAt_cot (sin_pos_of_pos_of_lt_pi (hall i) (hAπ i)).ne').tendsto.comp (hT i)
    have hs : Tendsto σ (𝓝[>] a) (𝓝 (arccot (∑ i, cot (A i)))) :=
      ((continuous_arccot.tendsto _).comp (tendsto_finsetSum _ fun i _ => hcot i)).congr'
        hσev.symm
    have hlim2 := (tendsto_finsetSum Finset.univ fun i _ => hT i).sub hs
    have heq := tendsto_nhds_unique hlim hlim2
    have := vertex_lemma hd A hall hAπ
    linarith
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hAj : A j = 0 := le_antisymm hj (hA0 j)
    have hτj : Tendsto (τ j) (𝓝[>] a) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hAj ▸ hT j, Filter.mem_of_superset hJ fun ω hω => hpos j ω hω⟩
    have hcj := tendsto_cot_nhdsGT_zero.comp hτj
    have hsumtop : Tendsto (fun ω => ∑ i, cot (τ i ω)) (𝓝[>] a) atTop := by
      refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _
        (∑ i ∈ Finset.univ.erase j, cot (τ i m)) hcj)
      have hJ' : Ioo a m ∈ 𝓝[>] a := Ioo_mem_nhdsGT hm.1
      filter_upwards [hJ'] with ω hω
      have hω' : ω ∈ Ioo a b := ⟨hω.1, hω.2.trans hm.2⟩
      have hle : ∑ i ∈ Finset.univ.erase j, cot (τ i m) ≤
          ∑ i ∈ Finset.univ.erase j, cot (τ i ω) := Finset.sum_le_sum fun i _ =>
        cot_strictAntiOn.antitoneOn ⟨hpos i ω hω', hlt i ω hω'⟩ ⟨hpos i m hm, hlt i m hm⟩
          (hmono i hω' hm hω.2.le)
      have := Finset.add_sum_erase Finset.univ (fun i => cot (τ i ω)) (Finset.mem_univ j)
      show cot (τ j ω) + _ ≤ _
      linarith
    have hs : Tendsto σ (𝓝[>] a) (𝓝 0) := (tendsto_arccot_atTop.comp hsumtop).congr' hσev.symm
    have hsum : Tendsto (fun ω => ∑ i, τ i ω) (𝓝[>] a) (𝓝 0) := by
      have := hlim.add hs
      simp only [sub_add_cancel, add_zero] at this
      exact this
    refine ⟨fun i => ?_, hs⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.mem_of_superset hJ fun ω hω => (hpos i ω hω).le)
      (Filter.mem_of_superset hJ fun ω hω => ?_)
    exact Finset.single_le_sum (f := fun i => τ i ω) (fun i _ => (hpos i ω hω).le)
      (Finset.mem_univ i)

/-! ## Part 5. The equality case (PROOF.md §3.4) -/

theorem eall_mono {P Q : RTree → Prop} (hPQ : ∀ S, P S → Q S) :
    ∀ T, eall P T → eall Q T := by
  intro T
  induction T with
  | leaf ℓ => exact hPQ _
  | node ℓ d cs ih => exact fun h => ⟨hPQ _ h.1, fun i => ih i (h.2 i)⟩

/-- Squeeze for a sum of two nonnegative terms. -/
theorem squeeze_two {l : Filter ℝ} {u v : ℝ → ℝ} (hu : ∀ᶠ ω in l, 0 ≤ u ω)
    (hv : ∀ᶠ ω in l, 0 ≤ v ω) (h : Tendsto (fun ω => u ω + v ω) l (𝓝 0)) :
    Tendsto u l (𝓝 0) ∧ Tendsto v l (𝓝 0) := by
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h hu ?_
    filter_upwards [hv] with ω hω; linarith
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h hv ?_
    filter_upwards [hu] with ω hω; linarith

/-- Top edge: if `τ_e → 0` and `s_e → 0` as `ω ↓ a`, then `a ℓ_e ∈ π ℤ_{>0}`. -/
theorem top_edge {a b : ℝ} (ha : 0 < a) (hab : a < b) {T : RTree} (hwf : WF T)
    (hgen : ∀ ω ∈ Ioo a b, Generic T ω)
    (hτ : Tendsto (fun ω => red (tAng T ω)) (𝓝[>] a) (𝓝 0))
    (hs : Tendsto (sAng T) (𝓝[>] a) (𝓝 0)) :
    ∃ m : ℕ, 0 < m ∧ a * len T = m * π := by
  obtain ⟨h1, h2, -, -⟩ := angles_mono ordConnected_Ioo T hwf hgen
  have hf := floor_const ordConnected_Ioo h1 h2 fun ω hω => (eall_top (hgen ω hω)).2
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊tAng T m / π⌋ := ⟨_, rfl⟩
  have hJ : Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  have hev : (fun ω => red (tAng T ω) - sAng T ω + π * n) =ᶠ[𝓝[>] a] fun ω => ω * len T :=
    Filter.mem_of_superset hJ fun ω hω => by
      show red (tAng T ω) - sAng T ω + π * n = ω * len T
      rw [red_eq_of_floor ((hf ω hω m hm).trans hn.symm)]; unfold tAng; ring
  have hlim1 : Tendsto (fun ω => red (tAng T ω) - sAng T ω + π * n) (𝓝[>] a) (𝓝 (π * n)) := by
    simpa using (hτ.sub hs).add_const (π * n)
  have hlim2 : Tendsto (fun ω : ℝ => ω * len T) (𝓝[>] a) (𝓝 (a * len T)) :=
    ((continuous_id.mul continuous_const).tendsto a).mono_left nhdsWithin_le_nhds
  have heq : π * n = a * len T := tendsto_nhds_unique (hlim1.congr' hev) hlim2
  have hlen : 0 < len T := by
    cases T with
    | leaf ℓ => exact hwf
    | node ℓ d cs => exact hwf.1.1
  have hnpos : (0 : ℝ) < n := by
    have : 0 < π * n := by rw [heq]; positivity
    exact pos_of_mul_pos_right this pi_pos.le
  have hn : 0 < n := by exact_mod_cast hnpos
  refine ⟨n.toNat, by omega, ?_⟩
  rw [← heq, mul_comm]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hn.le).symm

/-- Core induction (top-down): if `τ_top → 0` and the vertex-defect sum `→ 0` as `ω ↓ a`, then
every edge satisfies `a ℓ_e ∈ π ℤ_{>0}`. -/
theorem core_induct {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ T : RTree, WF T → (∀ ω ∈ Ioo a b, Generic T ω) →
      Tendsto (fun ω => red (tAng T ω)) (𝓝[>] a) (𝓝 0) →
      Tendsto (fun ω => vsum (fvert ω) T) (𝓝[>] a) (𝓝 0) →
      eall (fun S => ∃ m : ℕ, 0 < m ∧ a * len S = m * π) T := by
  have hJ : Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  intro T
  induction T with
  | leaf ℓ =>
    intro hwf hgen hτ _
    exact top_edge ha hab hwf hgen hτ tendsto_const_nhds
  | node ℓ d cs ih =>
    intro hwf hgen hτ hF
    -- split the defect sum: `f_c + Σ_i F(cs i)`, all terms nonnegative
    have hF' : Tendsto (fun ω => fvert ω (node ℓ d cs) + ∑ i, vsum (fvert ω) (cs i))
        (𝓝[>] a) (𝓝 0) := by simpa only [vsum] using hF
    obtain ⟨hf, hrest⟩ := squeeze_two
      (Filter.mem_of_superset hJ fun ω hω =>
        (fvert_node_pos hwf.1.2 fun i => (eall_top ((hgen ω hω).2 i)).2).le)
      (Filter.mem_of_superset hJ fun ω hω =>
        Finset.sum_nonneg fun i _ => vsum_fvert_nonneg (hwf.2 i) ((hgen ω hω).2 i)) hF'
    have hchild : ∀ i, Tendsto (fun ω => vsum (fvert ω) (cs i)) (𝓝[>] a) (𝓝 0) := by
      intro i
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrest
        (Filter.mem_of_superset hJ fun ω hω => vsum_fvert_nonneg (hwf.2 i) ((hgen ω hω).2 i))
        (Filter.mem_of_superset hJ fun ω hω => ?_)
      exact Finset.single_le_sum (f := fun i => vsum (fvert ω) (cs i))
        (fun i _ => vsum_fvert_nonneg (hwf.2 i) ((hgen ω hω).2 i)) (Finset.mem_univ i)
    -- vertex limit
    have hmono : ∀ i, MonotoneOn (fun ω => red (tAng (cs i) ω)) (Ioo a b) := by
      intro i
      obtain ⟨h1, h2, -, -⟩ := angles_mono ordConnected_Ioo (cs i) (hwf.2 i)
        fun ω hω => (hgen ω hω).2 i
      exact (strip_facts ordConnected_Ioo h1 h2
        fun ω hω => (eall_top ((hgen ω hω).2 i)).2).1.monotoneOn
    obtain ⟨hτi, hs⟩ := vertex_limit hwf.1.2 hab (fun i ω => red (tAng (cs i) ω))
      (sAng (node ℓ d cs)) hmono
      (fun i ω hω => red_pos (eall_top ((hgen ω hω).2 i)).2) (fun i ω _ => red_lt_pi _)
      (fun ω _ => by simp only [sAng_node, cot_red]) (by simpa only [fvert] using hf)
    exact ⟨top_edge ha hab hwf hgen hτ hs,
      fun i => ih i (hwf.2 i) (fun ω hω => (hgen ω hω).2 i) (hτi i) (hchild i)⟩

theorem totalLen_pos {T : RTree} (hwf : WF T) : 0 < totalLen T := by
  unfold totalLen
  induction T with
  | leaf ℓ => exact hwf
  | node ℓ d cs ih =>
    simp only [esum]
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (ih i (hwf.2 i)).le
    have h : (node ℓ d cs).len = ℓ := rfl
    linarith [hwf.1.1]

/-- **(c) Equality core.** Let `ω₀ = π k / L` with `k ≥ 1`. If on some interval `(ω₀, ω₀ + ε)`
every `ω` is generic (the interval avoids the exceptional set `E`) and
`Σ_e ⌊t_e(ω)/π⌋ ≥ k`, then every edge length is a positive integer multiple of `L / k`. -/
theorem equality_core {T : RTree} (hwf : WF T) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε)
    (hgen : ∀ ω ∈ Ioo (π * k / totalLen T) (π * k / totalLen T + ε), Generic T ω)
    (hcount : ∀ ω ∈ Ioo (π * k / totalLen T) (π * k / totalLen T + ε), (k : ℝ) ≤ floorSum T ω) :
    eall (fun S => ∃ m : ℕ, 0 < m ∧ len S = m * (totalLen T / k)) T := by
  have hL := totalLen_pos hwf
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set a := π * k / totalLen T with ha_def
  have ha : 0 < a := by positivity
  have hab : a < a + ε := by linarith
  have hJ : Ioo a (a + ε) ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  -- `τ_root + Σ f_c = ω L - π N ≤ (ω - a) L → 0`
  have hD : Tendsto (fun ω => red (tAng T ω) + vsum (fvert ω) T) (𝓝[>] a) (𝓝 0) := by
    have hup : Tendsto (fun ω => (ω - a) * totalLen T) (𝓝[>] a) (𝓝 0) := by
      have : Tendsto (fun ω => (ω - a) * totalLen T) (𝓝 a) (𝓝 ((a - a) * totalLen T)) :=
        ((continuous_id.sub continuous_const).mul continuous_const).tendsto a
      simpa using this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Filter.mem_of_superset hJ fun ω hω => ?_) (Filter.mem_of_superset hJ fun ω hω => ?_)
    · have := red_nonneg (tAng T ω)
      have := vsum_fvert_nonneg hwf (hgen ω hω)
      show 0 ≤ red (tAng T ω) + vsum (fvert ω) T
      linarith
    · show red (tAng T ω) + vsum (fvert ω) T ≤ (ω - a) * totalLen T
      rw [← key_identity]
      have h1 := hcount ω hω
      have h2 : a * totalLen T = π * k := by rw [ha_def]; field_simp
      nlinarith [pi_pos]
  obtain ⟨hτ, hF⟩ := squeeze_two
    (Filter.mem_of_superset hJ fun ω _ => red_nonneg (tAng T ω))
    (Filter.mem_of_superset hJ fun ω hω => vsum_fvert_nonneg hwf (hgen ω hω)) hD
  refine eall_mono ?_ T (core_induct ha hab T hwf hgen hτ hF)
  rintro S ⟨m, hm, hS⟩
  refine ⟨m, hm, ?_⟩
  rw [ha_def] at hS
  field_simp at hS ⊢
  nlinarith [pi_pos]

theorem esum_le {f g : RTree → ℝ} :
    ∀ T, eall (fun S => f S ≤ g S) T → esum f T ≤ esum g T := by
  intro T
  induction T with
  | leaf ℓ => exact id
  | node ℓ d cs ih =>
    intro h
    simp only [esum]
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => ih i (h.2 i)
    linarith [h.1]

/-- "If" direction, angle form: if every edge length is a positive integer multiple of `L/k`,
then `Σ_e ⌊t_e(ω)/π⌋ ≥ k` for every `ω > π k / L`. -/
theorem floorSum_ge_of_multiples {T : RTree} (hwf : WF T) {k : ℕ} (hk : 1 ≤ k)
    (hmult : eall (fun S => ∃ m : ℕ, 0 < m ∧ len S = m * (totalLen T / k)) T) {ω : ℝ}
    (hω : π * k / totalLen T < ω) : (k : ℝ) ≤ floorSum T ω := by
  have hL := totalLen_pos hwf
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set a := π * k / totalLen T with ha_def
  have ha : 0 < a := by positivity
  have hle : esum (fun S => (a / π) * len S) T ≤ floorSum T ω := by
    apply esum_le
    refine eall_mono ?_ T hmult
    rintro S ⟨m, hm, hS⟩
    -- `a ℓ = m π`, and `t ≥ ω ℓ > a ℓ`
    have haS : a / π * len S = m := by
      rw [hS, ha_def]; field_simp
    rw [haS]
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hlen : 0 < len S := by rw [hS]; positivity
    have ht : (m : ℝ) * π < tAng S ω := by
      have h1 : (m : ℝ) * π = a * len S := by
        rw [← haS]; field_simp
      have := sAng_nonneg S ω
      unfold tAng
      rw [h1]; nlinarith
    have : ((m : ℤ) : ℝ) ≤ tAng S ω / π := by
      rw [le_div_iff₀ pi_pos]; push_cast; linarith
    have := Int.le_floor.2 this
    exact_mod_cast this
  rw [esum_mul, ← totalLen, ha_def] at hle
  have : π * k / totalLen T / π * totalLen T = k := by field_simp
  linarith

end RTree

/-! ## Part 6. The spectral bridge (explicit hypothesis, NOT formalized)

`SpectralInput T lam` packages the *standard* spectral-theoretic input about the Dirichlet
Laplacian `-d²/dx²` on the metric tree encoded by `T` (Kirchhoff conditions at interior vertices,
Dirichlet at the leaves), with `lam 1 ≤ lam 2 ≤ …` its eigenvalues counted with multiplicity
(`lam 0` is an unused dummy). It is an *assumption* of the theorems below; none of the following
is formalized here (Mathlib has no spectral theory of quantum graphs):

* `mono`, `finite_below`: the spectrum is discrete, listed increasingly with multiplicity, with
  finitely many eigenvalues below any level (compact resolvent).
* `index`: the index formula (2) of PROOF.md, `N⁻(ω²) = Σ_e ⌊t_e(ω)/π⌋` for generic `ω > 0`,
  where `N⁻(μ) = #{j ≥ 1 : λ_j < μ}`. Its proof combines min-max (`N⁻(μ)` = negative index of
  `a(f) - μ‖f‖²` on `H¹`), Step 1 (splitting `H = H_harm ⊕ H_0`, which gives
  `N⁻ = Σ_e ⌊ωℓ_e/π⌋ + n₋(M)`) and Step 2 (LDLᵀ elimination of the vertex matrix `M` with the
  pivot/Schur identities, Sylvester's law of inertia, and the floor bookkeeping
  `⌊ωℓ_e/π⌋ + [p_c < 0] = ⌊t_e/π⌋`). The trigonometric identities used in Step 2 are proved in
  `QuantumGraphEquality.lean` / Part 1 here, but the linear-algebra and functional-analysis parts
  are not.
* `generic_right`: the non-generic set `E` is discrete in `(0, ∞)` (PROOF.md §3.2, "gap b": it is
  contained in the zero set of finitely many nonzero entire functions); only the consequence
  "every `ω₀ ≥ 0` has a punctured right neighbourhood of generic frequencies" is used. -/

open RTree

/-- `N⁻(μ) = #{j ≥ 1 : λ_j < μ}`. -/
noncomputable def countBelow (lam : ℕ → ℝ) (μ : ℝ) : ℕ := Set.ncard {j : ℕ | 1 ≤ j ∧ lam j < μ}

/-- The standard spectral input (an explicit hypothesis; see the comment above). -/
structure SpectralInput (T : RTree) (lam : ℕ → ℝ) : Prop where
  mono : Monotone lam
  finite_below : ∀ μ : ℝ, {j : ℕ | lam j < μ}.Finite
  index : ∀ ω : ℝ, 0 < ω → Generic T ω → (countBelow lam (ω ^ 2) : ℝ) = floorSum T ω
  generic_right : ∀ ω₀ : ℝ, 0 ≤ ω₀ → ∃ ε > 0, ∀ ω ∈ Ioo ω₀ (ω₀ + ε), Generic T ω

namespace SpectralInput

variable {T : RTree} {lam : ℕ → ℝ}

theorem k_le_count (hS : SpectralInput T lam) {k : ℕ} {μ : ℝ} (h : lam k < μ) :
    k ≤ countBelow lam μ := by
  have hsub : (↑(Finset.Icc 1 k) : Set ℕ) ⊆ {j : ℕ | 1 ≤ j ∧ lam j < μ} := by
    intro j hj
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj
    exact ⟨hj.1, (hS.mono hj.2).trans_lt h⟩
  have hfin : {j : ℕ | 1 ≤ j ∧ lam j < μ}.Finite :=
    (hS.finite_below μ).subset fun j hj => hj.2
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Nat.card_Icc] at this
  unfold countBelow; omega

theorem count_lt (hS : SpectralInput T lam) {k : ℕ} (hk : 1 ≤ k) {μ : ℝ} (h : μ ≤ lam k) :
    countBelow lam μ < k := by
  have hsub : {j : ℕ | 1 ≤ j ∧ lam j < μ} ⊆ (↑(Finset.Icc 1 (k - 1)) : Set ℕ) := by
    intro j ⟨h1, h2⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨h1, ?_⟩
    by_contra hc
    have : k ≤ j := by omega
    linarith [hS.mono this]
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Nat.card_Icc] at this
  unfold countBelow; omega

theorem exists_generic_between (hS : SpectralInput T lam) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ ω ∈ Ioo a b, Generic T ω := by
  obtain ⟨ε, hε, h⟩ := hS.generic_right a ha
  refine ⟨a + min ε (b - a) / 2, ⟨?_, ?_⟩, h _ ⟨?_, ?_⟩⟩ <;>
    [have := lt_min hε (sub_pos.2 hab); have := min_le_right ε (b - a);
     have := lt_min hε (sub_pos.2 hab); have := min_le_left ε (b - a)] <;> linarith

/-- **(b') Pólya bound** `λ_k ≥ (π k / L)²`, from the key inequality and the spectral input. -/
theorem polya_bound (hS : SpectralInput T lam) (hwf : WF T) {k : ℕ} (hk : 1 ≤ k) :
    (π * k / totalLen T) ^ 2 ≤ lam k := by
  have hL := totalLen_pos hwf
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set ω₀ := π * k / totalLen T with hω₀
  have h0 : 0 < ω₀ := by positivity
  by_contra hlt
  push Not at hlt
  have hsq : √(lam k) < ω₀ := (Real.sqrt_lt' h0).2 hlt
  obtain ⟨ω, hω, hgen⟩ := hS.exists_generic_between (Real.sqrt_nonneg _) hsq
  have hωpos : 0 < ω := (Real.sqrt_nonneg _).trans_lt hω.1
  have hc := hS.k_le_count (μ := ω ^ 2) (Real.lt_sq_of_sqrt_lt hω.1)
  have hidx := hS.index ω hωpos hgen
  have hkey := key_inequality hwf hgen
  have : ω * totalLen T / π < k := by
    rw [div_lt_iff₀ pi_pos]
    have : ω * totalLen T < ω₀ * totalLen T := mul_lt_mul_of_pos_right hω.2 hL
    have e : ω₀ * totalLen T = π * k := by rw [hω₀]; field_simp
    linarith
  have : (k : ℝ) ≤ countBelow lam (ω ^ 2) := by exact_mod_cast hc
  linarith

/-- **(c') Equality characterization** (Open Problem 1.12(3), conditional on `SpectralInput`):
`λ_k = (π k / L)²` iff every edge length is a positive integer multiple of `L / k`. -/
theorem equality_iff (hS : SpectralInput T lam) (hwf : WF T) {k : ℕ} (hk : 1 ≤ k) :
    lam k = (π * k / totalLen T) ^ 2 ↔
      eall (fun S => ∃ m : ℕ, 0 < m ∧ len S = m * (totalLen T / k)) T := by
  have hL := totalLen_pos hwf
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set ω₀ := π * k / totalLen T with hω₀
  have h0 : 0 < ω₀ := by positivity
  constructor
  · intro heq
    obtain ⟨ε, hε, hgen⟩ := hS.generic_right ω₀ h0.le
    refine equality_core hwf hk hε hgen fun ω hω => ?_
    have hωpos : 0 < ω := h0.trans hω.1
    have hlt : lam k < ω ^ 2 := by rw [heq]; nlinarith [hω.1]
    rw [← hS.index ω hωpos (hgen ω hω)]
    exact_mod_cast hS.k_le_count hlt
  · intro hmult
    refine le_antisymm ?_ (hS.polya_bound hwf hk)
    by_contra hlt
    push Not at hlt
    have hsq : ω₀ < √(lam k) := (Real.lt_sqrt h0.le).2 hlt
    obtain ⟨ω, hω, hgen⟩ := hS.exists_generic_between h0.le hsq
    have hωpos : 0 < ω := h0.trans hω.1
    have hle : ω ^ 2 ≤ lam k := by
      have := Real.sq_sqrt ((sq_nonneg ω₀).trans hlt.le)
      nlinarith [hω.2, Real.sqrt_nonneg (lam k)]
    have hc := hS.count_lt hk hle
    have hf := floorSum_ge_of_multiples hwf hk hmult hω.1
    rw [← hS.index ω hωpos hgen] at hf
    have : (countBelow lam (ω ^ 2) : ℝ) < k := by exact_mod_cast hc
    linarith

end SpectralInput

end DirichletTreeCore

#print axioms DirichletTreeCore.vertex_lemma
#print axioms DirichletTreeCore.RTree.key_inequality
#print axioms DirichletTreeCore.RTree.equality_core
#print axioms DirichletTreeCore.SpectralInput.polya_bound
#print axioms DirichletTreeCore.SpectralInput.equality_iff
