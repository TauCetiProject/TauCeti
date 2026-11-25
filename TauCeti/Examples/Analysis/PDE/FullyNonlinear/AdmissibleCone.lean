/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FullyNonlinear.AdmissiblePair
public import TauCeti.Data.Fin.Basic

/-!
# Examples and non-examples of admissible cones in `ℝ²`

Checks for admissible cones (`TauCeti.IsAdmissibleCone`), the cones `Γ` of the fully nonlinear
equations `f(λ) = c` of eigenvalue type: open, invariant under permutations and positive
dilations, with `Γ_2 ⊆ Γ ⊆ Γ_1`, where `Γ_2` is the open positive quadrant and `Γ_1` the open
half-plane `{μ₀ + μ₁ > 0}`.

* The half-plane `Γ_1` contains `(1, -1/2)`, which has a negative entry: admissible cones need not
  lie in the closed positive quadrant.
* The shifted quadrant `{μ₀ > -1, μ₁ > -1}` is open, symmetric and contains `Γ_2`, but it is not
  an admissible cone: it contains `(-1/2, 1)` but not `3 • (-1/2, 1)`, and it contains
  `(-1/2, -1/2)`, whose coordinate sum is negative.
* The union of `Γ_2` with the wedge `{μ₀ > 0, -μ₀/2 < μ₁ < -μ₀/3}` and its mirror image is an
  admissible cone that is not convex: it contains `(1, -2/5)` and `(1, 1/10)` but not their
  midpoint `(1, -3/20)`. It also violates `Γ + Γ_2 ⊆ Γ`, at `(1, -2/5) + (1/100, 1/4)`. So an
  admissible cone need not be convex; results about concave admissible pairs get convexity of the
  cone from `ConcaveOn ℝ Γ f`, whose first component is `Convex ℝ Γ`.
* Admissibility is preserved by finite intersections (`IsAdmissibleCone.iInter`) but not by
  arbitrary ones: for every `ε ≥ 0` the cone `{μ₀ + μ₁ > 0, μᵢ > -ε (μ₀ + μ₁)}` is admissible,
  but the intersection over all `ε > 0` is not open, since it contains `(1, 0)` and none of the
  points `(1, -t)`, `0 < t < 1`.
-/

public section

namespace TauCeti.Examples.AdmissibleCone

open Set Topology

/-! ### The half-plane `Γ_1` -/

/-- The half-plane `Γ_1 ⊂ ℝ²` contains `(1, -1/2)`, which is not in the positive quadrant. -/
example : (![1, -1 / 2] : Fin 2 → ℝ) ∈ {μ : Fin 2 → ℝ | 0 < ∑ i, μ i} ∧
    (![1, -1 / 2] : Fin 2 → ℝ) ∉ {μ : Fin 2 → ℝ | ∀ i, 0 < μ i} := by
  refine ⟨by norm_num [Fin.sum_univ_two], fun h ↦ ?_⟩
  have := h 1
  norm_num at this

/-! ### The shifted quadrant -/

/-- The shifted quadrant `{μ₀ > -1, μ₁ > -1}`. -/
def shiftedQuadrant : Set (Fin 2 → ℝ) :=
  {μ | ∀ i, -1 < μ i}

/-- Membership in `shiftedQuadrant` in terms of the coordinates. -/
@[simp]
theorem mem_shiftedQuadrant {μ : Fin 2 → ℝ} : μ ∈ shiftedQuadrant ↔ ∀ i, -1 < μ i :=
  Iff.rfl

/-- The shifted quadrant is open. -/
theorem isOpen_shiftedQuadrant : IsOpen shiftedQuadrant := by
  simpa only [shiftedQuadrant, Set.ofPred_forall] using
    isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)

/-- The shifted quadrant is invariant under permutations of the coordinates. -/
theorem comp_perm_mem_shiftedQuadrant (σ : Equiv.Perm (Fin 2)) {μ : Fin 2 → ℝ}
    (hμ : μ ∈ shiftedQuadrant) : μ ∘ σ ∈ shiftedQuadrant :=
  mem_shiftedQuadrant.2 fun i ↦ mem_shiftedQuadrant.1 hμ (σ i)

/-- The shifted quadrant contains the positive quadrant `Γ_2`. -/
theorem mem_shiftedQuadrant_of_forall_pos {μ : Fin 2 → ℝ} (hμ : ∀ i, 0 < μ i) :
    μ ∈ shiftedQuadrant :=
  mem_shiftedQuadrant.2 fun i ↦ by linarith [hμ i]

/-- The shifted quadrant contains `(-1/2, 1)` but not `3 • (-1/2, 1) = (-3/2, 3)`: it is not
invariant under positive dilations. -/
theorem mem_shiftedQuadrant_and_smul_notMem :
    (![-1 / 2, 1] : Fin 2 → ℝ) ∈ shiftedQuadrant ∧
      (3 : ℝ) • (![-1 / 2, 1] : Fin 2 → ℝ) ∉ shiftedQuadrant := by
  refine ⟨mem_shiftedQuadrant.2 fun i ↦ by fin_cases i <;> norm_num, fun h ↦ ?_⟩
  have := mem_shiftedQuadrant.1 h 0
  norm_num at this

/-- The shifted quadrant contains `(-1/2, -1/2)`, whose coordinate sum is negative: it is not
contained in `Γ_1`. -/
theorem mem_shiftedQuadrant_and_sum_neg :
    (![-1 / 2, -1 / 2] : Fin 2 → ℝ) ∈ shiftedQuadrant ∧
      ∑ i, (![-1 / 2, -1 / 2] : Fin 2 → ℝ) i < 0 := by
  exact ⟨mem_shiftedQuadrant.2 fun i ↦ by fin_cases i <;> norm_num, by norm_num [Fin.sum_univ_two]⟩

/-- The shifted quadrant is not an admissible cone. -/
theorem not_isAdmissibleCone_shiftedQuadrant : ¬ IsAdmissibleCone shiftedQuadrant := fun h ↦
  (mem_shiftedQuadrant_and_sum_neg.2.trans (h.sum_pos mem_shiftedQuadrant_and_sum_neg.1)).false

/-! ### A nonconvex admissible cone -/

/-- The union of the positive quadrant with the wedge `{μ₀ > 0, -μ₀/2 < μ₁ < -μ₀/3}` and its
mirror image under the transposition of the coordinates. -/
def wedgeCone : Set (Fin 2 → ℝ) :=
  {μ | 0 < μ 0 ∧ 0 < μ 1} ∪ {μ | 0 < μ 0 ∧ -(μ 0 / 2) < μ 1 ∧ μ 1 < -(μ 0 / 3)} ∪
    {μ | 0 < μ 1 ∧ -(μ 1 / 2) < μ 0 ∧ μ 0 < -(μ 1 / 3)}

/-- Membership in `wedgeCone` in terms of the two coordinates. -/
@[simp]
theorem mem_wedgeCone {μ : Fin 2 → ℝ} :
    μ ∈ wedgeCone ↔ (0 < μ 0 ∧ 0 < μ 1) ∨ (0 < μ 0 ∧ -(μ 0 / 2) < μ 1 ∧ μ 1 < -(μ 0 / 3)) ∨
      (0 < μ 1 ∧ -(μ 1 / 2) < μ 0 ∧ μ 0 < -(μ 1 / 3)) := by
  simp only [wedgeCone, mem_union, mem_ofPred_eq, or_assoc]

/-- The union of the positive quadrant with a wedge and its mirror image is an admissible cone. -/
theorem isAdmissibleCone_wedgeCone : IsAdmissibleCone wedgeCone where
  isOpen := by
    have h0 : Continuous fun μ : Fin 2 → ℝ ↦ μ 0 := continuous_apply 0
    have h1 : Continuous fun μ : Fin 2 → ℝ ↦ μ 1 := continuous_apply 1
    simp only [wedgeCone, ofPred_and]
    refine (((isOpen_lt continuous_const h0).inter (isOpen_lt continuous_const h1)).union
      ((isOpen_lt continuous_const h0).inter ((isOpen_lt (by fun_prop) h1).inter
        (isOpen_lt h1 (by fun_prop))))).union
      ((isOpen_lt continuous_const h1).inter ((isOpen_lt (by fun_prop) h0).inter
        (isOpen_lt h0 (by fun_prop))))
  comp_perm_mem σ μ hμ := by
    rw [mem_wedgeCone] at hμ ⊢
    rcases Equiv.Perm.eq_one_or_swap_fin_two σ with rfl | rfl <;>
      simp only [Function.comp_apply, Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_left,
        Equiv.swap_apply_right] <;> tauto
  smul_mem {t} ht μ hμ := by
    rw [mem_wedgeCone] at hμ ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rcases hμ with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact Or.inl ⟨mul_pos ht h0, mul_pos ht h1⟩
    · exact Or.inr (Or.inl ⟨mul_pos ht h0, by nlinarith, by nlinarith⟩)
    · exact Or.inr (Or.inr ⟨mul_pos ht h0, by nlinarith, by nlinarith⟩)
  mem_of_forall_pos hμ := mem_wedgeCone.2 (Or.inl ⟨hμ 0, hμ 1⟩)
  sum_pos {μ} hμ := by
    rw [mem_wedgeCone] at hμ
    rw [Fin.sum_univ_two]
    rcases hμ with ⟨h0, h1⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> linarith

/-- `wedgeCone` is not convex: it contains `(1, -2/5)` and `(1, 1/10)` but not their midpoint
`(1, -3/20)`. -/
theorem not_convex_wedgeCone : ¬ Convex ℝ wedgeCone := by
  intro h
  have hx : (![1, -2 / 5] : Fin 2 → ℝ) ∈ wedgeCone := mem_wedgeCone.2 (by norm_num)
  have hy : (![1, 1 / 10] : Fin 2 → ℝ) ∈ wedgeCone := mem_wedgeCone.2 (by norm_num)
  have hm := h hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  rw [mem_wedgeCone] at hm
  norm_num at hm

/-- `wedgeCone` is not stable under adding the positive quadrant `Γ_2`:
`(1, -2/5) ∈ wedgeCone` and `(1/100, 1/4) ∈ Γ_2`, but their sum `(101/100, -3/20)` is not in
`wedgeCone`. -/
theorem add_notMem_wedgeCone :
    (![1, -2 / 5] : Fin 2 → ℝ) ∈ wedgeCone ∧
      (![1, -2 / 5] : Fin 2 → ℝ) + ![1 / 100, 1 / 4] ∉ wedgeCone := by
  refine ⟨mem_wedgeCone.2 (by norm_num), fun h ↦ ?_⟩
  rw [mem_wedgeCone] at h
  norm_num at h

/-! ### Infinite intersections -/

/-- The cone `{μ₀ + μ₁ > 0, μᵢ > -ε (μ₀ + μ₁)}`. -/
def epsCone (ε : ℝ) : Set (Fin 2 → ℝ) :=
  {μ | 0 < μ 0 + μ 1 ∧ -(ε * (μ 0 + μ 1)) < μ 0 ∧ -(ε * (μ 0 + μ 1)) < μ 1}

/-- Membership in `epsCone ε` in terms of the two coordinates. -/
@[simp]
theorem mem_epsCone {ε : ℝ} {μ : Fin 2 → ℝ} :
    μ ∈ epsCone ε ↔ 0 < μ 0 + μ 1 ∧ -(ε * (μ 0 + μ 1)) < μ 0 ∧ -(ε * (μ 0 + μ 1)) < μ 1 :=
  Iff.rfl

/-- For `ε ≥ 0`, `{μ₀ + μ₁ > 0, μᵢ > -ε (μ₀ + μ₁)}` is an admissible cone. -/
theorem isAdmissibleCone_epsCone {ε : ℝ} (hε : 0 ≤ ε) : IsAdmissibleCone (epsCone ε) where
  isOpen := by
    have h0 : Continuous fun μ : Fin 2 → ℝ ↦ μ 0 := continuous_apply 0
    have h1 : Continuous fun μ : Fin 2 → ℝ ↦ μ 1 := continuous_apply 1
    simp only [epsCone, ofPred_and]
    exact (isOpen_lt continuous_const (by fun_prop)).inter
      ((isOpen_lt (by fun_prop) h0).inter (isOpen_lt (by fun_prop) h1))
  comp_perm_mem σ μ hμ := by
    obtain ⟨hs, h0, h1⟩ := mem_epsCone.1 hμ
    rw [mem_epsCone]
    rcases Equiv.Perm.eq_one_or_swap_fin_two σ with rfl | rfl
    · exact ⟨hs, h0, h1⟩
    · refine ⟨?_, ?_, ?_⟩ <;>
        simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] <;>
        linarith
  smul_mem {t} ht μ hμ := by
    obtain ⟨hs, h0, h1⟩ := mem_epsCone.1 hμ
    simp only [mem_epsCone, Pi.smul_apply, smul_eq_mul]
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  mem_of_forall_pos hμ := by
    have h0 := hμ 0
    have h1 := hμ 1
    refine mem_epsCone.2 ⟨by linarith, ?_, ?_⟩ <;> nlinarith
  sum_pos hμ := by
    rw [Fin.sum_univ_two]
    exact (mem_epsCone.1 hμ).1

/-- The intersection of the cones `{μ₀ + μ₁ > 0, μᵢ > -ε (μ₀ + μ₁)}` over all `ε > 0` is not
open: it contains `(1, 0)` but not `(1, -t)` for any `0 < t < 1`. -/
theorem not_isOpen_iInter_epsCone : ¬ IsOpen (⋂ ε > (0 : ℝ), epsCone ε) := by
  intro h
  let γ : ℝ → Fin 2 → ℝ := fun t ↦ ![1, -t]
  have hγ : Continuous γ := continuous_pi fun i ↦ by
    fin_cases i
    · exact continuous_const
    · exact continuous_neg
  have h0 : (0 : ℝ) ∈ γ ⁻¹' ⋂ ε > (0 : ℝ), epsCone ε := by
    simp only [mem_preimage, mem_iInter]
    intro ε hε
    refine mem_epsCone.2 ⟨by simp [γ], by simp [γ]; linarith, by simp [γ]; linarith⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (h.preimage hγ) 0 h0
  set t := min (r / 2) (1 / 2)
  have ht : 0 < t := by positivity
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith)
  have hmem := hball (by rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos ht]; exact htr)
  simp only [mem_preimage, mem_iInter] at hmem
  obtain ⟨-, -, h1⟩ := mem_epsCone.1 (hmem t ht)
  simp only [γ, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  nlinarith

end TauCeti.Examples.AdmissibleCone
