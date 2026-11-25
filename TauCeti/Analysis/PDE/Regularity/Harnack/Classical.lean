/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.PDE.Regularity.Classical
import TauCeti.Analysis.PDE.Regularity.InverseCoercive
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Pointwise Harnack inequalities for classical divergence-form solutions

For a classical solution with continuously differentiable principal coefficients, Green's identity
provides the weak equation on an interior ball. The weak Moser estimates on that ball give
pointwise bounds for the continuous solution. The lower-order estimate allows measurable drift
and potential and uses bounds on their rescaled sizes.

## Main statements

* `TauCeti.PDE.exists_pos_forall_le_mul_of_divMatrixGradient_eq_zero`: the pointwise estimate for
  the principal equation, uniform over coefficient fields with a fixed upper bound on the squared
  ellipticity ratio.
* `TauCeti.PDE.exists_pos_forall_le_mul_of_divMatrixGradient_eq_lowerOrder`: the pointwise
  estimate in the presence of drift and potential.

Otis Chodosh proved the principal-equation bridge and estimate. Riccardo Brasca extended the
argument to measurable drift and potential.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.20.
-/

public noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace Filter
open scoped ContDiff Distributions Gradient InnerProductSpace Matrix Topology

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]

local notation "E" => EuclideanSpace ℝ ι

variable [DecidableEq ι]

include μ in
/-- For a nonnegative classical solution of `div(A ∇g) = 0` on the fourfold ball,
Moser's pointwise comparison constant on the inner ball depends only on an upper bound for the
squared ellipticity ratio, dimension and normalization of the additive Haar measure. The ambient
open set contains the closed fourfold ball and carries the differentiability hypotheses. -/
theorem exists_pos_forall_le_mul_of_divMatrixGradient_eq_zero (ratio : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Opens E} {a : E → Matrix ι ι ℝ} {g : E → ℝ}
      {lam Lam : ℝ} {x₀ : E} {r : ℝ},
      closedBall x₀ (4 * r) ⊆ U → (∀ i j, ContDiffOn ℝ 1 (fun x ↦ a x i j) U) →
      ContDiffOn ℝ 2 g U →
      UniformlyEllipticOn (ball x₀ (4 * r)) a lam Lam → Lam ^ 2 / lam ≤ ratio * lam →
      (∀ᵐ x ∂μ.restrict (ball x₀ (4 * r)), 0 ≤ g x) →
      (∀ᵐ x ∂μ.restrict (ball x₀ (4 * r)), divMatrixGradient a g x = 0) →
      ∀ y ∈ ball x₀ r, ∀ z ∈ ball x₀ r, g y ≤ C * g z := by
  classical
  obtain ⟨C, hC, hH⟩ := exists_ae_ae_value_le_mul_value_of_isUniformlyEllipticAE (mu := μ) ratio
  refine ⟨C, hC, ?_⟩
  intro U a g lam Lam x₀ r hsub ha hg hA hratio hg₀ heq
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsmall : ball x₀ r ⊆ ball x₀ (4 * r) := ball_subset_ball (by linarith)
  obtain ⟨v, hv, hweak, haB⟩ := exists_w1p_weak_ball (b := 0) (c := 0) hsub ha hg
    hA.upper_nonneg (fun x hx ↦ hA.upper_bound hx) MemLp.zero MemLp.zero (by simpa using heq)
  have hv₀ : ∀ᵐ x ∂μ.restrict (ball x₀ (4 * r)), 0 ≤ W1p.value v x := by
    filter_upwards [hv, hg₀] with x hx hpos
    exact hx ▸ hpos
  have hae := hH (hA.isUniformlyEllipticAE isOpen_ball.measurableSet.nullMeasurableSet)
    hratio haB hweak hv₀
  exact ContinuousOn.forall_le_mul_of_ae_ae
    (hg.continuousOn.mono (hsmall.trans (ball_subset_closedBall.trans hsub))) isOpen_ball
    (ae_mono (Measure.restrict_mono hsmall le_rfl) hv) hae

include μ in
/-- Moser's pointwise Harnack estimate for a nonnegative classical solution with bounded measurable
drift and potential. The comparison constant depends on the ellipticity bounds, dimension,
normalization of the Haar measure and the bound on the rescaled lower-order coefficients. -/
theorem exists_pos_forall_le_mul_of_divMatrixGradient_eq_lowerOrder (lam Lam σ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Opens E} {a : E → Matrix ι ι ℝ} {b : E → E} {c g : E → ℝ}
      {β γ r : ℝ} {x₀ : E},
      let R := 16 * √(Fintype.card ι : ℝ) * r
      closedBall x₀ R ⊆ U → (∀ i j, ContDiffOn ℝ 1 (fun x ↦ a x i j) U) →
      ContDiffOn ℝ 2 g U → UniformlyEllipticOn (ball x₀ R) a lam Lam →
      AEStronglyMeasurable b (μ.restrict (ball x₀ R)) →
      AEStronglyMeasurable c (μ.restrict (ball x₀ R)) →
      (∀ x ∈ ball x₀ R, ‖b x‖ ≤ β) → (∀ x ∈ ball x₀ R, ‖c x‖ ≤ γ) →
      (∀ᵐ x ∂μ.restrict (ball x₀ R), 0 ≤ g x) →
      (∀ᵐ x ∂μ.restrict (ball x₀ R), divMatrixGradient a g x = ⟪b x, ∇ g x⟫_ℝ + c x * g x) →
      β * r ≤ σ * lam → γ * r ^ 2 ≤ σ * lam →
      ∀ y ∈ ball x₀ r, ∀ z ∈ ball x₀ r, g y ≤ C * g z := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, ?_⟩
    intro U a b c g β γ r x₀ R _ _ _ _ _ _ _ _ _ _ _ _ y _ z _
    rw [Subsingleton.elim y z, one_mul]
  obtain ⟨C, hC, hH⟩ :=
    exists_ae_ae_value_le_mul_value_lowerOrder (mu := μ) (lam := lam) (Lam := Lam) σ
  refine ⟨C, hC, ?_⟩
  intro U a b c g β γ r x₀ R hsub ha hg hA hb hc hb' hc' hg₀ heq hβ hγ
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hrR : r ≤ R := by
    have hsqrt := Real.one_le_sqrt.2 (Nat.one_le_cast.2 (Fintype.card_pos (α := ι)))
    dsimp [R]
    nlinarith [mul_le_mul_of_nonneg_right hsqrt hr.le]
  have hsmall : ball x₀ r ⊆ ball x₀ R := ball_subset_ball hrR
  have hbLp := memLp_top_of_bound hb β ((ae_restrict_mem isOpen_ball.measurableSet).mono hb')
  have hcLp := memLp_top_of_bound hc γ ((ae_restrict_mem isOpen_ball.measurableSet).mono hc')
  obtain ⟨v, hv, hweak, haB⟩ := exists_w1p_weak_ball hsub ha hg hA.upper_nonneg
    (fun x hx ↦ hA.upper_bound hx) hbLp hcLp heq
  have hv₀ : ∀ᵐ x ∂μ.restrict (ball x₀ R), 0 ≤ W1p.value v x := by
    filter_upwards [hv, hg₀] with x hx hpos
    exact hx ▸ hpos
  have hae := hH (Omega := ⟨ball x₀ R, isOpen_ball⟩) hA haB hb hc hb' hc' hweak hv₀
    Subset.rfl hβ hγ
  exact ContinuousOn.forall_le_mul_of_ae_ae
    (hg.continuousOn.mono (hsmall.trans (ball_subset_closedBall.trans hsub))) isOpen_ball
    (ae_mono (Measure.restrict_mono hsmall le_rfl) hv) hae

end TauCeti.PDE
