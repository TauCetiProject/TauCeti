/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.Regularity.Classical
import TauCeti.Analysis.PDE.Regularity.Harnack
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
  the principal equation, uniform in the ellipticity ratio.
* `TauCeti.PDE.exists_pos_forall_le_mul_of_divMatrixGradient_eq_lowerOrder`: the pointwise
  estimate in the presence of drift and potential.

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

private theorem forall_energyFormH1_eq_zero_of_forall_testFunction
    {U : Opens E} {a : E → Matrix ι ι ℝ} {b : E → E} {c : E → ℝ} {u : W1p μ U 2}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (μ.restrict U))
    (htest : ∀ φ : 𝓓(U, ℝ), energyFormH1 a b c u (W1p.ofTestFunctionₗ μ U 2 φ) = 0) :
    ∀ w : W1p0 μ U 2, energyFormH1 a b c u (w : W1p μ U 2) = 0 := by
  have hzero (f : E → ℝ) : ∫ x in U, (0 : Lp ℝ 2 (μ.restrict U)) x * f x ∂μ = 0 :=
    integral_eq_zero_of_ae ((Lp.coeFn_zero ℝ 2 (μ.restrict U)).mono fun _ hx ↦ by
      simp only [hx, Pi.zero_apply, zero_mul])
  have h := forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff 0 u
  simp only [hzero] at h
  exact h.mpr htest

private theorem forall_le_mul_of_ae_ae {U : Opens E} {B : Set E} {u : W1p μ U 2}
    {g : E → ℝ} {C : ℝ} (hB : IsOpen B) (hg : ContinuousOn g B)
    (hval : W1p.value u =ᵐ[μ.restrict B] g)
    (hae : ∀ᵐ x ∂μ.restrict B, ∀ᵐ y ∂μ.restrict B, W1p.value u y ≤ C * W1p.value u x) :
    ∀ y ∈ B, ∀ x ∈ B, g y ≤ C * g x := by
  have hall : ∀ᵐ x ∂μ.restrict B, ∀ y ∈ B, g y ≤ C * g x := by
    filter_upwards [hae, hval] with x hx hx'
    refine ContinuousOn.le_of_ae_le (μ := μ) hB hg continuousOn_const ?_
    filter_upwards [hx, hval] with y hy hy'
    simpa only [hy', hx'] using hy
  intro y hy
  exact ContinuousOn.le_of_ae_le (μ := μ) hB continuousOn_const (continuousOn_const.mul hg)
    (hall.mono fun _ hx ↦ hx y hy)

private theorem exists_w1p_weak_ball {U : Opens E} {a : E → Matrix ι ι ℝ}
    {b : E → E} {c g : E → ℝ} {x₀ : E} {R Lam : ℝ}
    (hsub : closedBall x₀ R ⊆ U) (ha : ∀ i j, ContDiffOn ℝ 1 (fun x ↦ a x i j) U)
    (hg : ContDiffOn ℝ 2 g U)
    (hLam : 0 ≤ Lam)
    (hA : ∀ x ∈ ball x₀ R, ∀ η ξ : E,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb : MemLp b ⊤ (μ.restrict (ball x₀ R))) (hc : MemLp c ⊤ (μ.restrict (ball x₀ R)))
    (hg₀ : ∀ᵐ x ∂μ.restrict (ball x₀ R), 0 ≤ g x)
    (heq : ∀ᵐ x ∂μ.restrict (ball x₀ R),
      divMatrixGradient a g x = ⟪b x, ∇ g x⟫_ℝ + c x * g x) :
    let B : Opens E := ⟨ball x₀ R, isOpen_ball⟩
    ∃ v : W1p μ B 2, W1p.value v =ᵐ[μ.restrict B] g ∧
      (∀ w : W1p0 μ B 2, energyFormH1 a b c v (w : W1p μ B 2) = 0) ∧
      (∀ᵐ x ∂μ.restrict B, 0 ≤ W1p.value v x) ∧ AEStronglyMeasurable a (μ.restrict B) := by
  classical
  let B : Opens E := ⟨ball x₀ R, isOpen_ball⟩
  have hBU : (B : Set E) ⊆ U := ball_subset_closedBall.trans hsub
  obtain ⟨v, hv, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    (mu := μ) (p := 2) (Omega := B) U.isOpen (hg.of_le one_le_two) (isCompact_closedBall x₀ R)
    ball_subset_closedBall hsub
  have haU : ContinuousOn (fun x ↦ (a x : ι → ι → ℝ)) U :=
    continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ (ha i j).continuousOn
  have haBpi : AEStronglyMeasurable (fun x ↦ (a x : ι → ι → ℝ)) (μ.restrict B) :=
    ContinuousOn.aestronglyMeasurable (β := ι → ι → ℝ)
      (haU.mono hBU) B.isOpen.measurableSet
  have haB : AEStronglyMeasurable a (μ.restrict B) := haBpi
  have hprincipal := memLp_energyIntegrand_of_bounds (Omega := B) (b := 0) (c := 0)
    (beta := 0) (gamma := 0) hLam haB aestronglyMeasurable_const
    aestronglyMeasurable_const hA (by simp) (by simp)
  have hg₁ : ContDiffOn ℝ 1 (∇ g) B :=
    (toDual ℝ E).symm.contDiff.comp_contDiffOn
      ((hg.mono hBU).fderiv_of_isOpen B.isOpen (by norm_num))
  have hq (i : ι) : ContDiffOn ℝ 1
      (fun x ↦ matrixBilinearForm (a x) (EuclideanSpace.basisFun ι ℝ i) (∇ g x)) B := by
    simp only [matrixBilinearForm_apply, dotProduct, Matrix.mulVec]
    exact ContDiffOn.sum fun j _ ↦ contDiffOn_const.mul
      (ContDiffOn.sum fun k _ ↦ ((ha j k).mono hBU).mul ((contDiffOn_piLp 2).1 hg₁ k))
  refine ⟨v, hv, forall_energyFormH1_eq_zero_of_forall_testFunction
    (memLp_energyIntegrand_of_memLp_top hLam haB hA hb hc)
    (energyFormH1_ofTestFunction_eq_zero_of_divMatrixGradient_eq_lowerOrder
      (hg.mono hBU) hq hprincipal hb hc hv heq), ?_, haB⟩
  filter_upwards [hv, hg₀] with x hx hpos
  exact hx ▸ hpos

variable [DecidableEq ι]

include μ in
/-- For a nonnegative classical solution of `div(A ∇g) = 0` on the fourfold ball,
Moser's pointwise comparison constant on the inner ball depends only on the ellipticity ratio,
dimension and normalization of the additive Haar measure. The ambient open set contains the
closed fourfold ball and carries the differentiability hypotheses. -/
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
  obtain ⟨v, hv, hweak, hv₀, haB⟩ := exists_w1p_weak_ball (b := 0) (c := 0) hsub ha hg
    hA.upper_nonneg (fun x hx ↦ hA.upper_bound hx) MemLp.zero MemLp.zero hg₀ (by simpa using heq)
  have hae := hH (hA.isUniformlyEllipticAE isOpen_ball.measurableSet.nullMeasurableSet)
    hratio haB hweak hv₀
  exact forall_le_mul_of_ae_ae isOpen_ball
    (hg.continuousOn.mono (hsmall.trans (ball_subset_closedBall.trans hsub)))
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
  obtain ⟨v, hv, hweak, hv₀, haB⟩ := exists_w1p_weak_ball hsub ha hg hA.upper_nonneg
    (fun x hx ↦ hA.upper_bound hx) hbLp hcLp hg₀ heq
  have hae := hH (Omega := ⟨ball x₀ R, isOpen_ball⟩) hA haB hb hc hb' hc' hweak hv₀
    Subset.rfl hβ hγ
  exact forall_le_mul_of_ae_ae isOpen_ball
    (hg.continuousOn.mono (hsmall.trans (ball_subset_closedBall.trans hsub)))
    (ae_mono (Measure.restrict_mono hsmall le_rfl) hv) hae

end TauCeti.PDE
