/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Convolution.Basic

/-!
# Smoothing at scale `ε` with derivative bounds from the oscillation

Let `E` be a finite-dimensional real normed space and `F` a real Banach space. If a continuous
map `g : E → F` oscillates by at most `w` on every ball of radius `ε`, that is
`‖g x - g y‖ ≤ w` whenever `dist x y < ε`, then mollifying `g` at scale `ε` gives a smooth map
`h` with

`‖h - g‖ ≤ w`, `‖Dh‖ ≤ C w / ε` and `‖D²h‖ ≤ C w / ε²`,

where `C` depends only on `E` and `F`
(`TauCeti.exists_contDiff_norm_sub_le_and_norm_fderiv_le`). No bound on the size of `g` is used:
the derivatives of `h` are controlled by the oscillation of `g` alone. If `ω` is a modulus of
continuity of `g`, the choice `w = ω(ε)` gives the familiar bounds `ω(ε)`, `C ω(ε) / ε` and
`C ω(ε) / ε²`. These are the bounds used to compare a solution of a second-order equation with
the mollification of its data: the operator applied to the mollification is of size
`ω(ε) / ε²`, which a time of order `ε²` turns into `ω(ε)`.

## The argument

At scale `1`, take `h = ψ ⋆ g` for a smooth nonnegative kernel `ψ` of integral `1` supported in
`ball 0 1`. Then `‖h - g‖ ≤ w` because `h x` is an average of values of `g` on `ball x 1`
(`dist_convolution_le`). The derivatives of `h` are the convolutions of `g` with the derivatives
of `ψ` (`HasCompactSupport.hasFDerivAt_convolution_left`), which have integral zero
(`TauCeti.integral_fderiv_eq_zero_of_hasCompactSupport`), so they are bounded by the oscillation
of `g` on `ball x 1` (`MeasureTheory.norm_convolution_le_of_integral_eq_zero`). The general scale
follows by applying this to `y ↦ g (ε • y)` and composing with `x ↦ ε⁻¹ • x`, which multiplies
the first and second derivatives by `ε⁻¹` and `ε⁻²` (`fderiv_comp_smul`).

## References

* L. C. Evans, *Partial Differential Equations*, Appendix C.4 (mollifiers).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004),
  Chapter 4 (approximation of uniformly continuous initial data).
-/

public section

noncomputable section

open MeasureTheory Metric ContinuousLinearMap
open scoped Convolution ContDiff

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A local shortcut for the norm on `F`-valued gradients. Without these shortcuts, instance search
for the operator norms of `(lsmul ℝ ℝ).precompL E` and of its `precompL`, whose codomains are spaces
of maps into gradients and Hessians, fails: the norm instance on such a space only arises as a
nested instance problem during unification. -/
private local instance instNormedAddCommGroupGradient : NormedAddCommGroup (E →L[ℝ] F) :=
  inferInstance

/-- A local shortcut for scalar operations on `F`-valued gradients, needed for the same reason. -/
private local instance instNormedSpaceGradient : NormedSpace ℝ (E →L[ℝ] F) :=
  inferInstance

/-- A local shortcut for the norm on `F`-valued Hessians, needed for the same reason. -/
private local instance instNormedAddCommGroupHessian : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

/-- A local shortcut for scalar operations on `F`-valued Hessians, needed for the same reason. -/
private local instance instNormedSpaceHessian : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

/-- The smoothing estimate at scale `1`. -/
private theorem exists_contDiff_norm_sub_le_and_norm_fderiv_le_of_dist_lt_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : E → F) (w : ℝ), Continuous g →
      (∀ x y, dist x y < 1 → ‖g x - g y‖ ≤ w) →
      ∃ h : E → F, ContDiff ℝ ∞ h ∧ (∀ x, ‖h x - g x‖ ≤ w) ∧
        (∀ x, ‖fderiv ℝ h x‖ ≤ C * w) ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C * w := by
  borelize E
  set μ : Measure E := Measure.addHaar
  -- A smooth nonnegative kernel of integral `1` whose closed support lies in `ball 0 1`.
  let φ : ContDiffBump (0 : E) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  set ψ : E → ℝ := φ.normed μ
  have hψd : ContDiff ℝ ∞ ψ := φ.contDiff_normed
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hψs : tsupport ψ ⊆ ball 0 1 := by
    rw [φ.tsupport_normed_eq]
    exact closedBall_subset_ball (by norm_num)
  have hψ1 : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψd.fderiv_right le_rfl
  have hψ1c : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv (𝕜 := ℝ)
  have hψ2c : HasCompactSupport (fderiv ℝ (fderiv ℝ ψ)) := hψ1c.fderiv (𝕜 := ℝ)
  set L₁ := (lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompL E
  set L₂ := L₁.precompL E
  set C₁ := ‖L₁‖ * ∫ t, ‖fderiv ℝ ψ t‖ ∂μ
  set C₂ := ‖L₂‖ * ∫ t, ‖fderiv ℝ (fderiv ℝ ψ) t‖ ∂μ
  have hC₁ : 0 ≤ C₁ := mul_nonneg (opNorm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)
  have hC₂ : 0 ≤ C₂ := mul_nonneg (opNorm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun g w hg hw ↦ ?_⟩
  have hw0 : 0 ≤ w := by simpa using hw 0 0 (by simp)
  have hgl : LocallyIntegrable g μ := hg.locallyIntegrable
  have hosc : ∀ x, ∀ y ∈ ball x 1, dist (g y) (g x) ≤ w := fun x y hy ↦ by
    rw [dist_eq_norm]
    exact hw y x hy
  -- The first two derivatives of `ψ ⋆ g` are the convolutions with the derivatives of `ψ`.
  have hD : ∀ x, fderiv ℝ (ψ ⋆[lsmul ℝ ℝ, μ] g) x = (fderiv ℝ ψ ⋆[L₁, μ] g) x := fun x ↦
    (hψc.hasFDerivAt_convolution_left _ (hψd.of_le (by simp)) hgl x).fderiv
  have hD2 : ∀ x, fderiv ℝ (fderiv ℝ (ψ ⋆[lsmul ℝ ℝ, μ] g)) x =
      (fderiv ℝ (fderiv ℝ ψ) ⋆[L₂, μ] g) x := fun x ↦ by
    rw [funext hD]
    exact (hψ1c.hasFDerivAt_convolution_left L₁ (hψ1.of_le (by simp)) hgl x).fderiv
  refine ⟨ψ ⋆[lsmul ℝ ℝ, μ] g, hψc.contDiff_convolution_left _ hψd hgl, fun x ↦ ?_, fun x ↦ ?_,
    fun x ↦ ?_⟩
  · rw [← dist_eq_norm]
    exact dist_convolution_le hw0
      (φ.support_normed_eq.trans_subset (ball_subset_ball (by norm_num))) φ.nonneg_normed
      φ.integral_normed hg.aestronglyMeasurable (hosc x)
  · rw [hD]
    refine (norm_convolution_le_of_integral_eq_zero L₁ hw0
      ((hψd.continuous_fderiv (by simp)).integrable_of_hasCompactSupport hψ1c)
      (integral_fderiv_eq_zero_of_hasCompactSupport (hψd.of_le (by simp)) hψc)
      ((support_fderiv_subset ℝ).trans hψs) hg.aestronglyMeasurable (hosc x)).trans ?_
    nlinarith
  · rw [hD2]
    refine (norm_convolution_le_of_integral_eq_zero L₂ hw0
      ((hψ1.continuous_fderiv (by simp)).integrable_of_hasCompactSupport hψ2c)
      (integral_fderiv_eq_zero_of_hasCompactSupport (hψ1.of_le (by simp)) hψ1c)
      ((support_fderiv_subset ℝ).trans ((tsupport_fderiv_subset ℝ).trans hψs))
      hg.aestronglyMeasurable (hosc x)).trans ?_
    nlinarith

/-- **Smoothing at scale `ε` with derivative bounds from the oscillation.** There is a constant
`C`, depending only on `E` and `F`, with the following property. Let `ε > 0` and let
`g : E → F` be continuous with `‖g x - g y‖ ≤ w` whenever `dist x y < ε`. Then there is a smooth
`h : E → F` with `‖h x - g x‖ ≤ w`, `‖Dh x‖ ≤ C w / ε` and `‖D²h x‖ ≤ C w / ε²` for every `x`.

No bound on `g` itself is assumed. For a modulus of continuity `ω` of `g`, take `w = ω(ε)`. -/
theorem exists_contDiff_norm_sub_le_and_norm_fderiv_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ∀ (g : E → F) (w : ℝ), Continuous g →
      (∀ x y, dist x y < ε → ‖g x - g y‖ ≤ w) →
      ∃ h : E → F, ContDiff ℝ ∞ h ∧ (∀ x, ‖h x - g x‖ ≤ w) ∧
        (∀ x, ‖fderiv ℝ h x‖ ≤ C * w / ε) ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C * w / ε ^ 2 := by
  obtain ⟨C, hC, hone⟩ :=
    exists_contDiff_norm_sub_le_and_norm_fderiv_le_of_dist_lt_one (E := E) (F := F)
  refine ⟨C, hC, fun {ε} hε g w hg hw ↦ ?_⟩
  -- Rescale `g` to oscillate by at most `w` on balls of radius `1`.
  obtain ⟨h, hd, h0, h1, h2⟩ := hone (fun y ↦ g (ε • y)) w (hg.comp (continuous_const_smul ε))
    fun x y hxy ↦ hw _ _ (by
      rw [dist_smul₀, Real.norm_of_nonneg hε.le]
      nlinarith [dist_nonneg (x := x) (y := y)])
  have hD : fderiv ℝ (fun x ↦ h (ε⁻¹ • x)) = fun x ↦ ε⁻¹ • fderiv ℝ h (ε⁻¹ • x) :=
    funext fun x ↦ fderiv_comp_smul (f := h) ε⁻¹
  -- Rescaling multiplies the second derivative by `ε⁻¹ ^ 2`.
  have hD2 : ∀ x, fderiv ℝ (fderiv ℝ (fun x ↦ h (ε⁻¹ • x))) x =
      ε⁻¹ ^ 2 • fderiv ℝ (fderiv ℝ h) (ε⁻¹ • x) := fun x ↦ by
    have hdiff : DifferentiableAt ℝ (fun y ↦ fderiv ℝ h (ε⁻¹ • y)) x :=
      ((hd.fderiv_right (m := ∞) le_rfl).differentiable (by simp)).differentiableAt.comp x
        (differentiableAt_id.const_smul ε⁻¹)
    rw [hD, fderiv_fun_const_smul hdiff, fderiv_comp_smul (f := fderiv ℝ h), smul_smul, sq]
  refine ⟨fun x ↦ h (ε⁻¹ • x), hd.comp (contDiff_const_smul _), fun x ↦ ?_, fun x ↦ ?_,
    fun x ↦ ?_⟩
  · simpa [smul_inv_smul₀ hε.ne'] using h0 (ε⁻¹ • x)
  · rw [hD, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (h1 _) (inv_nonneg.2 hε.le)
  · calc ‖fderiv ℝ (fderiv ℝ (fun x ↦ h (ε⁻¹ • x))) x‖
        = ε⁻¹ ^ 2 * ‖fderiv ℝ (fderiv ℝ h) (ε⁻¹ • x)‖ := by
          rw [hD2, norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ε⁻¹ ^ 2 * (C * w) := by gcongr; exact h2 _
      _ = C * w / ε ^ 2 := by field_simp

end TauCeti

end
