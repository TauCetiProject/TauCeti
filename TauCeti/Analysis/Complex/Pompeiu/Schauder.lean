/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Schauder
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Uniform smooth-data Hölder gain for the actual Cauchy transform

The normalized integral `π⁻¹ ∫ (w-z)⁻¹ f(z)` gains one derivative, with a fixed-disc estimate
depending only on the supremum and Hölder constant of the source. The smooth-data estimate is
obtained from the actual Newtonian potential through `T = -4∂N`, with all normalizations fixed.
-/

public noncomputable section

open Complex ContinuousLinearMap Metric MeasureTheory
open scoped Convolution NNReal ContDiff

namespace TauCeti

private def newtonianToCauchy : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ :=
  (-2 : ℂ) • (ofRealCLM.comp (apply ℝ ℝ 1) - I • ofRealCLM.comp (apply ℝ ℝ I))

private theorem newtonianToCauchy_apply (L : ℂ →L[ℝ] ℝ) :
    newtonianToCauchy L = -2 * ((L 1 : ℂ) - I * (L I : ℂ)) := by
  simp [newtonianToCauchy, smul_eq_mul]

private theorem norm_newtonianToCauchy_le : ‖newtonianToCauchy‖ ≤ 4 := by
  apply opNorm_le_bound _ (by norm_num)
  intro L
  rw [newtonianToCauchy_apply, norm_mul]
  have h1 := L.le_opNorm 1
  have hi := L.le_opNorm I
  simp only [norm_one, norm_I, mul_one, Real.norm_eq_abs] at h1 hi
  calc
    _ = 2 * ‖(L 1 : ℂ) - I * (L I : ℂ)‖ := by norm_num
    _ ≤ 2 * (‖(L 1 : ℂ)‖ + ‖I * (L I : ℂ)‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ 4 * ‖L‖ := by
      simp only [norm_real, norm_mul, norm_I, one_mul, Real.norm_eq_abs]
      linarith

/-- The actual normalized Cauchy transform of smooth compactly supported real data gains one
Hölder derivative on each fixed output disc. The estimate uses only the source supremum and
Hölder constant. -/
theorem exists_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul_real
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (c : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → ℝ} {H M : ℝ≥0}, ContDiff ℝ ∞ f →
      Function.support f ⊆ closedBall c r → HolderWith H α f → (∀ x, ‖f x‖ ≤ M) →
      let T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (f z : ℂ)
      ContDiff ℝ ∞ T ∧ HolderOnWith (C * (H + M)) α (fderiv ℝ T) (closedBall c R) ∧
        ∀ x ∈ closedBall c R, ‖fderiv ℝ T x‖ ≤ C * (H + M) := by
  obtain ⟨C, hC⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_planarNewtonianKernel_convolution hα hα1 c hr hR
  refine ⟨4 * C, fun {f H M} hf hs hH hM ↦ ?_⟩
  intro T
  let u := planarNewtonianKernel ⋆ f
  have hc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
  have hu : ContDiff ℝ ∞ u := contDiff_planarNewtonianKernel_convolution hf hc
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hT : T = newtonianToCauchy ∘ fderiv ℝ u := by
    funext w
    rw [Function.comp_apply, newtonianToCauchy_apply]
    exact hc.pi_inv_smul_integral_sub_inv_smul_eq_fderiv_planarNewtonianKernel_convolution
      (hf.of_le (by simp)) w
  have hDT (x : ℂ) : fderiv ℝ T x = newtonianToCauchy.comp (fderiv ℝ (fderiv ℝ u) x) := by
    rw [hT]
    exact (newtonianToCauchy.hasFDerivAt.comp x
      ((hDu.differentiable (by simp)) x).hasFDerivAt).fderiv
  obtain ⟨hHS, hDS⟩ := hC hf hs hH hM
  refine ⟨by rw [hT]; exact newtonianToCauchy.contDiff.comp hDu, ?_, fun x hx ↦ ?_⟩
  · apply HolderOnWith.of_dist_le
    intro x hx y hy
    rw [dist_eq_norm, hDT x, hDT y, ← comp_sub]
    calc
      _ ≤ ‖newtonianToCauchy‖ * ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ :=
        opNorm_comp_le _ _
      _ ≤ 4 * ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ :=
        mul_le_mul norm_newtonianToCauchy_le (norm_fderiv_fderiv_sub (𝕜 := ℝ) u x y).le
          (norm_nonneg (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)) (by norm_num)
      _ ≤ 4 * ((C * (H + M) : ℝ≥0) * dist x y ^ (α : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
        simpa only [dist_eq_norm] using hHS.dist_le hx hy
      _ = _ := by push_cast; ring
  · rw [hDT x]
    calc
      _ ≤ ‖newtonianToCauchy‖ * ‖fderiv ℝ (fderiv ℝ u) x‖ := opNorm_comp_le _ _
      _ ≤ 4 * ‖iteratedFDeriv ℝ 2 u x‖ :=
        mul_le_mul norm_newtonianToCauchy_le (by
          rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ u), norm_iteratedFDeriv_fderiv])
          (norm_nonneg (fderiv ℝ (fderiv ℝ u) x)) (by norm_num)
      _ ≤ 4 * ((C * (H + M) : ℝ≥0) : ℝ) := by gcongr; exact hDS x hx
      _ = _ := by push_cast; ring

end TauCeti
