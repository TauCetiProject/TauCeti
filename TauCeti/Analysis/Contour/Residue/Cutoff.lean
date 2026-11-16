/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Complex
public import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
public import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.MeasureTheory.Integral.Circle.Integral

/-!
# The residue as the integral of a cutoff against a meromorphic function

Let `f` be meromorphic at a point `z₀` of the open disc `|z - c| < R` and holomorphic at every
other point of the closed disc `|z - c| ≤ R`, and let `χ` be a real function, `C¹` at every point
of the closed disc, equal to `1` near `z₀` and vanishing on the circle `|z - c| = R`. The `1`-form
`(1 - χ) f dz` is then `C¹` at every point of the closed disc
(`TauCeti.Contour.contDiffAt_one_sub_mul_smul_dzForm`), it agrees with `f dz` on the boundary
circle, and away from `z₀` its exterior derivative is `-dχ ∧ f dz`, since `f dz` is closed
(`TauCeti.Contour.extDeriv_one_sub_mul_smul_dzForm_apply`).
Stokes' formula on the disc (`TauCeti.integral_extDeriv_closedBall`) together with the residue
theorem on a circle gives
`∫_{|z - c| ≤ R} d((1 - χ) f dz) = ∮_{|z - c| = R} f dz = 2πi · Res_{z₀} f`
(`TauCeti.Contour.integral_extDeriv_one_sub_mul_smul_dzForm_closedBall_eq_residue`), and in terms
of the derivative of the cutoff,
`∫_{|z - c| ≤ R} f · (i ∂ₓχ - ∂_yχ) = -2πi · Res_{z₀} f`
(`TauCeti.Contour.integral_mul_fderiv_sub_fderiv_closedBall_eq_neg_residue`).

This is the computation in a coordinate disc in the proof of the residue theorem on a compact
Riemann surface by Stokes' theorem: the contribution of a pole of a meromorphic `1`-form to the
integral of `d((1 - Σ χᵢ) ω)` is `2πi` times its residue.

## Main declarations

* `TauCeti.Contour.integral_extDeriv_one_sub_mul_smul_dzForm_closedBall_eq_residue`: the integral
  of `d((1 - χ) f dz)` over the disc is `2πi · Res_{z₀} f`.
* `TauCeti.Contour.integral_mul_fderiv_sub_fderiv_closedBall_eq_neg_residue`: the same statement
  with the integrand written through the derivative of `χ`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 10.21 (the residue theorem, proved by Stokes' theorem with cutoffs at the poles).
-/

public section

noncomputable section

open Complex Filter Metric MeasureTheory Set
open scoped Real Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {χ : ℂ → ℝ} {c z₀ z : ℂ} {R : ℝ}

/-- The cutoff `1`-form `(1 - χ) f dz` vanishes near any point near which `χ = 1`. -/
private theorem one_sub_mul_smul_dzForm_eventuallyEq_zero (hχz : χ =ᶠ[𝓝 z] 1) :
    (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) =ᶠ[𝓝 z] fun _ ↦ 0 := by
  filter_upwards [hχz] with y hy
  simp only [hy, Pi.one_apply, sub_self, ofReal_zero, zero_mul]
  exact zero_smul ℂ dzForm

/-- The cutoff `1`-form `(1 - χ) f dz` is `Cⁿ` at `z` when `χ` and `f` are, and also when `χ = 1`
near `z`, whatever `f` is. -/
theorem contDiffAt_one_sub_mul_smul_dzForm {n : WithTop ℕ∞} (hχ : ContDiffAt ℝ n χ z)
    (hf : ContDiffAt ℝ n f z ∨ χ =ᶠ[𝓝 z] 1) :
    ContDiffAt ℝ n (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) z := by
  rcases hf with hf | hχz
  · exact ((ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.sub hχ)).mul hf).smul_const
      dzForm
  · exact contDiffAt_const.congr_of_eventuallyEq (one_sub_mul_smul_dzForm_eventuallyEq_zero hχz)

/-- **The residue as the integral of the exterior derivative of a cutoff `1`-form.** Let `f` be
meromorphic at a point `z₀` of the open disc of radius `R` about `c` and holomorphic at every other
point of the closed disc, and let `χ` be a real function, `C¹` at every point of the closed disc,
equal to `1` near `z₀` and vanishing on the boundary circle. Then the integral of
`d((1 - χ) f dz)` over the disc is `2πi · Res_{z₀} f`. -/
theorem integral_extDeriv_one_sub_mul_smul_dzForm_closedBall_eq_residue (hz₀ : z₀ ∈ ball c R)
    (hf : MeromorphicAt f z₀) (hfa : ∀ z ∈ closedBall c R, z ≠ z₀ → AnalyticAt ℂ f z)
    (hχ : ∀ z ∈ closedBall c R, ContDiffAt ℝ 1 χ z) (hχz₀ : χ =ᶠ[𝓝 z₀] 1)
    (hχR : ∀ z ∈ sphere c R, χ z = 0) :
    (∫ z in closedBall c R,
      extDeriv (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) z ![1, I]) =
        2 * π * I * residue f z₀ := by
  have hR := (pos_of_mem_ball hz₀).le
  have hω : ∀ z ∈ closedBall c R,
      ContDiffAt ℝ 1 (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) z := fun z hz ↦ by
    refine contDiffAt_one_sub_mul_smul_dzForm (hχ z hz) ?_
    by_cases hzz₀ : z = z₀
    · exact .inr (hzz₀ ▸ hχz₀)
    · exact .inl ((hfa z hz hzz₀).contDiffAt.restrict_scalars ℝ)
  rw [integral_extDeriv_closedBall hR hω, ← circleIntegral_eq_residue hz₀ hf hfa,
    ← integral_neg_pi_pi_eq_circleIntegral]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp [hχR _ (circleMap_mem_sphere c hR θ), mul_comm]

/-- The exterior derivative of the cutoff `1`-form `(1 - χ) f dz` on a pair of vectors is
`d((1 - χ) f dz)(v, w) = -f · (w dχ(v) - v dχ(w))` at a point `z` where `χ` is real
differentiable and either `f` is complex differentiable (so `f dz` is closed at `z`) or `χ = 1`
near `z` (so both sides vanish). -/
theorem extDeriv_one_sub_mul_smul_dzForm_apply (hχ : DifferentiableAt ℝ χ z)
    (hf : DifferentiableAt ℂ f z ∨ χ =ᶠ[𝓝 z] 1) (v w : ℂ) :
    extDeriv (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) z ![v, w] =
      -(f z * (w * fderiv ℝ χ z v - v * fderiv ℝ χ z w)) := by
  rcases hf with hf | hχz
  · have hω : (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) =
        (fun y ↦ 1 - χ y) • fun y ↦ f y • dzForm := by
      funext y
      rw [Pi.smul_apply', ← real_smul, smul_assoc]
    rw [hω, extDeriv_function_smul (hχ.const_sub 1) ((hf.restrictScalars ℝ).smul_const dzForm),
      hf.extDeriv_smul_dzForm, smul_zero, zero_add,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply_pair]
    simp [fderiv_const_sub]
    ring
  · have hdχ : fderiv ℝ χ z = 0 := by
      rw [hχz.fderiv_eq]
      exact fderiv_const_apply _
    rw [extDeriv_apply_pair, (one_sub_mul_smul_dzForm_eventuallyEq_zero hχz).fderiv_eq, hdχ]
    simp

/-- **The residue as a cutoff integral.** Under the hypotheses of
`TauCeti.Contour.integral_extDeriv_one_sub_mul_smul_dzForm_closedBall_eq_residue`,
`∫_{|z - c| ≤ R} f · (i ∂ₓχ - ∂_yχ) = -2πi · Res_{z₀} f`. Only the region where `χ` is not locally
constant contributes. -/
theorem integral_mul_fderiv_sub_fderiv_closedBall_eq_neg_residue (hz₀ : z₀ ∈ ball c R)
    (hf : MeromorphicAt f z₀) (hfa : ∀ z ∈ closedBall c R, z ≠ z₀ → AnalyticAt ℂ f z)
    (hχ : ∀ z ∈ closedBall c R, ContDiffAt ℝ 1 χ z) (hχz₀ : χ =ᶠ[𝓝 z₀] 1)
    (hχR : ∀ z ∈ sphere c R, χ z = 0) :
    (∫ z in closedBall c R, f z * (I * fderiv ℝ χ z 1 - fderiv ℝ χ z I)) =
      -(2 * π * I * residue f z₀) := by
  rw [← integral_extDeriv_one_sub_mul_smul_dzForm_closedBall_eq_residue hz₀ hf hfa hχ hχz₀ hχR,
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_closedBall fun z hz ↦ ?_
  have hfz : DifferentiableAt ℂ f z ∨ χ =ᶠ[𝓝 z] 1 := by
    by_cases hzz₀ : z = z₀
    · exact .inr (hzz₀ ▸ hχz₀)
    · exact .inl (hfa z hz hzz₀).differentiableAt
  rw [extDeriv_one_sub_mul_smul_dzForm_apply ((hχ z hz).differentiableAt one_ne_zero) hfz 1 I,
    one_mul, neg_neg]

end TauCeti.Contour
