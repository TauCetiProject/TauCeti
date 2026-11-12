/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Complex
public import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
public import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.Calculus.FDeriv.OfReal

/-!
# The residue as the integral of a cutoff against a meromorphic function

Let `f` be meromorphic at `c` and holomorphic on the punctured closed disc `0 < |z - c| ≤ R`, and
let `χ` be a real `C¹` function equal to `1` near `c` and vanishing on the circle `|z - c| = R`.
The `1`-form `(1 - χ) f dz` is then `C¹` on the whole closed disc, it agrees with `f dz` on the
boundary circle, and away from `c` its exterior derivative is `-dχ ∧ f dz`, since `f dz` is closed.
Stokes' formula on the disc (`TauCeti.integral_extDeriv_closedBall`) together with the residue
theorem on a circle gives
`∫_{|z - c| ≤ R} d((1 - χ) f dz) = ∮_{|z - c| = R} f dz = 2πi · Res_c f`
(`TauCeti.Contour.integral_extDeriv_one_sub_smul_dzForm_closedBall`), and in terms of the
derivative of the cutoff,
`∫_{|z - c| ≤ R} f · (i ∂ₓχ - ∂_yχ) = -2πi · Res_c f`
(`TauCeti.Contour.integral_mul_fderiv_cutoff_closedBall`).

This is the computation in a coordinate disc in the proof of the residue theorem on a compact
Riemann surface by Stokes' theorem: the contribution of a pole of a meromorphic `1`-form to the
integral of `d((1 - Σ χᵢ) ω)` is `2πi` times its residue.

## Main declarations

* `TauCeti.Contour.integral_extDeriv_one_sub_smul_dzForm_closedBall`: the integral of
  `d((1 - χ) f dz)` over the disc is `2πi · Res_c f`.
* `TauCeti.Contour.integral_mul_fderiv_cutoff_closedBall`: the same statement with the integrand
  written through the derivative of `χ`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 10.21 (the residue theorem, proved by Stokes' theorem with cutoffs at the poles).
-/

public section

noncomputable section

open Complex Filter Metric MeasureTheory Set
open scoped Real Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {χ : ℂ → ℝ} {c : ℂ} {R : ℝ}

/-- The cutoff `1`-form `(1 - χ) f dz` is `C¹` on the closed disc. -/
private theorem contDiffAt_cutoff_smul_dzForm (hfa : ∀ z ∈ closedBall c R, z ≠ c → AnalyticAt ℂ f z)
    (hχ : ContDiff ℝ 1 χ) (hχc : χ =ᶠ[𝓝 c] 1) :
    ∀ z ∈ closedBall c R, ContDiffAt ℝ 1 (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) z := by
  intro z hz
  by_cases hzc : z = c
  · subst hzc
    refine contDiffAt_const (c := (0 : ℂ [⋀^Fin 1]→L[ℝ] ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hχc] with y hy
    simp only [hy, Pi.one_apply, sub_self, ofReal_zero, zero_mul]
    exact zero_smul ℂ dzForm
  · have hg : ContDiffAt ℝ 1 (fun y ↦ ((1 - χ y : ℝ) : ℂ) * f y) z :=
      (ofRealCLM.contDiff.comp (contDiff_const.sub hχ)).contDiffAt.mul
        ((hfa z hz hzc).contDiffAt.restrict_scalars ℝ)
    exact hg.smul_const dzForm

/-- On the circle the cutoff `1`-form is `f dz`, so its boundary integral is the circle integral
of `f`. -/
private theorem integral_cutoff_smul_dzForm_circle (hR : 0 ≤ R)
    (hχR : ∀ z ∈ sphere c R, χ z = 0) :
    (∫ θ in -π..π, ((((1 - χ (circleMap c R θ) : ℝ) : ℂ) * f (circleMap c R θ)) • dzForm)
      (fun _ ↦ circleMap 0 R θ * I)) = circleIntegral f c R := by
  have hper : Function.Periodic
      (fun θ ↦ (circleMap 0 R θ * I) • f (circleMap c R θ)) (2 * π) := fun θ ↦ by
    simp only [periodic_circleMap 0 R θ, periodic_circleMap c R θ]
  have hshift : circleIntegral f c R =
      ∫ θ in -π..π, (circleMap 0 R θ * I) • f (circleMap c R θ) := by
    rw [circleIntegral]
    simp_rw [deriv_circleMap]
    rw [← zero_add (2 * π), ← hper.intervalIntegral_add_eq (-π) 0,
      show -π + 2 * π = π by ring]
  rw [hshift]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp [hχR _ (circleMap_mem_sphere c hR θ), mul_comm]

/-- **The residue as the integral of the exterior derivative of a cutoff `1`-form.** Let `f` be
meromorphic at `c` and holomorphic on the punctured closed disc of radius `R > 0` about `c`, and
let `χ` be a real `C¹` function equal to `1` near `c` and vanishing on the boundary circle. Then the
integral of `d((1 - χ) f dz)` over the disc is `2πi · Res_c f`. -/
theorem integral_extDeriv_one_sub_smul_dzForm_closedBall (hR : 0 < R) (hf : MeromorphicAt f c)
    (hfa : ∀ z ∈ closedBall c R, z ≠ c → AnalyticAt ℂ f z) (hχ : ContDiff ℝ 1 χ)
    (hχc : χ =ᶠ[𝓝 c] 1) (hχR : ∀ z ∈ sphere c R, χ z = 0) :
    (∫ z in closedBall c R,
      extDeriv (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) z ![1, I]) =
        2 * π * I * residue f c := by
  rw [integral_extDeriv_closedBall hR.le (contDiffAt_cutoff_smul_dzForm hfa hχ hχc),
    integral_cutoff_smul_dzForm_circle hR.le hχR, circleIntegral_eq_residue_of_analyticAt hR hf hfa]

/-- The exterior derivative of the cutoff `1`-form `(1 - χ) f dz` on the standard frame is
`-f · (i ∂ₓχ - ∂_yχ)` throughout the closed disc: away from `c` because `f dz` is closed, and at
`c` because both sides vanish there. -/
theorem extDeriv_one_sub_smul_dzForm_apply (hfa : ∀ z ∈ closedBall c R, z ≠ c → AnalyticAt ℂ f z)
    (hχ : ContDiff ℝ 1 χ) (hχc : χ =ᶠ[𝓝 c] 1) {z : ℂ} (hz : z ∈ closedBall c R) :
    extDeriv (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) z ![1, I] =
      -(f z * (I * fderiv ℝ χ z 1 - fderiv ℝ χ z I)) := by
  by_cases hzc : z = c
  · subst hzc
    have hφ : (fun y ↦ (((1 - χ y : ℝ) : ℂ) * f y) • dzForm) =ᶠ[𝓝 z] fun _ ↦ 0 := by
      filter_upwards [hχc] with y hy
      simp only [hy, Pi.one_apply, sub_self, ofReal_zero, zero_mul]
      exact zero_smul ℂ dzForm
    have hdχ : fderiv ℝ χ z = 0 := by
      rw [hχc.fderiv_eq]
      exact fderiv_const_apply _
    rw [extDeriv_apply_pair, hφ.fderiv_eq, hdχ]
    simp
  · have hd : HasFDerivAt (fun y ↦ ((1 - χ y : ℝ) : ℂ) * f y)
        (((1 - χ z : ℝ) : ℂ) • ((fderiv ℂ f z).restrictScalars ℝ) +
          f z • (ofRealCLM.comp (-fderiv ℝ χ z))) z :=
      ((hχ.differentiable one_ne_zero z).hasFDerivAt.const_sub 1).ofReal_comp.mul
        ((hfa z hz hzc).differentiableAt.hasFDerivAt.restrictScalars ℝ)
    rw [extDeriv_smul_dzForm_apply hd.differentiableAt, hd.fderiv]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_comp, Function.comp_apply,
      neg_apply, ofRealCLM_apply, smul_eq_mul, ofReal_neg]
    have hlin : fderiv ℂ f z I = I * fderiv ℂ f z 1 := by
      rw [← smul_eq_mul, ← (fderiv ℂ f z).map_smul, smul_eq_mul, mul_one]
    rw [hlin]
    ring

/-- **The residue as a cutoff integral.** Under the hypotheses of
`TauCeti.Contour.integral_extDeriv_one_sub_smul_dzForm_closedBall`,
`∫_{|z - c| ≤ R} f · (i ∂ₓχ - ∂_yχ) = -2πi · Res_c f`. Only the annulus where `χ` is not locally
constant contributes. -/
theorem integral_mul_fderiv_cutoff_closedBall (hR : 0 < R) (hf : MeromorphicAt f c)
    (hfa : ∀ z ∈ closedBall c R, z ≠ c → AnalyticAt ℂ f z) (hχ : ContDiff ℝ 1 χ)
    (hχc : χ =ᶠ[𝓝 c] 1) (hχR : ∀ z ∈ sphere c R, χ z = 0) :
    (∫ z in closedBall c R, f z * (I * fderiv ℝ χ z 1 - fderiv ℝ χ z I)) =
      -(2 * π * I * residue f c) := by
  rw [← integral_extDeriv_one_sub_smul_dzForm_closedBall hR hf hfa hχ hχc hχR, ← integral_neg]
  exact setIntegral_congr_fun measurableSet_closedBall fun z hz ↦
    (by rw [extDeriv_one_sub_smul_dzForm_apply hfa hχ hχc hz, neg_neg])

end TauCeti.Contour
