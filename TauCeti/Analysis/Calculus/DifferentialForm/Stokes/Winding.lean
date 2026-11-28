/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.PhaseForm
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Circle.Loop
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Analysis.Contour.Winding.Number.Degree
import TauCeti.Topology.Circle.Normalize

/-!
# Cutoff integrals of phase forms around an annulus

Let `f` be a complex function without zeros on the circle of radius `r` about `c`. Its phase form
`Im (f⁻¹ df)` (`TauCeti.phaseForm`) integrates once around that circle to `2π` times the degree of
the direction map `ζ ↦ f (c + r ζ) / ‖f (c + r ζ)‖` of the circle
(`TauCeti.intervalIntegral_phaseForm_circleMap_eq_two_pi_mul_degree`): the integral is the
imaginary part of `∫ γ'/γ` for `γ = f ∘ circleMap c r`, which is `2πi` times the winding number of
`γ` around `0`.

Let now `Ψ` be a real function equal to `1` on the inner circle and `0` on the outer circle of the
closed annulus `r ≤ ‖z - c‖ ≤ b`, and let `f` be `C²` without zeros on the annulus. Then

`∫_{r ≤ ‖z - c‖ ≤ b} (dΨ ∧ Im (f⁻¹ df))(1, i) = -2π deg`

(`TauCeti.setIntegral_annulus_fderiv_mul_phaseForm_sub_eq_neg_two_pi_mul_degree`). The phase form
is closed away from the zeros of `f` (`TauCeti.extDeriv_phaseForm`), so the integrand is the
exterior derivative of `Ψ Im (f⁻¹ df)`, and Stokes' formula on the annulus
(`TauCeti.integral_extDeriv_annulus`) reduces the integral to the inner circle.

This is the local computation in Chern's proof of the Gauss–Bonnet theorem: the integral of
`dΨ ∧ ω` for the angle form `ω` of a unit vector field near one of its zeros, cut off by `Ψ`,
is `-2π` times the index of the zero.

## Main results

* `TauCeti.intervalIntegral_phaseForm_circleMap_eq_two_pi_mul_degree`: the phase form integrates
  around a circle to `2π` times the degree of the direction map.
* `TauCeti.setIntegral_annulus_fderiv_mul_phaseForm_sub_eq_neg_two_pi_mul_degree`: the cutoff
  integral of the phase form over an annulus is `-2π` times that degree on the inner circle.

## References

* S.-S. Chern, *A simple intrinsic proof of the Gauss–Bonnet formula for closed Riemannian
  manifolds*, Ann. of Math. 45 (1944), 747–752.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace TauCeti

variable {Ψ : ℂ → ℝ} {f : ℂ → ℂ} {c : ℂ} {r b : ℝ}

/-- **The phase form integrates around a circle to `2π` times the degree.** If `f` is `C¹` near
the circle of radius `r` about `c`, and `d : S¹ → S¹` is its direction map
`d ζ = f (c + r ζ) / ‖f (c + r ζ)‖` there, then the phase form `Im (f⁻¹ df)` integrates once
around the circle to `2π` times the degree of `d`. The equation for `d` forces `f` to have no
zero on the circle. -/
theorem intervalIntegral_phaseForm_circleMap_eq_two_pi_mul_degree
    (hf : ∀ θ, ContDiffAt ℝ 1 f (circleMap c r θ)) (d : C(Circle, Circle))
    (hd : ∀ ζ : Circle, (d ζ : ℂ) = f (c + r * ζ) / ‖f (c + r * ζ)‖) :
    ∫ θ in -π..π, phaseForm f (circleMap c r θ) (fun _ ↦ circleMap 0 r θ * I) =
      2 * π * Circle.degree d.toBasedLoop := by
  set γ := f ∘ circleMap c r with hγ
  have hγc : ContDiff ℝ 1 γ := contDiff_iff_contDiffAt.2 fun θ ↦
    (hf θ).comp θ (contDiff_circleMap c r).contDiffAt
  have hne (θ : ℝ) : γ θ ≠ 0 := Circle.ne_zero_of_coe_eq_div_norm (z := d (Circle.exp θ)) <| by
    simpa only [hγ, Function.comp_apply, circleMap, Circle.coe_exp] using hd (Circle.exp θ)
  -- The integrand is the imaginary part of the logarithmic derivative of `γ`.
  have hderiv (θ : ℝ) : deriv γ θ = fderiv ℝ f (circleMap c r θ) (circleMap 0 r θ * I) := by
    exact ((hf θ).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap c r θ) |>.deriv
  have hint : IntervalIntegrable (fun θ ↦ (γ θ - 0)⁻¹ * deriv γ θ) volume (-π) π :=
    Contour.intervalIntegrable_inv_sub_mul_deriv hγc.continuous.continuousOn (fun θ _ ↦ hne θ)
      ((hγc.continuous_deriv le_rfl).intervalIntegrable _ _)
  have hwind := Contour.windingNumber_eq_integral_of_avoidance hγc.continuous.continuousOn
    (fun θ _ ↦ hne θ) hint
  rw [Contour.windingNumber_comp_circleMap_eq_degree_toBasedLoop hγc d hd] at hwind
  have him : ∫ θ in -π..π, phaseForm f (circleMap c r θ) (fun _ ↦ circleMap 0 r θ * I) =
      (∫ θ in -π..π, (γ θ - 0)⁻¹ * deriv γ θ).im := by
    rw [← imCLM_apply, ← imCLM.intervalIntegral_comp_comm hint]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    simp only [hderiv]
    simp [hγ]
  rw [him, ← mul_inv_cancel_left₀ (by simp [Real.pi_ne_zero] : 2 * (π : ℂ) * I ≠ 0)
    (∫ θ in -π..π, (γ θ - 0)⁻¹ * deriv γ θ), ← hwind]
  simp

/-- **The cutoff integral of a phase form over an annulus.** Let `Ψ` be `C¹` and `f` be `C²`
without zeros near the closed annulus `r ≤ ‖z - c‖ ≤ b`, with `0 ≤ r ≤ b`. If `Ψ` is `1` on the
inner circle and `0` on the outer circle, then the integral over the annulus of
`dΨ ∧ Im (f⁻¹ df)` on the positive basis `(1, i)` is `-2π` times the degree of the direction map
`d ζ = f (c + r ζ) / ‖f (c + r ζ)‖` of the inner circle. -/
theorem setIntegral_annulus_fderiv_mul_phaseForm_sub_eq_neg_two_pi_mul_degree (hr : 0 ≤ r)
    (hrb : r ≤ b) (hΨ : ∀ z ∈ {z : ℂ | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b}, ContDiffAt ℝ 1 Ψ z)
    (hf : ∀ z ∈ {z : ℂ | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b}, ContDiffAt ℝ 2 f z)
    (hf₀ : ∀ z ∈ {z : ℂ | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b}, f z ≠ 0)
    (hΨr : ∀ θ, Ψ (circleMap c r θ) = 1) (hΨb : ∀ θ, Ψ (circleMap c b θ) = 0)
    (d : C(Circle, Circle)) (hd : ∀ ζ : Circle, (d ζ : ℂ) = f (c + r * ζ) / ‖f (c + r * ζ)‖) :
    ∫ z in {z : ℂ | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b},
        (fderiv ℝ Ψ z 1 * phaseForm f z (fun _ ↦ I) - fderiv ℝ Ψ z I * phaseForm f z (fun _ ↦ 1)) =
      -(2 * π * Circle.degree d.toBasedLoop) := by
  set A := {z : ℂ | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b}
  have hcirc {s : ℝ} (hs : 0 ≤ s) (hrs : r ≤ s) (hsb : s ≤ b) (θ : ℝ) : circleMap c s θ ∈ A := by
    simp [A, circleMap_sub_center, abs_of_nonneg hs, hrs, hsb]
  let ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ := Ψ • phaseForm f
  have hω (z : ℂ) (hz : z ∈ A) : ContDiffAt ℝ 1 ω z :=
    (hΨ z hz).smul (contDiffAt_phaseForm (hf z hz) (hf₀ z hz) (by norm_num))
  -- Since the phase form is closed, `dω` is `dΨ ∧ Im (f⁻¹ df)`.
  have hdω (z : ℂ) (hz : z ∈ A) : extDeriv ω z ![1, I] =
      fderiv ℝ Ψ z 1 * phaseForm f z (fun _ ↦ I) - fderiv ℝ Ψ z I * phaseForm f z (fun _ ↦ 1) := by
    rw [extDeriv_function_smul ((hΨ z hz).differentiableAt one_ne_zero)
      ((contDiffAt_phaseForm (hf z hz) (hf₀ z hz) le_rfl).differentiableAt one_ne_zero),
      extDeriv_phaseForm (hf z hz) (hf₀ z hz), smul_zero, zero_add,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply_pair]
    simp [smul_eq_mul]
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const (measurable_id.sub_const c).norm).inter
      (measurableSet_le (measurable_id.sub_const c).norm measurable_const)
  rw [← setIntegral_congr_fun hA fun z hz ↦ hdω z hz, integral_extDeriv_annulus c hr hrb hω]
  -- The outer circle contributes nothing, and on the inner circle `ω` is the phase form.
  simp only [ω, Pi.smul_apply', hΨr, hΨb, zero_smul, one_smul]
  rw [ContinuousAlternatingMap.coe_zero]
  simp only [Pi.zero_apply, intervalIntegral.integral_zero, zero_sub]
  rw [intervalIntegral_phaseForm_circleMap_eq_two_pi_mul_degree
    (fun θ ↦ (hf _ (hcirc hr le_rfl hrb θ)).of_le one_le_two) d hd]

end TauCeti
