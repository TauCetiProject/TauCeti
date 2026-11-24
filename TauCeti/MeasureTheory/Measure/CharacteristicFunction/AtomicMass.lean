/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Exp.Complex

/-!
# Atomic-mass inversion for characteristic functions

For a finite Borel measure `σ` on `ℝ`, the Cesàro time averages of its characteristic function
`charFun σ t = ∫ ξ, exp (t * ξ * I) ∂σ` twisted by `exp (-ω * t * I)` recover the point mass
`σ.real {ω}` at any frequency `ω : ℝ`:

`(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) * charFun σ t → (σ.real {ω} : ℂ)` as `T → ∞`.

## Main results

* `MeasureTheory.tendsto_average_exp_mul_charFun`: recovery of the point mass `σ.real {ω}` from
  twisted time averages of `charFun σ`.

## References

* N. Wiener, *The Fourier Integral and Certain of Its Applications*, Cambridge University Press
  (1933).
* Y. Katznelson, *An Introduction to Harmonic Analysis*, third edition, Cambridge University Press
  (2004), Section I.7.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

/-- Fubini swap turning a twisted time average of `charFun σ` over `[0, T]` (`T > 0`) into the
`σ`-integral of the exponential averaging kernel at shifted frequencies `ξ - ω`. -/
private theorem average_exp_mul_charFun_eq_integral (σ : Measure ℝ) [IsFiniteMeasure σ] (ω : ℝ)
    {T : ℝ} (hT : 0 < T) :
    (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t =
      ∫ ξ, ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
        Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I)) ∂σ := by
  have hint : Integrable
      (fun p : ℝ × ℝ ↦ Complex.exp ((p.1 : ℂ) * ((p.2 - ω : ℝ) : ℂ) * Complex.I))
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod σ) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (Eventually.of_forall fun p ↦ by simp [Complex.norm_exp])
  calc (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t
      = (T⁻¹ : ℂ) * ∫ t in Set.Ioc (0 : ℝ) T,
          (∫ ξ, Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I) ∂σ) := by
        rw [intervalIntegral.integral_of_le hT.le]
        congr 2 with t
        rw [charFun_apply_real, ← integral_const_mul]
        congr 1 with ξ
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
    _ = (T⁻¹ : ℂ) * ∫ ξ, (∫ t in Set.Ioc (0 : ℝ) T,
          Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I)) ∂σ := by
        rw [integral_integral_swap hint]
    _ = ∫ ξ, ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
          Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I)) ∂σ := by
        rw [← integral_const_mul]
        congr 1 with ξ
        rw [intervalIntegral.integral_of_le hT.le]

/-- **Atomic-mass inversion for characteristic functions.** For a finite Borel measure `σ` on `ℝ`
and any frequency `ω : ℝ`, the twisted time averages
`(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) * charFun σ t` converge to `(σ.real {ω} : ℂ)`
as `T → ∞`. -/
theorem tendsto_average_exp_mul_charFun (σ : Measure ℝ) [IsFiniteMeasure σ] (ω : ℝ) :
    Tendsto (fun T : ℝ ↦
      (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t)
      atTop (𝓝 (σ.real {ω} : ℂ)) := by
  let K : ℝ → ℝ → ℂ := fun T ξ ↦
    (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I)
  have hmeas : ∀ᶠ T : ℝ in atTop, AEStronglyMeasurable (K T) σ :=
    Eventually.of_forall fun T ↦
      (continuous_const.mul
        ((intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume)
          (f := fun ξ t : ℝ ↦ Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I))
          (a₀ := 0) (by fun_prop)).comp
          (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ ξ ∂σ, ‖K T ξ‖ ≤ 1 :=
    Eventually.of_forall fun T ↦ Eventually.of_forall fun ξ ↦
      TauCeti.norm_inv_mul_integral_cexp_mul_I_le_one (ξ - ω) T
  have hlim : ∀ᵐ ξ ∂σ, Tendsto (fun T : ℝ ↦ K T ξ) atTop
      (𝓝 (({ω} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) ξ)) :=
    Eventually.of_forall fun ξ ↦ by
      have h := TauCeti.tendsto_inv_mul_integral_cexp_mul_I (ξ - ω)
      have heq : (if ξ - ω = 0 then (1 : ℂ) else 0) =
          ({ω} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) ξ := by
        by_cases hξω : ξ = ω
        · simp [hξω]
        · simp [hξω, sub_ne_zero.mpr hξω]
      rwa [heq] at h
  have htend := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    hmeas hbound (integrable_const (1 : ℝ)) hlim
  have hind : ∫ ξ, ({ω} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) ξ ∂σ = (σ.real {ω} : ℂ) := by
    rw [integral_indicator_const _ (measurableSet_singleton ω), Complex.real_smul, mul_one]
  rw [hind] at htend
  refine htend.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (average_exp_mul_charFun_eq_integral σ ω hT).symm

end MeasureTheory

end
