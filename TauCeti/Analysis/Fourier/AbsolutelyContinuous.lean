/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Fourier coefficients of absolutely continuous functions

For an absolutely continuous function into a finite-dimensional complex normed space on a
compact interval, integration by parts identifies the Fourier coefficients of its almost-everywhere
derivative, including the endpoint contribution. For a closed curve the endpoint term vanishes.
For complex-valued curves, Parseval gives an exact expression for the derivative energy as a
frequency-weighted sum of squared coefficients.
These identities allow sharp periodic inequalities to be proved directly at absolutely
continuous regularity, without a passage through smooth approximation.

The Fourier convention and normalization are Mathlib's `fourierCoeffOn`: the frequency is
`2πn / (b - a)` and Parseval uses the interval average of the squared norm.
The integration-by-parts calculation extends Mathlib's `fourierCoeffOn_of_hasDeriv_right`
to almost-everywhere derivatives; the energy identity uses `hasSum_sq_fourierCoeffOn`.
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval

namespace TauCeti

variable {a b : ℝ}

section VectorValued

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {f f' : ℝ → E}

/-- The Fourier coefficient of an almost-everywhere derivative of an absolutely continuous
function, with the endpoint term retained. The identity holds at every frequency, including
zero, and does not require equal endpoint values. -/
theorem fourierCoeffOn_ae_derivative (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t) (n : ℤ) :
    fourierCoeffOn hab f' n =
      ((b - a)⁻¹ : ℝ) • (fourier (-n) (a : AddCircle (b - a)) • (f b - f a)) +
        (2 * π * I * n / (b - a)) • fourierCoeffOn hab f n := by
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  -- Reduce to the scalar integration-by-parts identity using the separating complex dual.
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun L ↦ ?_
  have hcoeff (g : ℝ → E) (hg : IntervalIntegrable g volume a b) :
      L (fourierCoeffOn hab g n) = fourierCoeffOn hab (fun t ↦ L (g t)) n := by
    have hi : IntervalIntegrable (fun t : ℝ ↦ fourier (-n) (t : AddCircle (b - a)) • g t)
        volume a b := hg.continuousOn_smul ((fourier (-n)).continuous.comp
          (AddCircle.continuous_mk' (b - a))).continuousOn
    rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, L.map_smul_of_tower,
      ← L.intervalIntegral_comp_comm hi]
    simp only [map_smul]
  simp only [map_add, L.map_smul_of_tower, map_sub]
  rw [hcoeff f' (hf.intervalIntegrable_of_ae_hasDerivAt hff'),
    hcoeff f hf.continuousOn.intervalIntegrable]
  have hLf := L.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have hLff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt (fun t ↦ L (f t)) (L (f' t)) t := by
    filter_upwards [hff'] with t ht hmem
    exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (ht hmem))
  let e : ℝ → ℂ := fun t ↦ fourier (-n) (t : AddCircle (b - a))
  let k : ℂ := 2 * π * I * n / (b - a)
  have he : AbsolutelyContinuousOnInterval e a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    apply ContDiff.contDiffOn (𝕜 := ℝ) (n := 1)
    simp only [e, fourier_coe_apply]
    have hcoe : ContDiff ℝ 1 (fun t : ℝ ↦ (t : ℂ)) := ofRealCLM.contDiff
    fun_prop
  have hed : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt e (-k * e t) t := by
    filter_upwards with t ht
    simpa [e, k, neg_div] using hasDerivAt_fourier_neg (b - a) n t
  have heb : e b = e a := by
    have h : (b : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
      simpa using AddCircle.coe_add_period (b - a) a
    simp only [e, h]
  have h := he.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt hLf hed hLff'
  simp only [mul_assoc] at h
  rw [intervalIntegral.integral_const_mul, heb] at h
  simp only [fourierCoeffOn_eq_integral, smul_eq_mul, real_smul, ofReal_inv]
  rw [h]
  simp only [e, k, Function.comp_apply]
  push_cast
  ring

/-- For an absolutely continuous closed curve, differentiation multiplies its `n`-th Fourier
coefficient by `2πin / (b - a)`. In particular, the derivative has zero mean. -/
theorem fourierCoeffOn_ae_derivative_of_eq_endpoints (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t) (hfab : f a = f b) (n : ℤ) :
    fourierCoeffOn hab f' n =
      (2 * π * I * n / (b - a)) • fourierCoeffOn hab f n := by
  simpa [hfab] using fourierCoeffOn_ae_derivative hab hf hff' n

end VectorValued

variable {f f' : ℝ → ℂ}

/-- **Parseval's energy identity** for an absolutely continuous closed complex curve with
square-integrable derivative. Each frequency contributes its squared frequency times the
squared norm of the corresponding Fourier coefficient. -/
theorem hasSum_sq_frequency_mul_sq_fourierCoeffOn (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t) (hfab : f a = f b)
    (hf' : MemLp f' 2 (volume.restrict (Ioc a b))) :
    HasSum (fun n : ℤ ↦ (2 * π * (n : ℝ) / (b - a)) ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2)
      ((b - a)⁻¹ * ∫ t in a..b, ‖f' t‖ ^ 2) := by
  have hnorm (n : ℤ) : ‖fourierCoeffOn hab f' n‖ ^ 2 =
      (2 * π * (n : ℝ) / (b - a)) ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2 := by
    rw [fourierCoeffOn_ae_derivative_of_eq_endpoints hab hf hff' hfab n, norm_smul, mul_pow]
    simp [← ofReal_sub, abs_of_pos (sub_pos.2 hab), abs_of_pos Real.pi_pos,
      div_pow, mul_pow, sq_abs]
  simpa only [hnorm, smul_eq_mul] using hasSum_sq_fourierCoeffOn hab hf'

end TauCeti
