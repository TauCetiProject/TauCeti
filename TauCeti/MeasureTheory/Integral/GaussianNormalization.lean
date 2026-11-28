/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volumes normalized by a Gaussian integral

This file defines the typeclass `TauCeti.HasGaussianIntegral` recording that the volume measure on
`V` satisfies `∫ x, exp (-t * q x) = (π / t) ^ a` for all `t > 0`, establishes instances for `ℝ`,
`ℂ`, binary products `V × W`, and finite powers `ι → V`, and evaluates the lower Lebesgue integral
of `(c + q x)⁻¹ ^ s` via the Gamma function.

## Main definitions and results

* `TauCeti.HasGaussianIntegral`: Gaussian normalization of the volume on `V` for `q : V → ℝ` with
  exponent `a`.
* `TauCeti.lintegral_inv_add_rpow`: for `c > 0`, `s > 0`, `a < s`, and measurable `q ≥ 0`,
  evaluates `∫⁻ x : V, ENNReal.ofReal ((c + q x)⁻¹ ^ s)` via `Gamma`.

## Provenance

Adapted from `New.HasGaussianIntegral`, `New.HasGaussianIntegral.pi`, and
`New.lintegral_inv_add_rpow` in `src/Lib/General/Measure/HaarNormalisation.lean` of
[grh-lean](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open MeasureTheory Real GaussianFourier Finset Fintype

namespace TauCeti

variable {V W : Type*} [MeasureSpace V] [MeasureSpace W]
  {q : V → ℝ} {q' : W → ℝ} {a b : ℝ} {ι : Type*} [Fintype ι]

/-- Gaussian normalization of the volume on `V` for a real function `q` with exponent `a`: for
every `t > 0`, the integral of `exp (-t * q x)` over `V` equals `(π / t) ^ a`. -/
class HasGaussianIntegral (a : outParam ℝ) (q : outParam (V → ℝ)) : Prop where
  /-- For `t > 0`, the integral of `exp (-t * q x)` over `V` is `(π / t) ^ a`. -/
  integral_exp_eq {t : ℝ} : 0 < t → ∫ x : V, exp (-t * q x) = (π / t) ^ a

/-- The Gaussian integral on `ℝ`: `∫ x : ℝ, exp (-t * x ^ 2) = (π / t) ^ (1 / 2)`. -/
instance : HasGaussianIntegral (1 / 2) fun x : ℝ ↦ x ^ 2 where
  integral_exp_eq {t} _ := by rw [integral_gaussian t, sqrt_eq_rpow]

/-- The Gaussian integral on `ℂ`: `∫ z : ℂ, exp (-t * ‖z‖ ^ 2) = (π / t) ^ 1`. -/
instance : HasGaussianIntegral 1 fun z : ℂ ↦ ‖z‖ ^ 2 where
  integral_exp_eq ht := by
    simpa [Complex.finrank_real_complex] using integral_rexp_neg_mul_sq_norm (V := ℂ) ht

/-- Product instance for `HasGaussianIntegral`: exponents and functions add on `V × W`. -/
instance [SigmaFinite (volume : Measure V)] [SFinite (volume : Measure W)]
    [h : HasGaussianIntegral a q] [h' : HasGaussianIntegral b q'] :
    HasGaussianIntegral (a + b) fun x : V × W ↦ q x.fst + q' x.snd where
  integral_exp_eq {t} ht :=
    calc ∫ x : V × W, exp (-t * (q x.fst + q' x.snd))
      _ = (∫ v : V, exp (-t * q v)) * ∫ w : W, exp (-t * q' w) := by
        simp only [mul_add, exp_add, Measure.volume_eq_prod, ← integral_prod_mul]
      _ = (π / t) ^ (a + b) := by
        rw [h.integral_exp_eq ht, h'.integral_exp_eq ht, rpow_add (by positivity)]

/-- Finite-power instance for `HasGaussianIntegral`: on `ι → V` the exponent scales by `card ι`. -/
instance HasGaussianIntegral.pi [SigmaFinite (volume : Measure V)]
    [h : HasGaussianIntegral a q] :
    HasGaussianIntegral (a * Fintype.card ι) fun x : ι → V ↦ ∑ i : ι, q (x i) where
  integral_exp_eq {t} ht :=
    calc ∫ x : ι → V, exp (-t * ∑ i : ι, q (x i))
      _ = ∫ x : ι → V, ∏ i : ι, exp (-t * q (x i)) := by simp only [mul_sum, exp_sum]
      _ = ((π / t) ^ a) ^ Fintype.card ι := by
        rw [integral_fintype_prod_volume_eq_pow fun v : V ↦ exp (-t * q v), h.integral_exp_eq ht]
      _ = (π / t) ^ (a * Fintype.card ι) := by rw [rpow_mul (by positivity), rpow_natCast]

/-- Let the volume on `V` be σ-finite with `∫ exp (-t * q x) = (π / t) ^ a` for all `t > 0`, and
let `q ≥ 0` be measurable. For `c > 0`, `s > 0`, and `a < s`, the lower Lebesgue integral of
`(c + q x)⁻¹ ^ s` is `π ^ a / Γ(s) * ((1 / c) ^ (s - a) * Γ(s - a))`. -/
theorem lintegral_inv_add_rpow [SigmaFinite (volume : Measure V)] [h : HasGaussianIntegral a q]
    {s c : ℝ} (hc : 0 < c) (ha : a < s) (hq_nonneg : ∀ x : V, 0 ≤ q x) (hs : 0 < s)
    (hq : Measurable q := by fun_prop) :
    ∫⁻ x : V, ENNReal.ofReal ((c + q x)⁻¹ ^ s) =
      ENNReal.ofReal (π ^ a / Gamma s * ((1 / c) ^ (s - a) * Gamma (s - a))) := by
  have h_gamma {b r K : ℝ} (hb : 0 < b) (hr : 0 < r) (hK : 0 < K) :
      ∫⁻ t : ℝ in Set.Ioi 0, ENNReal.ofReal (K * (t ^ (b - 1) * rexp (-(r * t)))) =
        ENNReal.ofReal (K * ((1 / r) ^ b * Gamma b)) := by
    have h_int : ∫ t : ℝ in Set.Ioi 0, K * (t ^ (b - 1) * rexp (-(r * t))) =
        K * ((1 / r) ^ b * Gamma b) := by
      rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi hb hr]
    have h_ne : K * ((1 / r) ^ b * Gamma b) ≠ 0 := by positivity
    rw [← ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (h_int.trans_ne h_ne))
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦ by positivity), h_int]
  let F (x : V) (t : ℝ) : ℝ := (Gamma s)⁻¹ * (t ^ (s - 1) * rexp (-((c + q x) * t)))
  rw [← h_gamma (sub_pos.mpr ha) hc (by positivity),
    lintegral_congr (g := fun x ↦ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (F x t)) fun x ↦ by
      rw [h_gamma hs (add_pos_of_pos_of_nonneg hc (hq_nonneg x)) (by positivity)]
      exact congrArg ENNReal.ofReal (by field_simp),
    lintegral_lintegral_swap (by fun_prop)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  have h_split (x : V) :
      F x t = (Gamma s)⁻¹ * t ^ (s - 1) * rexp (-(c * t)) * rexp (-t * q x) := by
    simp only [F, mul_assoc, ← exp_add]; ring_nf
  have h_val : ∫ x : V, F x t =
      π ^ a / Gamma s * (t ^ (s - a - 1) * rexp (-(c * t))) := by
    simp only [h_split, integral_const_mul, h.integral_exp_eq ht]
    rw [div_rpow pi_pos.le ht.le, sub_right_comm, rpow_sub ht (s - 1) a]; ring
  have h_ne : π ^ a / Gamma s * (t ^ (s - a - 1) * rexp (-(c * t))) ≠ 0 := by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (h_val.trans_ne h_ne))
    (.of_forall fun x ↦ show 0 ≤ F x t by positivity), h_val]

end TauCeti
