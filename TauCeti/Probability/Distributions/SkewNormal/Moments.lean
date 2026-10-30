/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.SkewNormal.Construction
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.Chi.Gaussian
import TauCeti.Probability.Distributions.Chi.Moments
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Tilted

/-!
# Moments and transforms of the skew-normal distribution

Write `Φ = cdf (gaussianReal 0 1)` and `δ = α / √(1 + α ^ 2)`. The skew-normal law with
location `m`, scale `s > 0` and shape `α` is the law of `m + s * (δ * |Z₁| + √(1 - δ ^ 2) * Z₂)`
for independent standard Gaussians `Z₁` and `Z₂` (`map_prod_gaussianReal_eq_skewNormalMeasure`).
Its moments and transforms split accordingly into a half-normal factor and a Gaussian factor. The
half-normal factor has moment-generating function `E[exp (u * |Z₁|)] = 2 * exp (u ^ 2 / 2) * Φ(u)`,
and so

* `M(t) = 2 * exp (m * t + s ^ 2 * t ^ 2 / 2) * Φ(δ * s * t)` for every real `t`;
* `K(t) = log 2 + m * t + s ^ 2 * t ^ 2 / 2 + log Φ(δ * s * t)`;
* `E[X] = m + s * δ * √(2 / π)` and `Var X = s ^ 2 * (1 - 2 * δ ^ 2 / π)`.

## Main results

* `integral_exp_mul_abs_gaussianReal` — the half-normal moment-generating function;
* `integrableExpSet_id_skewNormalMeasure` — every exponential moment is finite;
* `mgf_id_skewNormalMeasure` and `cgf_id_skewNormalMeasure` — the moment- and
  cumulant-generating functions;
* `integral_id_skewNormalMeasure` and `variance_id_skewNormalMeasure` — the mean and variance.

## References

* A. Azzalini, *A class of distributions which includes the normal ones*, Scandinavian Journal of
  Statistics 12 (1985), 171–178.
* A. Azzalini and A. Capitanio, *The Skew-Normal and Related Families*, Cambridge University
  Press, 2014, Section 2.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {s : ℝ}

/-! ### The half-normal factor -/

/-- Every exponential moment of the absolute value of a standard Gaussian is finite. -/
theorem integrable_exp_mul_abs_gaussianReal (u : ℝ) :
    Integrable (fun x => exp (u * |x|)) (gaussianReal 0 1) := by
  have hmap := gaussianReal_map_abs (v := 1) one_ne_zero
  rw [NNReal.coe_one, sqrt_one] at hmap
  have h := integrable_exp_mul_id_chiMeasure 1 1 u
  rwa [← hmap, integrable_map_measure (by fun_prop) (by fun_prop)] at h

/-- **The moment-generating function of the half-normal law.** For a standard Gaussian `Z`,
`E[exp (u * |Z|)] = 2 * exp (u ^ 2 / 2) * Φ(u)`. -/
theorem integral_exp_mul_abs_gaussianReal (u : ℝ) :
    ∫ x, exp (u * |x|) ∂gaussianReal 0 1 = 2 * exp (u ^ 2 / 2) * cdf (gaussianReal 0 1) u := by
  -- Completing the square: `φ(x) * exp (u * x) = exp (u ^ 2 / 2) * N(u, 1)(x)`.
  have htilt (x : ℝ) :
      gaussianPDFReal 0 1 x * exp (u * x) = exp (u ^ 2 / 2) * gaussianPDFReal u 1 x := by
    have h := gaussianPDFReal_mul_exp_div_mgf 0 1 u x
    simp only [zero_mul, NNReal.coe_one, one_mul, zero_add] at h
    rw [← h]
    field_simp
  have heven : (fun x => gaussianPDFReal 0 1 x * exp (u * |x|)) =
      fun x => (fun y => gaussianPDFReal 0 1 y * exp (u * y)) |x| := by
    funext x
    simp [gaussianPDFReal, sq_abs]
  have hIoi : ∫ x in Ioi 0, gaussianPDFReal u 1 x = cdf (gaussianReal 0 1) u := by
    rw [← sub_zero u, ← div_one (u - 0), ← sqrt_one, ← NNReal.coe_one,
      ← measureReal_Ioi_gaussianReal_eq_cdf _ one_ne_zero, measureReal_def,
      gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal
        (setIntegral_nonneg measurableSet_Ioi fun x _ => gaussianPDFReal_nonneg _ _ x)]
    simp
  simp_rw [integral_gaussianReal_eq_integral_smul one_ne_zero, smul_eq_mul]
  rw [heven, integral_comp_abs (f := fun y => gaussianPDFReal 0 1 y * exp (u * y))]
  simp_rw [htilt]
  rw [integral_const_mul, hIoi]
  ring

/-! ### Exponential moments -/

/-- In the Gaussian construction, the exponential weight `exp (t * x)` splits into a function of
the half-normal coordinate times a function of the Gaussian coordinate. -/
private theorem exp_mul_skewNormal_construction (m s δ c t : ℝ) (z : ℝ × ℝ) :
    exp (t * (m + s * (δ * |z.1| + c * z.2))) =
      exp (t * m) * exp (t * s * δ * |z.1|) * exp (t * s * c * z.2) := by
  rw [← exp_add, ← exp_add]
  ring_nf

/-- Every exponential moment of a skew-normal law is finite. -/
theorem integrable_exp_mul_skewNormalMeasure (m s α t : ℝ) :
    Integrable (fun x => exp (t * x)) (skewNormalMeasure m s α) := by
  rcases le_or_gt s 0 with hs | hs
  · simp [skewNormalMeasure_of_nonpos hs]
  rw [← map_prod_gaussianReal_eq_skewNormalMeasure hs m α,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, exp_mul_skewNormal_construction]
  exact ((integrable_exp_mul_abs_gaussianReal _).const_mul _).mul_prod
    (integrable_exp_mul_gaussianReal _)

/-- **The exponential-integrability domain of a skew-normal law is all of `ℝ`.** -/
@[simp]
theorem integrableExpSet_id_skewNormalMeasure (m s α : ℝ) :
    integrableExpSet id (skewNormalMeasure m s α) = univ := by
  ext t
  simpa [integrableExpSet] using integrable_exp_mul_skewNormalMeasure m s α t

/-- **The skew-normal moment-generating function.** For `s > 0` and `δ = α / √(1 + α ^ 2)`,
`M(t) = 2 * exp (m * t + s ^ 2 * t ^ 2 / 2) * Φ(δ * s * t)` for every real `t`. -/
theorem mgf_id_skewNormalMeasure (hs : 0 < s) (m α t : ℝ) :
    mgf id (skewNormalMeasure m s α) t =
      2 * exp (m * t + s ^ 2 * t ^ 2 / 2) *
        cdf (gaussianReal 0 1) (α / √(1 + α ^ 2) * s * t) := by
  have hδ1 : (α / √(1 + α ^ 2)) ^ 2 ≤ 1 := by
    rw [← sin_arctan]
    exact sin_sq_le_one _
  set δ := α / √(1 + α ^ 2)
  have hδ : δ ^ 2 + √(1 - δ ^ 2) ^ 2 = 1 := by
    rw [sq_sqrt (sub_nonneg.mpr hδ1)]
    ring
  have hgauss (u : ℝ) : ∫ x, exp (u * x) ∂gaussianReal 0 1 = exp (u ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) u
  rw [mgf, ← map_prod_gaussianReal_eq_skewNormalMeasure hs m α,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [id, exp_mul_skewNormal_construction]
  rw [integral_prod_mul (fun x => exp (t * m) * exp (t * s * δ * |x|))
    (fun y => exp (t * s * √(1 - δ ^ 2) * y)), integral_const_mul,
    integral_exp_mul_abs_gaussianReal, hgauss]
  rw [show δ * s * t = t * s * δ by ring]
  have hexp : t * m + (t * s * δ) ^ 2 / 2 + (t * s * √(1 - δ ^ 2)) ^ 2 / 2 =
      m * t + s ^ 2 * t ^ 2 / 2 := by
    linear_combination (t ^ 2 * s ^ 2 / 2) * hδ
  rw [← hexp, exp_add, exp_add]
  ring

/-- **The skew-normal cumulant-generating function.** For `s > 0` and `δ = α / √(1 + α ^ 2)`,
`K(t) = log 2 + m * t + s ^ 2 * t ^ 2 / 2 + log Φ(δ * s * t)` for every real `t`. -/
theorem cgf_id_skewNormalMeasure (hs : 0 < s) (m α t : ℝ) :
    cgf id (skewNormalMeasure m s α) t =
      log 2 + (m * t + s ^ 2 * t ^ 2 / 2) +
        log (cdf (gaussianReal 0 1) (α / √(1 + α ^ 2) * s * t)) := by
  rw [cgf, mgf_id_skewNormalMeasure hs, log_mul (by positivity)
    (cdf_gaussianReal_pos 0 one_ne_zero _).ne', log_mul two_ne_zero (exp_pos _).ne', log_exp]

/-! ### Mean and variance -/

/-- The mean of the absolute value of a standard Gaussian is `√(2 / π)`. -/
private theorem integral_abs_gaussianReal : ∫ x, |x| ∂gaussianReal 0 1 = √(2 / π) := by
  have h := integral_abs_sub_pow_gaussianReal 0 1 1
  simp only [sub_zero, pow_one, NNReal.coe_one, mul_one, Nat.cast_one] at h
  rw [h, show ((1 : ℝ) + 1) / 2 = 1 by norm_num, Gamma_one, ← sqrt_eq_rpow, sqrt_div' _ pi_pos.le]
  ring

/-- The location-free, unit-scale part `δ * |z.1| + c * z.2` of the skew-normal construction is
square-integrable for two standard Gaussian coordinates. -/
private theorem memLp_skewNormal_construction (δ c : ℝ) :
    MemLp (fun z : ℝ × ℝ => δ * |z.1| + c * z.2) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have habs : MemLp (fun x : ℝ => |x|) 2 (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs] using (memLp_id_gaussianReal (μ := 0) (v := 1) 2).norm
  exact ((habs.comp_fst _).const_mul δ).add
    (((memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_snd _).const_mul c)

/-- The mean of the location-free, unit-scale part of the skew-normal construction. -/
private theorem integral_skewNormal_construction (δ c : ℝ) :
    ∫ z, δ * |z.1| + c * z.2 ∂(gaussianReal 0 1).prod (gaussianReal 0 1) = δ * √(2 / π) := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  have h₁ : Integrable (fun z : ℝ × ℝ => δ * |z.1|) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (hid.abs.comp_fst _).const_mul δ
  have h₂ : Integrable (fun z : ℝ × ℝ => c * z.2) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (hid.comp_snd _).const_mul c
  rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul,
    integral_fun_fst (fun x : ℝ => |x|), integral_fun_snd (fun x : ℝ => x),
    integral_abs_gaussianReal, integral_id_gaussianReal]
  simp

/-- The second moment of the location-free, unit-scale part of the skew-normal construction is
`1` when `δ ^ 2 + c ^ 2 = 1`. -/
private theorem integral_sq_skewNormal_construction {δ c : ℝ} (hδc : δ ^ 2 + c ^ 2 = 1) :
    ∫ z, (δ * |z.1| + c * z.2) ^ 2 ∂(gaussianReal 0 1).prod (gaussianReal 0 1) = 1 := by
  set ρ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hsq : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    simpa using integral_sub_pow_two_mul_gaussianReal 0 1 1
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mp (memLp_id_gaussianReal 2)
  have h₁ : Integrable (fun z : ℝ × ℝ => δ ^ 2 * z.1 ^ 2) ρ := (hint2.comp_fst _).const_mul _
  have h₂ : Integrable (fun z : ℝ × ℝ => 2 * δ * c * (|z.1| * z.2)) ρ :=
    (hid.abs.mul_prod hid).const_mul _
  have h₃ : Integrable (fun z : ℝ × ℝ => c ^ 2 * z.2 ^ 2) ρ := (hint2.comp_snd _).const_mul _
  have hexpand (z : ℝ × ℝ) : (δ * |z.1| + c * z.2) ^ 2 =
      δ ^ 2 * z.1 ^ 2 + 2 * δ * c * (|z.1| * z.2) + c ^ 2 * z.2 ^ 2 := by
    rw [← sq_abs z.1]
    ring
  simp_rw [hexpand]
  rw [integral_add (f := fun z => δ ^ 2 * z.1 ^ 2 + 2 * δ * c * (|z.1| * z.2)) (h₁.add h₂) h₃,
    integral_add h₁ h₂, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_fun_fst (fun x : ℝ => x ^ 2),
    integral_fun_snd (fun x : ℝ => x ^ 2),
    integral_prod_mul (fun x : ℝ => |x|) (fun x : ℝ => x), integral_id_gaussianReal, hsq]
  simp [hδc]

/-- **The skew-normal mean.** For `s > 0` and `δ = α / √(1 + α ^ 2)`,
`E[X] = m + s * δ * √(2 / π)`. -/
@[simp]
theorem integral_id_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    ∫ x, x ∂skewNormalMeasure m s α = m + s * (α / √(1 + α ^ 2)) * √(2 / π) := by
  rw [← map_prod_gaussianReal_eq_skewNormalMeasure hs m α,
    integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_const m)
      ((memLp_skewNormal_construction _ _).integrable one_le_two |>.const_mul s),
    integral_const_mul, integral_skewNormal_construction]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- **The skew-normal variance.** For `s > 0` and `δ = α / √(1 + α ^ 2)`,
`Var X = s ^ 2 * (1 - 2 * δ ^ 2 / π)`. -/
@[simp]
theorem variance_id_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    Var[id; skewNormalMeasure m s α] = s ^ 2 * (1 - 2 * (α / √(1 + α ^ 2)) ^ 2 / π) := by
  have hδ1 : (α / √(1 + α ^ 2)) ^ 2 ≤ 1 := by
    rw [← sin_arctan]
    exact sin_sq_le_one _
  set δ := α / √(1 + α ^ 2)
  have hδ : δ ^ 2 + √(1 - δ ^ 2) ^ 2 = 1 := by
    rw [sq_sqrt (sub_nonneg.mpr hδ1)]
    ring
  have hLp := memLp_skewNormal_construction δ √(1 - δ ^ 2)
  rw [← map_prod_gaussianReal_eq_skewNormalMeasure hs m α, variance_id_map (by fun_prop),
    variance_const_add (by fun_prop), variance_const_mul, variance_eq_sub hLp]
  simp only [Pi.pow_apply]
  rw [integral_sq_skewNormal_construction hδ, integral_skewNormal_construction, mul_pow,
    sq_sqrt (div_nonneg zero_le_two pi_pos.le)]
  ring

end Probability

end TauCeti
