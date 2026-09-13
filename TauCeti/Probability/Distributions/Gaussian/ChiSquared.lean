/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.ChiSquared
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import TauCeti.Probability.Moments.Pi

/-!
# Squares of standard Gaussian variables

This file identifies the square of a standard real Gaussian variable with the chi-squared law
of one degree of freedom. It then combines this identification with independence to prove that
the sum of the squares of a finite independent standard Gaussian family has the chi-squared law
whose degrees of freedom are the cardinality of the family. The empty family is included: both
the empty sum and `chiSquaredMeasure 0` are the point mass at zero.

It also computes the exponential-integrability domain and the moment-generating function of a
weighted square `w * x ^ 2` of a standard Gaussian variable, and of a weighted sum of squares
`∑ j, w j * c j ^ 2` of finitely many independent ones, which is the form a Gaussian quadratic
statistic takes in eigen-coordinates.

These laws identify Gaussian quadratic statistics with chi-squared distributions. In particular,
they provide the scalar foundation for distributional results about Gaussian norms and Gaussian
Gram matrices.

## Main results

* `TauCeti.Probability.gaussianReal_map_sq` — the square of the standard Gaussian measure is
  `chiSquaredMeasure 1`;
* `TauCeti.Probability.iIndepFun.hasLaw_sum_sq_gaussian` — a finite sum of independent squared
  standard Gaussian variables has the corresponding chi-squared law;
* `TauCeti.Probability.mem_integrableExpSet_mul_sq_gaussianReal_iff` and
  `TauCeti.Probability.mgf_mul_sq_gaussianReal` — the exponential moments of `w * x ^ 2` are
  finite exactly when `2 * t * w < 1`, where the moment-generating function is
  `(1 - 2 * t * w) ^ (-1 / 2)`;
* `TauCeti.Probability.mem_integrableExpSet_sum_mul_sq_pi_gaussianReal_iff` and
  `TauCeti.Probability.mgf_sum_mul_sq_pi_gaussianReal` — the same for a weighted sum of squares of
  independent standard Gaussian coordinates, with the product of the one-dimensional values.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), ch. 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The image of the standard Gaussian law under squaring is the chi-squared law with one degree
of freedom. -/
@[simp]
theorem gaussianReal_map_sq :
    (gaussianReal 0 1).map (fun x : ℝ ↦ x ^ 2) = chiSquaredMeasure 1 := by
  let _ : IsProbabilityMeasure (chiSquaredMeasure 1) :=
    isProbabilityMeasure_chiSquaredMeasure zero_le_one
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    cdf_chiSquaredMeasure_eq zero_lt_one]
  by_cases hx : x < 0
  · have hpreimage : (fun y : ℝ ↦ y ^ 2) ⁻¹' Iic x = ∅ := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hy ↦ (not_le_of_gt hx) ((sq_nonneg y).trans hy)
    rw [hpreimage, measureReal_empty,
      regularizedGamma_eq_zero_of_nonpos_right (1 / 2) (by linarith)]
  · have hx' : 0 ≤ x := le_of_not_gt hx
    have hpreimage : (fun y : ℝ ↦ y ^ 2) ⁻¹' Iic x = Icc (-√x) √x := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_Icc]
      constructor
      · exact fun hy ↦ abs_le.mp (Real.abs_le_sqrt hy)
      · intro hy
        rw [← Real.sq_sqrt hx']
        exact sq_le_sq' hy.1 hy.2
    rw [hpreimage]
    let _ : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal one_ne_zero
    have hIoc :
        (gaussianReal 0 1).real (Ioc (-√x) √x) =
          cdf (gaussianReal 0 1) √x - cdf (gaussianReal 0 1) (-√x) := by
      calc
        (gaussianReal 0 1).real (Ioc (-√x) √x) =
            (cdf (gaussianReal 0 1)).measure.real (Ioc (-√x) √x) := by
          rw [measure_cdf]
        _ = cdf (gaussianReal 0 1) √x - cdf (gaussianReal 0 1) (-√x) := by
          rw [Measure.real, StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal]
          exact sub_nonneg.mpr ((cdf (gaussianReal 0 1)).mono (by linarith [Real.sqrt_nonneg x]))
    rw [← measureReal_congr (Ioc_ae_eq_Icc (a := -√x) (b := √x)),
      hIoc, cdf_gaussianReal_zero_one, cdf_gaussianReal_zero_one]
    have hneg : -√x / √2 = -(√x / √2) := by ring
    rw [hneg, Real.erf_neg]
    have herf : 0 ≤ √x / √2 := by positivity
    rw [Real.erf_eq_regularizedGamma_half_sq herf]
    rw [div_pow, Real.sq_sqrt hx', Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
    ring

section scalar

variable {w t : ℝ}

/-- The exponential moment of order `t` of `w * x ^ 2` under the standard Gaussian is finite
exactly when `2 * t * w < 1`. -/
@[simp]
theorem mem_integrableExpSet_mul_sq_gaussianReal_iff (w t : ℝ) :
    t ∈ integrableExpSet (fun x ↦ w * x ^ 2) (gaussianReal 0 1) ↔ 2 * t * w < 1 := by
  have key : t ∈ integrableExpSet (fun x ↦ w * x ^ 2) (gaussianReal 0 1) ↔
      t * w ∈ integrableExpSet id (chiSquaredMeasure 1) := by
    simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq]
    rw [← gaussianReal_map_sq, integrable_map_measure (by fun_prop) (by fun_prop),
      Function.comp_def]
    simp only [mul_assoc]
  rw [key, integrableExpSet_id_chiSquaredMeasure zero_lt_one, Set.mem_Iio]
  constructor <;> intro h <;> linarith

/-- The moment-generating function of `w * x ^ 2` under the standard Gaussian is
`(1 - 2 * t * w) ^ (-1 / 2)` on its domain `2 * t * w < 1`. -/
@[simp]
theorem mgf_mul_sq_gaussianReal (ht : 2 * t * w < 1) :
    mgf (fun x ↦ w * x ^ 2) (gaussianReal 0 1) t = (1 - 2 * t * w) ^ (-1 / 2 : ℝ) := by
  rw [mgf_const_mul, ← mgf_id_map (X := fun x : ℝ ↦ x ^ 2) (by fun_prop), gaussianReal_map_sq,
    mgf_id_chiSquaredMeasure zero_le_one (by linarith), mul_comm w t, ← mul_assoc]
  norm_num

end scalar

section pi

variable {ι : Type*} [Fintype ι] {w : ι → ℝ} {t : ℝ}

/-- The exponential moment of order `t` of the weighted sum of squares `∑ j, w j * c j ^ 2` of
independent standard Gaussian coordinates is finite exactly when `2 * t * w j < 1` for every
`j`. -/
@[simp]
theorem mem_integrableExpSet_sum_mul_sq_pi_gaussianReal_iff (w : ι → ℝ) (t : ℝ) :
    t ∈ integrableExpSet (fun c : ι → ℝ ↦ ∑ j, w j * c j ^ 2)
        (Measure.pi fun _ : ι ↦ gaussianReal 0 1) ↔
      ∀ j, 2 * t * w j < 1 := by
  rw [integrableExpSet_sum_pi fun j (u : ℝ) ↦ w j * u ^ 2, Set.mem_iInter]
  simp only [mem_integrableExpSet_mul_sq_gaussianReal_iff]

/-- The moment-generating function of the weighted sum of squares `∑ j, w j * c j ^ 2` of
independent standard Gaussian coordinates is `∏ j, (1 - 2 * t * w j) ^ (-1 / 2)` on its
domain. -/
@[simp]
theorem mgf_sum_mul_sq_pi_gaussianReal (ht : ∀ j, 2 * t * w j < 1) :
    mgf (fun c : ι → ℝ ↦ ∑ j, w j * c j ^ 2)
        (Measure.pi fun _ : ι ↦ gaussianReal 0 1) t =
      ∏ j, (1 - 2 * t * w j) ^ (-1 / 2 : ℝ) := by
  rw [mgf_sum_pi fun j (u : ℝ) ↦ w j * u ^ 2]
  exact Finset.prod_congr rfl fun j _ ↦ mgf_mul_sq_gaussianReal (ht j)

end pi

variable {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota] {P : Measure Omega}
  {X : iota → Omega → ℝ}

/-- A finite sum of squares of independent standard Gaussian variables has the chi-squared law
with one degree of freedom per variable. This includes an empty index type, when both sides are
the point mass at zero. -/
theorem iIndepFun.hasLaw_sum_sq_gaussian (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) :
    HasLaw (fun omega ↦ ∑ i, X i omega ^ 2) (chiSquaredMeasure (Fintype.card iota)) P := by
  have hsquareLaw :
      HasLaw (fun x : ℝ ↦ x ^ 2) (chiSquaredMeasure 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, gaussianReal_map_sq⟩
  have hlawSq (i : iota) :
      HasLaw (fun omega ↦ X i omega ^ 2) (chiSquaredMeasure 1) P := by
    simpa [Function.comp_def] using hsquareLaw.comp (hlaw i)
  have hindepSq : iIndepFun (fun i omega ↦ X i omega ^ 2) P := by
    simpa [Function.comp_def] using
      hindep.comp (fun (_ : iota) (x : ℝ) ↦ x ^ 2) (fun _ ↦ by fun_prop)
  simpa using iIndepFun.hasLaw_sum_chiSquared hindepSq (fun _ ↦ zero_le_one) hlawSq

end Probability

end TauCeti
