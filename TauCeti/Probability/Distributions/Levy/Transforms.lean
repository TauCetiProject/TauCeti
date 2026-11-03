/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Levy.Basic
public import Mathlib.Probability.Moments.Basic
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.InverseGaussian.Transforms

/-!
# Moment-generating function of the Lévy distribution

The Lévy law with location `m` and positive scale `c` has exponential moments exactly at `t ≤ 0`
(`integrableExpSet_id_levyMeasure`). On that half-line its moment-generating function is

`M(t) = exp (m t - √(-2 c t))`,

and its cumulant-generating function is `m t - √(-2 c t)`.

For `t < 0`, the standard Lévy density reweighted by `exp (t x)` is `exp (-√(-2 t))` times the
inverse Gaussian density with mean `1 / √(-2 t)` and shape `1`
(`inverseGaussianPDFReal_mul_exp_eq_levyPDFReal_mul_exp`), so the normalization of that density
gives the standard value. Positive affine transport gives the general one.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer (2020),
  chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {c t : ℝ}

private theorem mgf_id_levyMeasure_zero_one (ht : t ≤ 0) :
    mgf id (levyMeasure 0 1) t = exp (-√(-2 * t)) := by
  rcases ht.lt_or_eq with ht | rfl
  · have hr : 0 < √(-2 * t) := sqrt_pos.2 (by linarith)
    have hμ : 0 < 1 / √(-2 * t) := by positivity
    have hcrit : 0 - 1 / (2 * (1 / √(-2 * t)) ^ 2) = t := by
      rw [div_pow, sq_sqrt (by linarith)]
      field_simp
      ring
    have hpoint (x : ℝ) : levyPDFReal 0 1 x * exp (t * x) =
        exp (-√(-2 * t)) * inverseGaussianPDFReal (1 / √(-2 * t)) 1 x := by
      have h := inverseGaussianPDFReal_mul_exp_eq_levyPDFReal_mul_exp hμ one_pos 0 x
      rw [hcrit, zero_mul, exp_zero, mul_one, one_div_one_div] at h
      rw [h, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
    rw [mgf, levyMeasure_eq_withDensity, funext (levyPDF_eq_ofReal 0 1),
      integral_withDensity_ofReal (measurable_levyPDFReal 0 1).aemeasurable
        (ae_of_all _ (levyPDFReal_nonneg 0 1))]
    simp only [id_eq, smul_eq_mul, hpoint, integral_const_mul,
      integral_inverseGaussianPDFReal hμ one_pos, mul_one]
  · let _ := isProbabilityMeasure_levyMeasure one_pos 0
    simp

/-- **The moment-generating function of a Lévy law** with location `m` and positive scale `c` is
`exp (m t - √(-2 c t))` on its exponential-integrability domain `t ≤ 0`. -/
theorem mgf_id_levyMeasure (hc : 0 < c) (m : ℝ) (ht : t ≤ 0) :
    mgf id (levyMeasure m c) t = exp (m * t - √(-2 * c * t)) := by
  rw [levyMeasure_eq_map_affine_levyMeasure_zero_one hc, mgf_id_map_affine,
    mgf_id_levyMeasure_zero_one (mul_nonpos_of_nonneg_of_nonpos hc.le ht), ← exp_add, mul_assoc,
    sub_eq_add_neg]

/-- **The cumulant-generating function of a Lévy law** with location `m` and positive scale `c`
is `m t - √(-2 c t)` on its exponential-integrability domain `t ≤ 0`. -/
theorem cgf_id_levyMeasure (hc : 0 < c) (m : ℝ) (ht : t ≤ 0) :
    cgf id (levyMeasure m c) t = m * t - √(-2 * c * t) := by
  rw [cgf, mgf_id_levyMeasure hc m ht, log_exp]

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m : ℝ}

/-- The moment-generating function of a variable with a Lévy law, on the nonpositive
half-line. -/
theorem mgf_of_hasLaw_levyMeasure (hc : 0 < c) (hX : HasLaw X (levyMeasure m c) P)
    (ht : t ≤ 0) :
    mgf X P t = exp (m * t - √(-2 * c * t)) := by
  rw [← mgf_id_levyMeasure hc m ht, ← hX.map_eq, mgf_map hX.aemeasurable (by fun_prop),
    Function.id_comp]

/-- The cumulant-generating function of a variable with a Lévy law, on the nonpositive
half-line. -/
theorem cgf_of_hasLaw_levyMeasure (hc : 0 < c) (hX : HasLaw X (levyMeasure m c) P)
    (ht : t ≤ 0) :
    cgf X P t = m * t - √(-2 * c * t) := by
  rw [cgf, mgf_of_hasLaw_levyMeasure hc hX ht, log_exp]

end RandomVariables

end TauCeti.Probability
