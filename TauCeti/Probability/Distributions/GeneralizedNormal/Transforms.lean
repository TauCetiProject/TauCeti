/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedNormal.Gamma
public import TauCeti.Probability.Distributions.GeneralizedNormal.Relations
public import TauCeti.Probability.Distributions.GeneralizedGamma.Transforms

/-!
# Exponential integrability of generalized normal laws

For positive scale `s` and shape `p`, the exact exponential-integrability domain is:

* all of `ℝ` when `1 < p`;
* `(-s⁻¹, s⁻¹)` when `p = 1`, with both endpoints excluded;
* `{0}` when `0 < p < 1`.

The location does not affect this domain. The proof uses
`generalizedNormalMeasure_eq_add_map_neg`: both the generalized gamma magnitude and its
reflection must have a finite exponential moment. Their domains are supplied by
`integrableExpSet_id_generalizedGammaMeasure`. Invalid scale or shape gives the zero law,
whose exponential-integrability domain is all of `ℝ`.

## References

* S. Nadarajah, *A generalized normal distribution*, Journal of Applied Statistics 32(7),
  685–694 (2005).
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {s p : ℝ}

private theorem integrable_exp_mul_id_generalizedNormalMeasure_zero_iff (s p t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (generalizedNormalMeasure 0 s p) ↔
      t ∈ integrableExpSet id (generalizedGammaMeasure p⁻¹ p s) ∧
        -t ∈ integrableExpSet id (generalizedGammaMeasure p⁻¹ p s) := by
  rw [generalizedNormalMeasure_eq_add_map_neg, integrable_add_measure,
    integrable_smul_measure (by norm_num) (by norm_num),
    integrable_smul_measure (by norm_num) (by norm_num),
    integrable_map_measure (by fun_prop) (by fun_prop)]
  simp [integrableExpSet, Function.comp_def, mul_neg, neg_mul]

/-- The exact exponential-integrability domain of a generalized normal law with positive
scale and shape. The location has no effect on the domain. -/
theorem integrableExpSet_id_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) (m : ℝ) :
    integrableExpSet id (generalizedNormalMeasure m s p) =
      if 1 < p then univ else if p = 1 then Ioo (-s⁻¹) s⁻¹ else {0} := by
  have htranslate := generalizedNormalMeasure_map_affine 0 s p m (c := 1) one_ne_zero
  simp only [mul_zero, add_zero, abs_one, one_mul] at htranslate
  have hdomain := integrableExpSet_id_map_affine
    (μ := generalizedNormalMeasure 0 s p) (a := m) (b := 1)
  simp only [one_mul] at hdomain
  rw [← htranslate, hdomain]
  ext t
  simp only [integrableExpSet, mem_preimage, mem_ofPred_eq, id_eq]
  rw [integrable_exp_mul_id_generalizedNormalMeasure_zero_iff,
    integrableExpSet_id_generalizedGammaMeasure (inv_pos.mpr hp) hp.ne' hs]
  split_ifs <;> simp only [mem_univ, mem_Iio, mem_Ioo, mem_singleton_iff] <;> grind

/-- Above shape one, all exponential moments exist, including for invalid zero laws. -/
@[simp]
theorem integrableExpSet_id_generalizedNormalMeasure_of_one_lt
    (hp : 1 < p) (m s : ℝ) :
    integrableExpSet id (generalizedNormalMeasure m s p) = univ := by
  by_cases hs : 0 < s
  · simp [integrableExpSet_id_generalizedNormalMeasure hs (lt_trans zero_lt_one hp), hp]
  · simp [generalizedNormalMeasure_of_not_pos (fun h ↦ hs h.1), integrableExpSet]

/-- At shape one, both reciprocal-scale endpoints are excluded from the domain. -/
@[simp]
theorem integrableExpSet_id_generalizedNormalMeasure_one (hs : 0 < s) (m : ℝ) :
    integrableExpSet id (generalizedNormalMeasure m s 1) = Ioo (-s⁻¹) s⁻¹ := by
  rw [generalizedNormalMeasure_one, integrableExpSet_id_laplaceMeasure hs]

/-- Below shape one, a valid generalized normal law has no nonzero exponential moments. -/
@[simp]
theorem integrableExpSet_id_generalizedNormalMeasure_of_lt_one
    (hs : 0 < s) (hp : 0 < p) (hp1 : p < 1) (m : ℝ) :
    integrableExpSet id (generalizedNormalMeasure m s p) = {0} := by
  simp [integrableExpSet_id_generalizedNormalMeasure hs hp, not_lt.mpr hp1.le, hp1.ne]

end TauCeti.Probability
