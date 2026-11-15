/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Levy
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Levy.Moments

/-!
# Exponential transforms of the reflected Lévy stable law

This file computes the exponential-integrability domain and transforms of the fully left-skewed
stable law of shape one half. This stable law is the reflection of a Lévy law, so its domain is
the nonnegative half-line.

The location shift `m + s` in the cumulant is the correction required by Nolan's `S₀`
parameterization. The corresponding right-skewed formulas follow directly from
`stableMeasure_one_half_one` and the existing Lévy transform API; reflection reverses the domain
and requires the affine transport carried out here.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

/-- The exponential-integrability domain of a fully left-skewed stable law of shape one half is
the nonnegative half-line. -/
theorem integrableExpSet_id_stableMeasure_one_half_neg_one {s : ℝ≥0} (hs : 0 < s) (m : ℝ) :
    integrableExpSet id (stableMeasure 2⁻¹ (-1) s m) = Ici 0 := by
  rw [stableMeasure_one_half_neg_one hs]
  -- The affine transport lemma writes reflection as `fun x ↦ 0 + -1 * x`, whereas the stable
  -- specialization uses `Neg.neg`; isolate their normalization before rewriting the domain.
  rw [show integrableExpSet id ((levyMeasure (-m - s) s).map Neg.neg) =
      (fun t : ℝ ↦ -1 * t) ⁻¹' integrableExpSet id (levyMeasure (-m - s) s) by
    simpa only [zero_add, neg_one_mul] using
      (integrableExpSet_id_map_affine (μ := levyMeasure (-m - s) s) (a := 0) (b := -1))]
  simp only [neg_one_mul]
  rw [integrableExpSet_id_levyMeasure (by exact_mod_cast hs)]
  ext t
  simp

/-- The moment-generating function of a fully left-skewed stable law of shape one half on its
exponential-integrability domain. -/
theorem mgf_id_stableMeasure_one_half_neg_one (s : ℝ≥0) (m : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    mgf id (stableMeasure 2⁻¹ (-1) s m) t = exp ((m + s) * t - √(2 * s * t)) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [stableMeasure_zero_scale (by norm_num) (by norm_num), mgf_dirac']
    simp [mul_comm]
  have hspos : 0 < s := pos_iff_ne_zero.mpr hs
  rw [stableMeasure_one_half_neg_one hspos]
  -- As above, normalize the `Neg.neg` reflection to the affine map expected by
  -- `mgf_id_map_affine` before rewriting the transform.
  rw [show mgf id ((levyMeasure (-m - s) s).map Neg.neg) t =
      exp (0 * t) * mgf id (levyMeasure (-m - s) s) (-1 * t) by
    simpa only [zero_add, neg_one_mul] using
      (mgf_id_map_affine (μ := levyMeasure (-m - s) s) (a := 0) (b := -1) t)]
  simp only [zero_mul, exp_zero, one_mul, neg_one_mul]
  rw [mgf_id_levyMeasure (by exact_mod_cast hspos) (-m - s) (by linarith : -t ≤ 0)]
  congr 1
  congr 1 <;> ring_nf

/-- The cumulant-generating function of a fully left-skewed stable law of shape one half on its
exponential-integrability domain. -/
theorem cgf_id_stableMeasure_one_half_neg_one (s : ℝ≥0) (m : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cgf id (stableMeasure 2⁻¹ (-1) s m) t = (m + s) * t - √(2 * s * t) := by
  rw [cgf, mgf_id_stableMeasure_one_half_neg_one s m ht, log_exp]

end TauCeti.Probability
