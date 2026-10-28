/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralF.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.NoncentralChiSquared.Moments
import TauCeti.Probability.Distributions.FisherSnedecor.Moments
import TauCeti.Probability.Distributions.InverseGamma.Moments
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of noncentral F laws

For positive numerator and denominator degrees `m` and `n`, the natural moment of order `q`
of the noncentral F law exists exactly when `2 * q < n`. In particular, its mean exists for
`n > 2` and its variance for `n > 4`. Noncentrality changes their values but not these thresholds.
The exact exponential-integrability domain is the nonpositive half-line.

The ratio construction separates moments into a noncentral chi-squared moment and an
inverse-gamma moment. Sharp divergence follows from the positive-weight central F component.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {m n : ℝ} {l : ℝ≥0}

/-- A natural power is integrable under a valid noncentral F law exactly when twice its order
is below the denominator degree, including order zero and zero noncentrality. -/
@[simp]
theorem integrable_pow_noncentralFMeasure_iff (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) (q : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ q) (noncentralFMeasure m n l) ↔ 2 * q < n := by
  constructor
  · intro h
    have hcentral := h.mono_measure (smul_fisherSnedecorMeasure_le_noncentralFMeasure m n l)
    rw [integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top] at hcentral
    exact (integrable_pow_fisherSnedecorMeasure_iff hm hn q).1 hcentral
  · intro hq
    let _ := isProbabilityMeasure_chiSquaredMeasure hn.le
    have hinv : Integrable (fun y : ℝ ↦ (y ^ q)⁻¹) (chiSquaredMeasure n) := by
      rw [chiSquaredMeasure_eq_gammaMeasure hn, integrable_inv_pow_gammaMeasure_iff
        (by positivity) (by positivity)]
      linarith
    rw [noncentralFMeasure_eq_map hm hn,
      integrable_map_measure (by fun_prop) (by fun_prop)]
    convert ((integrable_pow_noncentralChiSquaredMeasure m l q).mul_prod hinv).const_mul
      ((n / m) ^ q) using 1
    ext z
    simp only [Function.comp_apply, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow, inv_pow]
    ring

/-- The identity is integrable exactly above two denominator degrees of freedom. -/
@[simp]
theorem integrable_id_noncentralFMeasure_iff (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    Integrable id (noncentralFMeasure m n l) ↔ 2 < n := by
  simpa only [pow_one, Function.id_def, Nat.cast_one, mul_one] using
    integrable_pow_noncentralFMeasure_iff hm hn l 1

/-- The second moment exists exactly above four denominator degrees of freedom. -/
theorem integrable_sq_noncentralFMeasure_iff (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x ^ 2) (noncentralFMeasure m n l) ↔ 4 < n := by
  have h := integrable_pow_noncentralFMeasure_iff hm hn l 2
  norm_num at h
  exact h

private theorem integral_pow_eq_prod (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) (q : ℕ) :
    ∫ x, x ^ q ∂noncentralFMeasure m n l =
      (n / m) ^ q * (∫ x, x ^ q ∂noncentralChiSquaredMeasure m l) *
        ∫ y, y ^ q ∂inverseGammaMeasure (n / 2) (1 / 2) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hn.le
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hm.le l
  rw [noncentralFMeasure_eq_map hm hn, integral_map (by fun_prop) (by fun_prop)]
  have heq (z : ℝ × ℝ) : (z.1 / m / (z.2 / n)) ^ q =
      (n / m) ^ q * (z.1 ^ q * (z.2 ^ q)⁻¹) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow, inv_pow]
    ring
  simp_rw [heq]
  rw [integral_const_mul,
    integral_prod_mul (fun x : ℝ ↦ x ^ q) (fun y : ℝ ↦ (y ^ q)⁻¹), mul_assoc,
    inverseGammaMeasure_of_pos (by positivity) (by positivity),
    integral_map measurable_inv.aemeasurable (by fun_prop),
    chiSquaredMeasure_eq_gammaMeasure hn]
  simp only [inv_pow]

/-- The mean of a noncentral F law is `n * (m + l) / (m * (n - 2))`. -/
@[simp]
theorem integral_id_noncentralFMeasure (hm : 0 < m) (hn : 2 < n) (l : ℝ≥0) :
    ∫ x, x ∂noncentralFMeasure m n l = n * (m + l) / (m * (n - 2)) := by
  have h := integral_pow_eq_prod hm (by linarith) l 1
  simp only [pow_one] at h
  rw [h, integral_id_noncentralChiSquaredMeasure hm.le,
    integral_id_inverseGammaMeasure (by positivity) (by linarith)]
  field_simp [hm.ne', (by linarith : n - 2 ≠ 0)]

/-- The second raw moment of a noncentral F law. -/
@[simp]
theorem integral_sq_noncentralFMeasure (hm : 0 < m) (hn : 4 < n) (l : ℝ≥0) :
    ∫ x, x ^ 2 ∂noncentralFMeasure m n l =
      n ^ 2 * ((m + l) ^ 2 + 2 * (m + 2 * l)) /
        (m ^ 2 * (n - 2) * (n - 4)) := by
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hm.le l
  have hLp : MemLp id 2 (noncentralChiSquaredMeasure m l) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_pow_noncentralChiSquaredMeasure m l 2)
  have hsecond : ∫ x, x ^ 2 ∂noncentralChiSquaredMeasure m l =
      (m + l) ^ 2 + 2 * (m + 2 * l) := by
    have hvar := variance_eq_sub hLp
    simp only [Pi.pow_apply, id_eq, variance_id_noncentralChiSquaredMeasure hm.le,
      integral_id_noncentralChiSquaredMeasure hm.le] at hvar
    linarith
  rw [integral_pow_eq_prod hm (by linarith), hsecond,
    integral_sq_inverseGammaMeasure (by positivity) (by linarith)]
  have hn1 : n / 2 - 1 = (n - 2) / 2 := by ring
  have hn2 : n / 2 - 2 = (n - 4) / 2 := by ring
  rw [hn1, hn2]
  field_simp [hm.ne', (by linarith : n - 2 ≠ 0), (by linarith : n - 4 ≠ 0)]

/-- The variance of a noncentral F law, for denominator degree greater than four. -/
@[simp]
theorem variance_id_noncentralFMeasure (hm : 0 < m) (hn : 4 < n) (l : ℝ≥0) :
    variance id (noncentralFMeasure m n l) =
      2 * n ^ 2 * ((m + l) ^ 2 + (m + 2 * l) * (n - 2)) /
        (m ^ 2 * (n - 2) ^ 2 * (n - 4)) := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm (by linarith) l
  have hLp : MemLp id 2 (noncentralFMeasure m n l) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      ((integrable_sq_noncentralFMeasure_iff hm (by linarith) l).2 hn)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_sq_noncentralFMeasure hm hn,
    integral_id_noncentralFMeasure hm (by linarith : 2 < n)]
  field_simp [hm.ne', (by linarith : n - 2 ≠ 0), (by linarith : n - 4 ≠ 0)]
  ring

/-- The exact exponential-integrability domain of a valid noncentral F law is the nonpositive
half-line, independently of noncentrality. -/
@[simp]
theorem integrableExpSet_id_noncentralFMeasure (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    integrableExpSet id (noncentralFMeasure m n l) = Iic 0 := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm hn l
  ext t
  constructor
  · intro ht
    have hcentral := ht.mono_measure (smul_fisherSnedecorMeasure_le_noncentralFMeasure m n l)
    rw [integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top] at hcentral
    exact (integrable_exp_mul_id_fisherSnedecorMeasure_iff hm hn t).1 hcentral
  · intro ht
    exact integrable_exp_mul_of_ge t 0 ht measurable_id.aemeasurable
      ((ae_pos_noncentralFMeasure m n l).mono fun _ hx ↦ hx.le)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with noncentral F law has the stated mean when the denominator degree exceeds
two. -/
theorem integral_of_hasLaw_noncentralFMeasure (hm : 0 < m) (hn : 2 < n)
    (hX : HasLaw X (noncentralFMeasure m n l) P) :
    ∫ ω, X ω ∂P = n * (m + l) / (m * (n - 2)) := by
  rw [hX.integral_eq, integral_id_noncentralFMeasure hm hn]

/-- A variable with noncentral F law has the stated variance when the denominator degree exceeds
four. -/
theorem variance_of_hasLaw_noncentralFMeasure (hm : 0 < m) (hn : 4 < n)
    (hX : HasLaw X (noncentralFMeasure m n l) P) :
    variance X P = 2 * n ^ 2 * ((m + l) ^ 2 + (m + 2 * l) * (n - 2)) /
      (m ^ 2 * (n - 2) ^ 2 * (n - 4)) := by
  rw [hX.variance_eq, variance_id_noncentralFMeasure hm hn]

end TauCeti.Probability
