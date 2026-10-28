/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralT.Moments
public import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# Exponential integrability of noncentral t laws

A noncentral t law with positive degrees of freedom has no finite exponential moment at any
nonzero real parameter, regardless of its noncentrality. Its exponential-integrability domain
is therefore the singleton `{0}`. Nonpositive degrees give the zero measure, whose domain is
all of `ℝ`.

The Gaussian numerator in the independent-ratio construction takes both signs with positive
probability. Exponential integrability would force every natural moment of the inverse
chi-squared denominator to be finite, contradicting the sharp moment threshold from
`integrable_pow_noncentralTMeasure_iff`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 31.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {ν δ : ℝ}

/-- A noncentral t law with positive degrees has a finite exponential moment exactly at zero.
In particular, neither tail admits a nonzero exponential parameter. -/
@[simp]
theorem integrable_exp_mul_id_noncentralTMeasure_iff (hν : 0 < ν) (δ t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (noncentralTMeasure ν δ) ↔ t = 0 := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  constructor
  · intro hint
    by_contra ht
    rw [noncentralTMeasure_eq_map_gaussianReal hν,
      integrable_map_measure (by fun_prop) (by fun_prop)] at hint
    -- Select a numerator of the sign that makes the exponential grow at a small denominator.
    have hae := (gaussianReal_absolutelyContinuous' δ (v := 1) one_ne_zero).ae_le
      hint.prod_right_ae
    have hopen : IsOpen {z : ℝ | 0 < t * z} :=
      isOpen_lt continuous_const (continuous_const.mul continuous_id)
    have hnonempty : ({z : ℝ | 0 < t * z} : Set ℝ).Nonempty :=
      ⟨t, mul_self_pos.2 ht⟩
    obtain ⟨z, hz, hzint⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (hopen.measure_ne_zero volume hnonempty) (ae_restrict_of_ae hae)
    have hpos : Integrable (fun v : ℝ ↦ exp ((t * z) * (√(v / ν))⁻¹))
        (chiSquaredMeasure ν) := by
      simpa only [Function.comp_apply, div_eq_mul_inv, mul_assoc] using hzint
    have hneg : Integrable (fun v : ℝ ↦ exp (-(t * z) * (√(v / ν))⁻¹))
        (chiSquaredMeasure ν) := by
      refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun v ↦ ?_)
      rw [norm_of_nonneg (exp_pos _).le]
      exact exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.2 hz.le) (inv_nonneg.2 (sqrt_nonneg _)))
    -- All denominator moments would then exist, hence so would a forbidden ratio moment.
    let n := ⌈ν⌉₊
    have hpow := integrable_pow_of_integrable_exp_mul hz.ne' hpos hneg n
    have hratio : Integrable (fun x : ℝ ↦ x ^ n) (noncentralTMeasure ν δ) := by
      rw [noncentralTMeasure_eq_map_gaussianReal hν,
        integrable_map_measure (by fun_prop) (by fun_prop)]
      simpa only [Function.comp_def, div_eq_mul_inv, mul_pow] using
        (integrable_pow_gaussianReal δ 1 n).mul_prod hpow
    exact (not_lt_of_ge (Nat.le_ceil ν))
      ((integrable_pow_noncentralTMeasure_iff hν δ n).1 hratio)
  · rintro rfl
    simp

/-- The exact exponential-integrability domain of a noncentral t probability law. -/
theorem integrableExpSet_id_noncentralTMeasure (hν : 0 < ν) (δ : ℝ) :
    integrableExpSet id (noncentralTMeasure ν δ) = {0} := by
  ext t
  simp [integrableExpSet, hν]

/-- A variable with a noncentral t law of positive degree has no finite exponential moment
away from zero. -/
theorem integrable_exp_mul_of_hasLaw_noncentralTMeasure_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hν : 0 < ν) (hX : HasLaw X (noncentralTMeasure ν δ) P) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) P ↔ t = 0 := by
  have h := integrable_exp_mul_id_noncentralTMeasure_iff hν δ t
  rw [← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable] at h
  exact h

end TauCeti.Probability
