/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Basic
public import TauCeti.Probability.Distributions.Gumbel.Moments
import TauCeti.Probability.Distributions.Affine

/-!
# Moments of the generalized extreme-value distribution

For positive scale, the absolute moment of order `p ≥ 0` is finite exactly when `p * ξ < 1`.
In particular, all natural moments exist at nonpositive shape, whereas positive shape has a
sharp polynomial-tail threshold. At nonzero shape, the raw moments are finite binomial sums
of Gamma values, and the mean and variance have their usual Gamma-function formulas.
The zero-shape case inherits the Gumbel moments, including every finite absolute moment.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {m s ξ : ℝ}

private lemma gev_eq_map_affine (hs : 0 < s) (hξ : ξ ≠ 0) (m : ℝ) :
    generalizedExtremeValueMeasure m s ξ =
      ((expMeasure 1).map fun e : ℝ ↦ e ^ (-ξ)).map
        (fun x ↦ (m - s / ξ) + (s / ξ) * x) := by
  rw [generalizedExtremeValueMeasure_of_shape_ne_zero hs hξ,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext e
  simp only [Function.comp_apply]
  ring

/-- The exact finite `Lᵖ` criterion for a positive-scale generalized extreme-value law,
including order zero and shape zero. -/
@[simp]
theorem memLp_id_generalizedExtremeValueMeasure_iff (hs : 0 < s) (m ξ : ℝ) (p : ℝ≥0) :
    MemLp id p (generalizedExtremeValueMeasure m s ξ) ↔ (p : ℝ) * ξ < 1 := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  by_cases hp : p = 0
  · subst p
    simp [memLp_zero_iff_aestronglyMeasurable, aestronglyMeasurable_id]
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [generalizedExtremeValueMeasure_zero, mul_zero, zero_lt_one, iff_true]
    exact memLp_id_gumbelMeasure m s p
  rw [gev_eq_map_affine hs hξ, memLp_id_map_affine_iff (div_ne_zero hs.ne' hξ),
    memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
  rw [← integrable_norm_rpow_iff (by fun_prop) (by exact_mod_cast hp) ENNReal.coe_ne_top]
  simp only [ENNReal.coe_toReal]
  have heq : (fun e : ℝ ↦ ‖(id ∘ fun e : ℝ ↦ e ^ (-ξ)) e‖ ^ (p : ℝ))
      =ᵐ[expMeasure 1] fun e ↦ e ^ (-ξ * (p : ℝ)) := by
    filter_upwards [ae_pos_expMeasure 1] with e he
    simp only [Function.comp_apply, id_eq, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos he _), ← Real.rpow_mul he.le]
  rw [integrable_congr heq, integrable_rpow_expMeasure_iff one_pos]
  constructor <;> intro h <;> nlinarith

/-- A natural absolute moment is finite exactly below the generalized extreme-value tail
threshold. This includes the zeroth moment and the Gumbel shape. -/
@[simp]
theorem integrable_pow_abs_generalizedExtremeValueMeasure_iff (hs : 0 < s)
    (m ξ : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) (generalizedExtremeValueMeasure m s ξ) ↔
      (n : ℝ) * ξ < 1 := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  by_cases hn : n = 0
  · subst n
    simp
  have h := integrable_norm_rpow_iff
    (μ := generalizedExtremeValueMeasure m s ξ) aestronglyMeasurable_id
    (p := (n : ℝ≥0∞)) (by exact_mod_cast hn) (by simp)
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, id_eq,
    NNReal.coe_natCast] using
    h.trans (memLp_id_generalizedExtremeValueMeasure_iff hs m ξ (n : ℝ≥0))

/-- Natural raw moments have the same sharp integrability threshold as absolute moments. -/
@[simp]
theorem integrable_pow_generalizedExtremeValueMeasure_iff (hs : 0 < s)
    (m ξ : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (generalizedExtremeValueMeasure m s ξ) ↔
      (n : ℝ) * ξ < 1 := by
  rw [← integrable_pow_abs_generalizedExtremeValueMeasure_iff hs m ξ n]
  simpa only [Real.norm_eq_abs, norm_pow] using
    (integrable_norm_iff (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ x ^ n)
      (generalizedExtremeValueMeasure m s ξ))).symm

/-- Natural raw moments at nonzero shape, expressed by the binomial expansion of the
exponential-variable construction. The strict threshold ensures absolute integrability. -/
theorem integral_pow_generalizedExtremeValueMeasure (hs : 0 < s) (hξ : ξ ≠ 0)
    (m : ℝ) (n : ℕ) (hn : (n : ℝ) * ξ < 1) :
    ∫ x, x ^ n ∂generalizedExtremeValueMeasure m s ξ =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (m - s / ξ) ^ (n - k) *
        (s / ξ) ^ k * Real.Gamma (1 - (k : ℝ) * ξ) := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  let ν := (expMeasure 1).map fun e : ℝ ↦ e ^ (-ξ)
  have hsource : Integrable (fun x : ℝ ↦ |x| ^ n) ν := by
    have hLp := (memLp_id_generalizedExtremeValueMeasure_iff hs m ξ (n : ℝ≥0)).2 hn
    rw [gev_eq_map_affine hs hξ, memLp_id_map_affine_iff (div_ne_zero hs.ne' hξ)] at hLp
    simpa only [id_eq, Real.norm_eq_abs] using hLp.integrable_norm_pow'
  have h := moment_id_map_affine (μ := ν) (a := m - s / ξ) (b := s / ξ) hsource
  simp only [moment_def, Pi.pow_apply, id_eq] at h
  rw [gev_eq_map_affine hs hξ, h]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkξ : (k : ℝ) * ξ < 1 := by
    rcases le_or_gt ξ 0 with hξ' | hξ'
    · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hξ') zero_lt_one
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hkn hξ'.le) hn
  have heq : (fun e : ℝ ↦ (e ^ (-ξ)) ^ k) =ᵐ[expMeasure 1]
      fun e ↦ e ^ (-ξ * (k : ℝ)) := by
    filter_upwards [ae_pos_expMeasure 1] with e he
    exact (Real.rpow_mul_natCast he.le _ _).symm
  rw [integral_map (by fun_prop) (by fun_prop), integral_congr_ae heq,
    integral_rpow_expMeasure one_pos (by nlinarith), Real.one_rpow, div_one]
  congr 2
  ring

/-- The identity is integrable exactly when the shape is less than one. -/
@[simp]
theorem integrable_id_generalizedExtremeValueMeasure_iff (hs : 0 < s) (m ξ : ℝ) :
    Integrable id (generalizedExtremeValueMeasure m s ξ) ↔ ξ < 1 := by
  simpa only [pow_one, Nat.cast_one, one_mul, Function.id_def] using
    integrable_pow_generalizedExtremeValueMeasure_iff hs m ξ 1

/-- The mean of a generalized extreme-value law at nonzero shape. -/
@[simp]
theorem integral_id_generalizedExtremeValueMeasure (hs : 0 < s) (hξ : ξ ≠ 0)
    (hξ₁ : ξ < 1) (m : ℝ) :
    ∫ x, x ∂generalizedExtremeValueMeasure m s ξ =
      m + s * (Real.Gamma (1 - ξ) - 1) / ξ := by
  have h := integral_pow_generalizedExtremeValueMeasure hs hξ m 1 (by simpa using hξ₁)
  norm_num [Finset.sum_range_succ] at h
  rw [h]
  ring

/-- The variance of a generalized extreme-value law with a finite second moment, at nonzero
shape. Shape zero is the Gumbel variance. -/
@[simp]
theorem variance_id_generalizedExtremeValueMeasure (hs : 0 < s) (hξ : ξ ≠ 0)
    (hξ₂ : ξ < (2 : ℝ)⁻¹) (m : ℝ) :
    variance id (generalizedExtremeValueMeasure m s ξ) =
      s ^ 2 * (Real.Gamma (1 - 2 * ξ) - Real.Gamma (1 - ξ) ^ 2) / ξ ^ 2 := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  have hLp : MemLp id 2 (generalizedExtremeValueMeasure m s ξ) := by
    simpa using (memLp_id_generalizedExtremeValueMeasure_iff hs m ξ 2).2 (by norm_num; linarith)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_id_generalizedExtremeValueMeasure hs hξ (by linarith) m,
    integral_pow_generalizedExtremeValueMeasure hs hξ m 2 (by norm_num; linarith)]
  norm_num [Finset.sum_range_succ]
  ring

end TauCeti.Probability
