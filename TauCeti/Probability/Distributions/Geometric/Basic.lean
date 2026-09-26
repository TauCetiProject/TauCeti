/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import TauCeti.Probability.GeneratingFunction

import TauCeti.Probability.Distributions.NegativeBinomial.Transforms

/-!
# Elementary theory of the geometric distribution

This file develops moments and transforms of Mathlib's geometric measure, using the convention
that the random variable counts failures before the first success.  It also records its cumulative
mass and memoryless tail identity.  Mathlib totalizes the zero-success parameter by
`geometricMeasure 0 = Measure.dirac 0`; the boundary formulas are stated separately.  The
hypotheses `p ≠ 0` below only exclude that totalized boundary: they still admit the degenerate
endpoint `p = 1`, where the law is Dirac at zero and the formulas below specialize to the constant
random variable `0`.

For `p ≠ 0` the geometric law is the negative-binomial law of shape one
(`geometricMeasure_eq_negativeBinomialMeasure_one`), so its transforms and moments are
specializations of the negative-binomial ones.

## Main results

* `integral_id_map_cast_geometricMeasure` and `variance_id_map_cast_geometricMeasure` compute the
  mean and variance of the real cast of a geometric law.
* `integrableExpSet_id_map_cast_geometricMeasure` and `mgf_id_map_cast_geometricMeasure` give its
  exact moment-generating domain and moment-generating function.
* `integrable_pow_geometricMeasure_iff` and `pgf_geometricMeasure` give the exact
  probability-generating domain and probability-generating function on the native carrier.
* `charFun_map_cast_geometricMeasure` computes its characteristic function.
* `geometricMeasure_real_Iic` and `geometricMeasure_memoryless` give the cumulative mass and the
  division-free memoryless identity on the native carrier.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley, 2005, Chapter 5.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {p : unitInterval}

/-- For a nonzero success probability, the geometric probability-generating-function integrand
is integrable exactly on the open interval determined by the geometric-series ratio. -/
theorem integrable_pow_geometricMeasure_iff (hp : p ≠ 0) (t : ℝ) :
    Integrable (fun n : ℕ => t ^ n) (geometricMeasure p) ↔
      |(1 - (p : ℝ)) * t| < 1 := by
  rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp]
  exact integrable_pow_negativeBinomialMeasure_iff one_pos
    (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2 t

/-- The probability-generating function of a geometric distribution with nonzero parameter, on its
exact integrability domain.  The boundary case `p = 1`, whose law is a Dirac mass at zero, is
included. -/
theorem pgf_geometricMeasure (hp : p ≠ 0) {t : ℝ}
    (ht : |(1 - (p : ℝ)) * t| < 1) :
    pgf id (geometricMeasure p) t = (p : ℝ) / (1 - (1 - (p : ℝ)) * t) := by
  rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp,
    pgf_negativeBinomialMeasure one_pos
      (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2 ht]
  exact Real.rpow_one _

/-- The exponential integrand for the cast geometric law is integrable exactly below the pole of
its geometric series. -/
theorem integrable_exp_mul_id_map_cast_geometricMeasure_iff (hp : p ≠ 0) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x))
        ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) ↔
      (1 - (p : ℝ)) * exp t < 1 := by
  rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp]
  exact integrable_exp_mul_id_map_cast_negativeBinomialMeasure_iff one_pos
    (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2 t

/-- The exact moment-generating domain of the real cast of a nonzero-parameter geometric law. -/
theorem integrableExpSet_id_map_cast_geometricMeasure (hp : p ≠ 0) :
    integrableExpSet id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) =
      {t | (1 - (p : ℝ)) * exp t < 1} := by
  rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp]
  exact integrableExpSet_id_map_cast_negativeBinomialMeasure one_pos
    (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2

/-- The moment-generating function of the real cast of a nonzero-parameter geometric law. -/
theorem mgf_id_map_cast_geometricMeasure (hp : p ≠ 0)
    (ht : (1 - (p : ℝ)) * exp t < 1) :
    mgf id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      (p : ℝ) / (1 - (1 - (p : ℝ)) * exp t) := by
  rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp,
    mgf_id_map_cast_negativeBinomialMeasure zero_le_one
      (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2 ht]
  exact Real.rpow_one _

/-- The cumulant-generating function of the real cast of a nonzero-parameter geometric law. -/
theorem cgf_id_map_cast_geometricMeasure (hp : p ≠ 0)
    (ht : (1 - (p : ℝ)) * exp t < 1) :
    cgf id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      log ((p : ℝ) / (1 - (1 - (p : ℝ)) * exp t)) := by
  rw [cgf, mgf_id_map_cast_geometricMeasure hp ht]

/-- The mean of the real cast of a geometric law. -/
theorem integral_id_map_cast_geometricMeasure :
    ∫ x, x ∂((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) =
      (1 - (p : ℝ)) / (p : ℝ) := by
  by_cases hp : p = 0
  · subst p
    norm_num [geometricMeasure]
  · rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp,
      integral_id_map_cast_negativeBinomialMeasure zero_le_one
        (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2, one_mul]

/-- The variance of the real cast of a geometric law. -/
theorem variance_id_map_cast_geometricMeasure :
    variance id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) =
      (1 - (p : ℝ)) / (p : ℝ) ^ 2 := by
  by_cases hp : p = 0
  · subst p
    norm_num [geometricMeasure]
  · rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp,
      variance_id_map_cast_negativeBinomialMeasure zero_le_one
        (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2, one_mul]

/-- The characteristic function of the real cast of a nonzero-parameter geometric law. -/
theorem charFun_map_cast_geometricMeasure (hp : p ≠ 0) (t : ℝ) :
    charFun ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) t =
      (p : ℂ) / (1 - (1 - (p : ℂ)) * Complex.exp (Complex.I * t)) := by
  rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp,
    charFun_map_cast_negativeBinomialMeasure zero_le_one
      (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2,
    Complex.ofReal_one, Complex.cpow_one]

/-- The cumulative mass of a nonzero-parameter geometric law on its native carrier. -/
theorem geometricMeasure_real_Iic (hp : p ≠ 0) (n : ℕ) :
    (geometricMeasure p).real {k | k ≤ n} = 1 - (1 - (p : ℝ)) ^ (n + 1) := by
  have hset : {k : ℕ | k ≤ n} = (Finset.Iic n : Set ℕ) := by ext k; simp
  rw [hset, ← sum_measureReal_singleton]
  simp_rw [geometricMeasure_real_singleton hp]
  have hIic : Finset.Iic n = Finset.range (n + 1) := by ext k; simp
  rw [hIic, ← Finset.sum_mul]
  have h := geom_sum_mul_of_le_one (sub_le_self 1 p.2.1) (n + 1)
  convert h using 1
  ring

/-- The upper-tail mass of a nonzero-parameter geometric law on its native carrier. -/
theorem geometricMeasure_real_Ici (hp : p ≠ 0) (n : ℕ) :
    (geometricMeasure p).real {k | n ≤ k} = (1 - (p : ℝ)) ^ n := by
  have hcompl : {k : ℕ | n ≤ k} = {k : ℕ | k < n}ᶜ := by ext k; simp
  rw [hcompl, probReal_compl_eq_one_sub (MeasurableSet.of_discrete :
    MeasurableSet {k : ℕ | k < n})]
  have hset : {k : ℕ | k < n} = (Finset.range n : Set ℕ) := by ext k; simp
  rw [hset, ← sum_measureReal_singleton]
  simp_rw [geometricMeasure_real_singleton hp]
  rw [← Finset.sum_mul]
  calc
    1 - (∑ i ∈ Finset.range n, (1 - (p : ℝ)) ^ i) * (p : ℝ) =
        1 - (∑ i ∈ Finset.range n, (1 - (p : ℝ)) ^ i) *
          (1 - (1 - (p : ℝ))) := by ring
    _ = (1 - (p : ℝ)) ^ n := by
      rw [geom_sum_mul_of_le_one (sub_le_self 1 p.2.1)]
      ring

/-- The geometric law is memoryless for every parameter: the mass of the tail beyond `n + m`
is the product of the masses of the tails beyond `n` and beyond `m`. -/
theorem geometricMeasure_memoryless (p : unitInterval) (n m : ℕ) :
    (geometricMeasure p).real {k | n + m ≤ k} =
      (geometricMeasure p).real {k | n ≤ k} * (geometricMeasure p).real {k | m ≤ k} := by
  by_cases hp : p = 0
  · subst p
    rcases n with _ | n <;> rcases m with _ | m <;>
      simp [geometricMeasure, measureReal_def]
  · rw [geometricMeasure_real_Ici hp, geometricMeasure_real_Ici hp,
      geometricMeasure_real_Ici hp, pow_add]

/-- Conditional form of geometric memorylessness, stated only when the conditioning tail has
nonzero mass. -/
theorem geometricMeasure_cond_Ici (p : unitInterval) (n m : ℕ)
    (hn : geometricMeasure p {k | n ≤ k} ≠ 0) :
    (ProbabilityTheory.cond (geometricMeasure p) {k | n ≤ k}).real {k | n + m ≤ k} =
      (geometricMeasure p).real {k | m ≤ k} := by
  by_cases hp : p = 0
  · subst p
    rcases n with _ | n
    · simp [geometricMeasure]
    · simp [geometricMeasure] at hn
  · rw [measureReal_def,
      cond_apply (MeasurableSet.of_discrete : MeasurableSet {k : ℕ | n ≤ k}),
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hinter : {k : ℕ | n ≤ k} ∩ {k | n + m ≤ k} = {k | n + m ≤ k} := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      omega
    rw [hinter, ← measureReal_def, ← measureReal_def, geometricMeasure_real_Ici hp,
      geometricMeasure_real_Ici hp, geometricMeasure_real_Ici hp, pow_add]
    have hn' : (1 - (p : ℝ)) ^ n ≠ 0 := by
      rw [← geometricMeasure_real_Ici hp]
      exact (measureReal_ne_zero_iff (μ := geometricMeasure p) (s := {k | n ≤ k})).2 hn
    field_simp

/-- At success probability zero, Mathlib's totalized geometric law is Dirac at zero. -/
theorem geometricMeasure_zero : geometricMeasure (0 : unitInterval) = Measure.dirac 0 := by
  simp [geometricMeasure]

/-- At the zero parameter, Mathlib's geometric distribution is a Dirac mass at zero, so its
probability-generating function is identically one. -/
@[simp]
theorem pgf_geometricMeasure_zero (t : ℝ) : pgf id (geometricMeasure 0) t = 1 := by
  rw [geometricMeasure_zero, pgf_def]
  simp

/-- The real cast of the zero-parameter geometric law has every exponential moment. -/
@[simp] theorem integrableExpSet_id_map_cast_geometricMeasure_zero :
    integrableExpSet id
      ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) = Set.univ := by
  rw [geometricMeasure_zero, Measure.map_dirac' (by fun_prop)]
  norm_num
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_dirac (by simp)

/-- The moment-generating function at the zero parameter is identically one. -/
@[simp] theorem mgf_id_map_cast_geometricMeasure_zero (t : ℝ) :
    mgf id ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) t = 1 := by
  rw [geometricMeasure_zero, Measure.map_dirac' (by fun_prop)]
  norm_num
  rw [mgf_dirac']
  simp

/-- The cumulant-generating function at the zero parameter is identically zero. -/
@[simp] theorem cgf_id_map_cast_geometricMeasure_zero (t : ℝ) :
    cgf id ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) t = 0 := by
  rw [cgf, mgf_id_map_cast_geometricMeasure_zero]
  simp

/-- The zero-parameter geometric law has mean zero after casting to the reals. -/
@[simp] theorem integral_id_map_cast_geometricMeasure_zero :
    ∫ x, x ∂((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) = 0 := by
  simpa using integral_id_map_cast_geometricMeasure (p := 0)

/-- The zero-parameter geometric law has variance zero after casting to the reals. -/
@[simp] theorem variance_id_map_cast_geometricMeasure_zero :
    variance id ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) = 0 := by
  simpa using variance_id_map_cast_geometricMeasure (p := 0)

/-- The characteristic function at the zero parameter is identically one. -/
@[simp] theorem charFun_map_cast_geometricMeasure_zero (t : ℝ) :
    charFun ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) t = 1 := by
  rw [geometricMeasure_zero, Measure.map_dirac' (by fun_prop)]
  norm_num

/-- The cumulative mass of the zero-parameter geometric law is one at every natural cutoff. -/
@[simp] theorem geometricMeasure_real_Iic_zero (n : ℕ) :
    (geometricMeasure (0 : unitInterval)).real {k | k ≤ n} = 1 := by
  rw [geometricMeasure_zero]
  rw [measureReal_def, Measure.dirac_apply_of_mem (by simp)]
  simp

/-- A real random variable with a geometric law has mean `(1 - p) / p`. -/
theorem integral_of_hasLaw_map_cast_geometricMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) :
    P[X] = (1 - (p : ℝ)) / (p : ℝ) := by
  rw [hX.integral_eq, integral_id_map_cast_geometricMeasure]

/-- A real random variable with a geometric law has variance `(1 - p) / p²`. -/
theorem variance_of_hasLaw_map_cast_geometricMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) :
    variance X P = (1 - (p : ℝ)) / (p : ℝ) ^ 2 := by
  rw [hX.variance_eq, variance_id_map_cast_geometricMeasure]

end Probability

end TauCeti
