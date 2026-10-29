/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.DiscreteLaplace.Basic
public import TauCeti.Probability.Distributions.Geometric.Basic
import TauCeti.Analysis.SpecialFunctions.Log.MulExpLtOne
import TauCeti.Probability.Distributions.NegativeBinomial.Transforms
import TauCeti.Probability.Distributions.Sums
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Moments and transforms of the discrete Laplace distribution

For `0 ≤ q < 1`, the real cast of a discrete Laplace variable with integer center `m` has
exponential-integrability domain

`{t | q * exp t < 1 ∧ q * exp (-t) < 1}`.

When `0 < q`, this is the symmetric interval `(log q, -log q)`. Its moment-generating function
factors through the two geometric tails. The resulting mean is `m` and the variance is
`2q / (1 - q) ^ 2`. The boundary `q = 0` is the point mass at `m` and is included in the general
formulas.

The proofs use the representation as the difference of two independent geometric variables.

## References

* S. Inusah and T. J. Kozubowski, *A discrete analogue of the Laplace distribution*, Journal of
  Statistical Planning and Inference 136 (2006), 1090–1102.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {q t : ℝ}

/-- Real casting identifies a discrete Laplace law with an integer translate of the difference of
two real-cast geometric laws. -/
theorem map_intCast_discreteLaplaceMeasure (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ) =
      (((geometricMeasure ⟨1 - q, by constructor <;> linarith⟩).map (Nat.cast : ℕ → ℝ)).prod
        ((geometricMeasure ⟨1 - q, by constructor <;> linarith⟩).map (Nat.cast : ℕ → ℝ))).map
          (fun z : ℝ × ℝ ↦ (m : ℝ) + z.1 - z.2) := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := by
    intro h
    have : (p : ℝ) = 0 := congrArg Subtype.val h
    simp [p] at this
    linarith
  have hm := map_add_const_discreteLaplaceMeasure 0 m q
  simp only [zero_add] at hm
  have hsub := map_sub_prod_geometricMeasure hp
  have hpq : (1 : ℝ) - p = q := by simp [p]
  rw [hpq] at hsub
  rw [← hm, Measure.map_map (by fun_prop) (by fun_prop),
    ← hsub, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards with z
  simp
  ring

private theorem memLp_id_map_cast_geometricMeasure_of_ne_zero (p : unitInterval) (hp : p ≠ 0)
    (r : ℝ≥0) : MemLp id r ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) := by
  rw [geometricMeasure_eq_negativeBinomialMeasure_one p hp]
  exact memLp_id_map_cast_negativeBinomialMeasure zero_le_one
    (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)) p.2.2 r

private theorem mgf_intCast_discreteLaplaceMeasure_eq_mul (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    mgf (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) t =
      exp (t * m) *
        (mgf id ((geometricMeasure ⟨1 - q, by constructor <;> linarith⟩).map
            (Nat.cast : ℕ → ℝ)) t *
          mgf id ((geometricMeasure ⟨1 - q, by constructor <;> linarith⟩).map
            (Nat.cast : ℕ → ℝ)) (-t)) := by
  rw [← mgf_id_map (by fun_prop), map_intCast_discreteLaplaceMeasure m hq0 hq1,
    mgf_id_map (by fun_prop), mgf]
  have hfactor : (fun z : ℝ × ℝ ↦ exp (t * ((m : ℝ) + z.1 - z.2))) =
      fun z ↦ exp (t * m) * (exp (t * z.1) * exp (-t * z.2)) := by
    funext z
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  rw [hfactor, integral_const_mul,
    integral_prod_mul (fun x : ℝ ↦ exp (t * x)) (fun x : ℝ ↦ exp (-t * x))]
  simp only [mgf, id_eq]

/-- Exponentials of a discrete Laplace variable are integrable exactly when both geometric tails
converge. The statement includes `q = 0`, when both inequalities hold for every `t`. -/
theorem integrable_exp_mul_intCast_discreteLaplaceMeasure_iff (m : ℤ) (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    Integrable (fun k : ℤ ↦ exp (t * k)) (discreteLaplaceMeasure m q) ↔
      q * exp t < 1 ∧ q * exp (-t) < 1 := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := by
    intro h
    have : (p : ℝ) = 0 := congrArg Subtype.val h
    simp [p] at this
    linarith
  let _ := isProbabilityMeasure_discreteLaplaceMeasure m hq0 hq1
  let _ : IsProbabilityMeasure (geometricMeasure p) := inferInstance
  have hright : 0 < mgf id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) t ↔
      q * exp t < 1 := by
    rw [mgf_pos_iff]
    simpa [p] using integrable_exp_mul_id_map_cast_geometricMeasure_iff hp t
  have hleft : 0 < mgf id ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) (-t) ↔
      q * exp (-t) < 1 := by
    rw [mgf_pos_iff]
    simpa [p] using integrable_exp_mul_id_map_cast_geometricMeasure_iff hp (-t)
  rw [← mgf_pos_iff, mgf_intCast_discreteLaplaceMeasure_eq_mul m hq0 hq1,
    mul_pos_iff_of_pos_left (exp_pos _), mul_pos_iff]
  simp only [not_lt_of_ge mgf_nonneg, and_false, or_false]
  simpa [p] using and_congr hright hleft

/-- The exact exponential-integrability domain of a discrete Laplace variable, including the
point-mass boundary `q = 0`. -/
theorem integrableExpSet_intCast_discreteLaplaceMeasure (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    integrableExpSet (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) =
      {t | q * exp t < 1 ∧ q * exp (-t) < 1} := by
  ext u
  exact integrable_exp_mul_intCast_discreteLaplaceMeasure_iff m hq0 hq1

/-- For `0 < q < 1`, the exponential-integrability domain is the symmetric open interval
`(log q, -log q)`. -/
theorem integrableExpSet_intCast_discreteLaplaceMeasure_of_pos (m : ℤ) (hq0 : 0 < q)
    (hq1 : q < 1) :
    integrableExpSet (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) =
      Ioo (log q) (-log q) := by
  rw [integrableExpSet_intCast_discreteLaplaceMeasure m hq0.le hq1]
  ext u
  simp only [mem_ofPred_eq, mem_Ioo]
  rw [Real.mul_exp_lt_one_iff hq0, Real.mul_exp_lt_one_iff hq0]
  constructor
  · rintro ⟨hu, hu'⟩
    exact ⟨by linarith, hu⟩
  · rintro ⟨hu, hu'⟩
    exact ⟨hu', by linarith⟩

/-- The moment-generating function of the real-cast discrete Laplace law on its exact domain. -/
theorem mgf_intCast_discreteLaplaceMeasure (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ht : q * exp t < 1 ∧ q * exp (-t) < 1) :
    mgf (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) t =
      exp (m * t) * (1 - q) ^ 2 / ((1 - q * exp t) * (1 - q * exp (-t))) := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := by
    intro h
    have : (p : ℝ) = 0 := congrArg Subtype.val h
    simp [p] at this
    linarith
  rw [mgf_intCast_discreteLaplaceMeasure_eq_mul m hq0 hq1,
    mgf_id_map_cast_geometricMeasure hp (by simpa [p] using ht.1),
    mgf_id_map_cast_geometricMeasure hp (by simpa [p] using ht.2)]
  simp only [p]
  rw [mul_comm t (m : ℝ)]
  have htpos : 1 - q * exp t ≠ 0 := (sub_pos.mpr ht.1).ne'
  have htneg : 1 - q * exp (-t) ≠ 0 := (sub_pos.mpr ht.2).ne'
  field_simp [htpos, htneg]
  ring

/-- The cumulant-generating function of the real-cast discrete Laplace law on its exact domain. -/
theorem cgf_intCast_discreteLaplaceMeasure (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ht : q * exp t < 1 ∧ q * exp (-t) < 1) :
    cgf (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) t =
      m * t + 2 * log (1 - q) - log (1 - q * exp t) - log (1 - q * exp (-t)) := by
  have hq : 0 < 1 - q := sub_pos.mpr hq1
  have htpos : 0 < 1 - q * exp t := sub_pos.mpr ht.1
  have htneg : 0 < 1 - q * exp (-t) := sub_pos.mpr ht.2
  rw [cgf, mgf_intCast_discreteLaplaceMeasure m hq0 hq1 ht]
  rw [div_eq_mul_inv,
    log_mul (mul_pos (exp_pos _) (sq_pos_of_pos hq)).ne'
      (inv_pos.mpr (mul_pos htpos htneg)).ne',
    log_mul (exp_pos _).ne' (sq_pos_of_pos hq).ne', log_exp,
    log_pow, log_inv, log_mul htpos.ne' htneg.ne']
  ring

/-- Every natural moment of a valid discrete Laplace law is absolutely integrable. -/
theorem integrable_pow_intCast_discreteLaplaceMeasure (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) : Integrable (fun k : ℤ ↦ (k : ℝ) ^ n) (discreteLaplaceMeasure m q) := by
  by_cases hq : q = 0
  · subst q
    rw [discreteLaplaceMeasure_zero_right]
    exact integrable_dirac (by simp)
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have hlog : 0 < -log q := neg_pos.mpr (log_neg hqpos hq1)
    let a := -log q / 2
    have ha : 0 < a := div_pos hlog zero_lt_two
    have halt : a < -log q := by dsimp [a]; linarith
    have hnegalt : -a < -log q := (neg_lt_zero.mpr ha).trans hlog
    exact integrable_pow_of_integrable_exp_mul ha.ne'
      ((integrable_exp_mul_intCast_discreteLaplaceMeasure_iff m hq0 hq1).2 ⟨
        (Real.mul_exp_lt_one_iff hqpos).2 halt,
        (Real.mul_exp_lt_one_iff hqpos).2 hnegalt⟩)
      ((integrable_exp_mul_intCast_discreteLaplaceMeasure_iff m hq0 hq1).2 ⟨
        (Real.mul_exp_lt_one_iff hqpos).2 hnegalt,
        (Real.mul_exp_lt_one_iff hqpos).2 (by simpa only [neg_neg] using halt)⟩) n

/-- The mean of a discrete Laplace law is its integer center. -/
@[simp]
theorem integral_intCast_discreteLaplaceMeasure (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∫ k : ℤ, (k : ℝ) ∂discreteLaplaceMeasure m q = m := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  let μ := (geometricMeasure p).map (Nat.cast : ℕ → ℝ)
  have hμdef : (geometricMeasure p).map (Nat.cast : ℕ → ℝ) = μ := rfl
  have hp : p ≠ 0 := by
    intro h
    have : (p : ℝ) = 0 := congrArg Subtype.val h
    simp [p] at this
    linarith
  let _ : IsProbabilityMeasure μ := inferInstance
  have hμ : Integrable id μ :=
    (memLp_id_map_cast_geometricMeasure_of_ne_zero p hp 2).integrable one_le_two
  have hfst : Integrable (fun z : ℝ × ℝ ↦ z.1) (μ.prod μ) := hμ.comp_fst μ
  have hsnd : Integrable (fun z : ℝ × ℝ ↦ z.2) (μ.prod μ) := hμ.comp_snd μ
  have hifst : (∫ z : ℝ × ℝ, z.1 ∂μ.prod μ) = ∫ x, x ∂μ := by
    simpa only [id_eq, mul_one, integral_const, probReal_univ, one_smul] using
      (integral_prod_mul (μ := μ) (ν := μ) id (fun _ : ℝ ↦ 1))
  have hisnd : (∫ z : ℝ × ℝ, z.2 ∂μ.prod μ) = ∫ x, x ∂μ := by
    simpa only [id_eq, one_mul, integral_const, probReal_univ, one_smul] using
      (integral_prod_mul (μ := μ) (ν := μ) (fun _ : ℝ ↦ 1) id)
  have hcast : (∫ x : ℝ, x ∂(discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)) =
      ∫ k : ℤ, (k : ℝ) ∂discreteLaplaceMeasure m q := by
    simpa only using integral_map (μ := discreteLaplaceMeasure m q)
      (φ := (Int.cast : ℤ → ℝ)) (by fun_prop) (by fun_prop)
  have hsplit : (∫ z : ℝ × ℝ, (m : ℝ) + z.1 - z.2 ∂μ.prod μ) =
      (∫ z : ℝ × ℝ, (m : ℝ) + z.1 ∂μ.prod μ) - ∫ z : ℝ × ℝ, z.2 ∂μ.prod μ := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_sub ((integrable_const (m : ℝ)).add hfst) hsnd
  have hadd : (∫ z : ℝ × ℝ, (m : ℝ) + z.1 ∂μ.prod μ) =
      (∫ _ : ℝ × ℝ, (m : ℝ) ∂μ.prod μ) + ∫ z : ℝ × ℝ, z.1 ∂μ.prod μ := by
    simpa only [Pi.add_apply] using integral_add (integrable_const (m : ℝ)) hfst
  rw [← hcast, map_intCast_discreteLaplaceMeasure m hq0 hq1, hμdef,
    integral_map (by fun_prop) (by fun_prop), hsplit, hadd, integral_const, hifst, hisnd]
  simp

/-- The variance of a discrete Laplace law is `2q / (1 - q)²`. -/
@[simp]
theorem variance_intCast_discreteLaplaceMeasure (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    variance (Int.cast : ℤ → ℝ) (discreteLaplaceMeasure m q) =
      2 * q / (1 - q) ^ 2 := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  let μ := (geometricMeasure p).map (Nat.cast : ℕ → ℝ)
  have hμdef : (geometricMeasure p).map (Nat.cast : ℕ → ℝ) = μ := rfl
  have hp : p ≠ 0 := by
    intro h
    have : (p : ℝ) = 0 := congrArg Subtype.val h
    simp [p] at this
    linarith
  let _ : IsProbabilityMeasure μ := inferInstance
  have hμ : MemLp id 2 μ := memLp_id_map_cast_geometricMeasure_of_ne_zero p hp 2
  have hfun : (fun z : ℝ × ℝ ↦ (m : ℝ) + z.1 - z.2) =
      fun z ↦ (m : ℝ) + (z.1 + -z.2) := by
    funext z
    ring
  rw [← variance_id_map (μ := discreteLaplaceMeasure m q) (by fun_prop),
    map_intCast_discreteLaplaceMeasure m hq0 hq1, hμdef, variance_id_map (by fun_prop), hfun,
    variance_const_add (by fun_prop)]
  have hvar : variance (fun z : ℝ × ℝ ↦ z.1 + -z.2) (μ.prod μ) =
      variance id μ + variance (-id) μ := by
    have hadd : (fun z : ℝ × ℝ ↦ z.1 + -z.2) =
        fun z ↦ id z.1 + (-id) z.2 := by
      funext z
      rfl
    rw [hadd]
    exact variance_add_prod hμ hμ.neg
  rw [hvar, variance_neg, variance_id_map_cast_geometricMeasure]
  simp only [p]
  have hne : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  field_simp
  ring

/-- The characteristic function of the real-cast discrete Laplace law. -/
theorem charFun_map_intCast_discreteLaplaceMeasure (m : ℤ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (t : ℝ) :
    charFun ((discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)) t =
      Complex.exp (Complex.I * t * m) * (1 - q) ^ 2 /
        ((1 - q * Complex.exp (Complex.I * t)) *
          (1 - q * Complex.exp (-Complex.I * t))) := by
  let p : unitInterval := ⟨1 - q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := by
    intro h
    have : (p : ℝ) = 0 := congrArg Subtype.val h
    simp [p] at this
    linarith
  rw [map_intCast_discreteLaplaceMeasure m hq0 hq1, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_intCast]
  have hfactor :
      (fun z : ℝ × ℝ ↦
        Complex.exp ((t : ℂ) * ((m : ℂ) + z.1 - z.2) * Complex.I)) =
        fun z ↦ Complex.exp (Complex.I * t * (m : ℂ)) *
          (Complex.exp ((t : ℂ) * z.1 * Complex.I) *
            Complex.exp ((-t : ℂ) * z.2 * Complex.I)) := by
    funext z
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hfactor, integral_const_mul,
    integral_prod_mul (fun x : ℝ ↦ Complex.exp ((t : ℂ) * x * Complex.I))
      (fun x : ℝ ↦ Complex.exp ((-t : ℂ) * x * Complex.I)),
    ← charFun_apply_real, ← Complex.ofReal_neg, ← charFun_apply_real,
    charFun_map_cast_geometricMeasure hp, charFun_map_cast_geometricMeasure hp]
  simp only [p]
  have hexpneg : Complex.exp (Complex.I * (-t : ℂ)) =
      Complex.exp (-Complex.I * t) := by
    congr 1
    ring
  simp only [Complex.ofReal_neg]
  rw [hexpneg]
  push_cast
  have hdenpos : (1 - (q : ℂ) * Complex.exp (Complex.I * t)) ≠ 0 := by
    intro h
    have heq : (q : ℂ) * Complex.exp (Complex.I * t) = 1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm heq
    simp [Complex.norm_exp, abs_of_nonneg hq0] at hn
    linarith
  have hdenneg : (1 - (q : ℂ) * Complex.exp (-Complex.I * t)) ≠ 0 := by
    intro h
    have heq : (q : ℂ) * Complex.exp (-Complex.I * t) = 1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm heq
    simp [Complex.norm_exp, abs_of_nonneg hq0] at hn
    linarith
  field_simp [hdenpos, hdenneg]
  ring

end TauCeti.Probability
