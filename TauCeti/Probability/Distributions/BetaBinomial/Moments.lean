/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaBinomial.Basic
public import TauCeti.Probability.Distributions.Binomial.Basic

/-!
# Moments of the beta-binomial distribution

For positive shapes `a` and `b`, the beta-binomial law has mean `n * a / (a + b)` and variance
`n * (a / (a + b)) * (1 - a / (a + b)) * (a + b + n) / (a + b + 1)`.
These formulas include zero trials. All functions on its finite native support are integrable,
including every natural moment of the real cast law.

The mixture integration formula reduces the calculation to the existing binomial mean and
second moment and the Beta mean and variance. It also permits integration of other observables
without expanding the beta-binomial masses.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- Every natural raw moment of the real cast beta-binomial law is a finite Beta-function sum.
Integrability is given by `integrable_map_cast_betaBinomialMeasure`. -/
theorem integral_pow_map_cast_betaBinomialMeasure {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (n m : ℕ) :
    ∫ x : ℝ, x ^ m ∂((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) =
      ∑ k ∈ Finset.Iic n,
        (n.choose k * beta (a + k) (b + (n - k)) / beta a b) * (k : ℝ) ^ m := by
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integral_map,
    integral_betaBinomialMeasure _ ha hb]
  simp only [smul_eq_mul]

/-- The mean of the real cast of a beta-binomial law. -/
@[simp]
theorem integral_id_map_cast_betaBinomialMeasure {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ x, x ∂((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) =
      (n : ℝ) * a / (a + b) := by
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_betaBinomialMeasure_eq_integral ha hb]
  have hmean (p : unitInterval) :
      ∫ k : ℕ, (k : ℝ) ∂binomial n p = (p : ℝ) * n :=
    integral_of_hasLaw_binomial (hasLaw_map (by fun_prop))
  simp_rw [hmean]
  calc
    _ = ∫ p : ℝ, p * n ∂betaMeasure a b := by
      apply integral_congr_ae
      filter_upwards [ae_mem_Ioo_betaMeasure a b] with p hp
      rw [Set.projIcc_of_mem zero_le_one ⟨hp.1.le, hp.2.le⟩]
    _ = (n : ℝ) * a / (a + b) := by
      rw [integral_mul_const, integral_id_betaMeasure ha hb]
      ring

/-- The second raw moment of the real cast of a beta-binomial law. -/
theorem integral_sq_id_map_cast_betaBinomialMeasure {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ x : ℝ, x ^ 2 ∂((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) =
      (n : ℝ) * a / (a + b) + (n : ℝ) * ((n : ℝ) - 1) * a * (a + 1) /
        ((a + b) * (a + b + 1)) := by
  let _ := isProbabilityMeasureBeta ha hb
  have hmem : MemLp id 2 (betaMeasure a b) :=
    memLp_of_bounded (ae_mem_Icc_betaMeasure a b) measurable_id.aestronglyMeasurable 2
  have hsecond : ∫ p : ℝ, p ^ 2 ∂betaMeasure a b =
      a * (a + 1) / ((a + b) * (a + b + 1)) := by
    have hv := variance_eq_sub hmem
    simp only [Pi.pow_apply, id_eq, variance_id_betaMeasure ha hb,
      integral_id_betaMeasure ha hb] at hv
    have hab : a + b ≠ 0 := (add_pos ha hb).ne'
    have hab1 : a + b + 1 ≠ 0 := by positivity
    apply (sub_eq_iff_eq_add.mp hv.symm).trans
    field_simp
    ring
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_betaBinomialMeasure_eq_integral ha hb]
  have hbin (p : unitInterval) : ∫ k : ℕ, (k : ℝ) ^ 2 ∂binomial n p =
      (p : ℝ) * (1 - p) * n + ((p : ℝ) * n) ^ 2 := by
    have hi := integral_sq_id_map_cast_binomial n p
    rw [integral_map (by fun_prop) (by fun_prop)] at hi
    exact hi
  simp_rw [hbin]
  calc
    _ = ∫ p : ℝ, (n : ℝ) * p + ((n : ℝ) * ((n : ℝ) - 1)) * p ^ 2
        ∂betaMeasure a b := by
      apply integral_congr_ae
      filter_upwards [ae_mem_Ioo_betaMeasure a b] with p hp
      rw [Set.projIcc_of_mem zero_le_one ⟨hp.1.le, hp.2.le⟩]
      ring
    _ = _ := by
      have hi : Integrable (fun p : ℝ => p) (betaMeasure a b) := hmem.integrable one_le_two
      have hs : Integrable (fun p : ℝ => p ^ 2) (betaMeasure a b) :=
        (memLp_two_iff_integrable_sq aestronglyMeasurable_id).1 hmem
      rw [integral_add (hi.const_mul n) (hs.const_mul _),
        integral_const_mul, integral_const_mul, integral_id_betaMeasure ha hb, hsecond]
      ring

/-- The variance of the real cast of a beta-binomial law, including zero trials. -/
@[simp]
theorem variance_id_map_cast_betaBinomialMeasure {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    variance id ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) =
      (n : ℝ) * (a / (a + b)) * (1 - a / (a + b)) *
        (a + b + n) / (a + b + 1) := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  have hmem : MemLp id 2 ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_map_cast_betaBinomialMeasure _ n a b)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_id_map_cast_betaBinomialMeasure ha hb,
    integral_id_map_cast_betaBinomialMeasure ha hb]
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hab1 : a + b + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The expectation of a natural-valued beta-binomial random variable, after real casting. -/
theorem integral_of_hasLaw_betaBinomialMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℕ} {a b : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hX : HasLaw X (betaBinomialMeasure n a b) P) :
    ∫ ω, (X ω : ℝ) ∂P = (n : ℝ) * a / (a + b) := by
  have hcast : HasLaw (fun ω => (X ω : ℝ))
      ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) P :=
    (hasLaw_map (by fun_prop)).comp hX
  rw [hcast.integral_eq, integral_id_map_cast_betaBinomialMeasure ha hb]

/-- The variance of a natural-valued beta-binomial random variable, after real casting. -/
theorem variance_of_hasLaw_betaBinomialMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℕ} {a b : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hX : HasLaw X (betaBinomialMeasure n a b) P) :
    variance (fun ω => (X ω : ℝ)) P =
      (n : ℝ) * (a / (a + b)) * (1 - a / (a + b)) *
        (a + b + n) / (a + b + 1) := by
  have hcast : HasLaw (fun ω => (X ω : ℝ))
      ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) P :=
    (hasLaw_map (by fun_prop)).comp hX
  rw [hcast.variance_eq, variance_id_map_cast_betaBinomialMeasure ha hb]

end TauCeti.Probability
