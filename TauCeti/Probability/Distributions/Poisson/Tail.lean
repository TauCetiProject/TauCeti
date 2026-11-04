/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma
public import TauCeti.Probability.Cdf
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The cumulative masses of a Poisson law in closed form

For a rate `r : ℝ≥0` the Poisson law `Po(r)` on `ℕ` assigns to the upper tail `{k | n < k}` the
value `P(n + 1, r)` of the regularized lower incomplete gamma function `TauCeti.regularizedGamma`,
and to the complementary lower half-line the value `1 - P(n + 1, r)`.

This is the Poisson entry of the closed-form cdf and tail target of
`TauCetiRoadmap/StandardDistributions/README.md`, Layer 2. It also supplies the native
cumulative-mass formula that the Poisson family entry of Layer 4 asks for, together with the cdf
of the cast law `Po(ℝ, r)` that the same entry derives from it.

The finite-sum identity
`∑ k ≤ n, exp (-r) * r ^ k / k! = 1 - P(n + 1, r)` expresses the lower cumulative mass; its
complement is the upper-tail identity above.

Read the other way round, the resulting identity is the classical duality between a Poisson law of
rate `r` and a gamma law of integer shape: a Poisson variable of rate `r` exceeds `n` exactly as
often as the `(n + 1)`-st arrival of a unit-rate Poisson process occurs before time `r`, which is
the event `TauCeti.Probability.measureReal_Iic_gammaMeasure` measures.

## Main results

* `TauCeti.Probability.poissonMeasure_tail_eq_regularizedGamma` — the upper tail
  `Po(r) {k | n < k}` is `P(n + 1, r)`;
* `TauCeti.Probability.poissonMeasure_real_Iic` — the complementary cumulative mass
  `1 - P(n + 1, r)`;
* `TauCeti.Probability.sum_range_poissonMeasure_real_singleton` — the same identity written as the
  classical partial sum `∑ k ≤ n, exp (-r) * r ^ k / k !`;
* `TauCeti.Probability.cdf_map_cast_poissonMeasure` — the cumulative distribution function of the
  real-valued law `Po(ℝ, r)`, a step function with its jumps at the natural numbers;
* `TauCeti.Probability.measureReal_lt_of_hasLaw_poissonMeasure` and
  `TauCeti.Probability.measureReal_le_of_hasLaw_poissonMeasure` — the random-variable corollaries.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley, 2005,
  chapter 4.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal Nat

namespace TauCeti.Probability

variable {r : ℝ≥0} {n : ℕ}

/-! ### Stripping one atom at a time -/

/-- The Poisson tail above `n + 1` is the tail above `n` with the atom at `n + 1` removed, so it is
smaller by the Poisson mass `exp (-r) * r ^ (n + 1) / (n + 1)!` of that atom. -/
theorem poissonMeasure_real_tail_succ (r : ℝ≥0) (n : ℕ) :
    Po(r).real {k | n + 1 < k} =
      Po(r).real {k | n < k} - exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1)! := by
  have hsplit : ({n + 1} : Set ℕ) ∪ {k | n + 1 < k} = {k | n < k} := by
    ext k
    simp only [mem_union, mem_singleton_iff, mem_ofPred_eq]
    omega
  have hdisj : Disjoint ({n + 1} : Set ℕ) {k | n + 1 < k} := by
    rw [Set.disjoint_left]
    intro k hk hk'
    rw [mem_singleton_iff] at hk
    rw [mem_ofPred_eq] at hk'
    omega
  have hunion := measureReal_union (μ := Po(r)) hdisj .of_discrete
  rw [hsplit, poissonMeasure_real_singleton] at hunion
  rw [hunion]
  ring

/-- A Poisson law of rate `r` puts mass `1 - exp (-r)` on the positive integers: only the atom at
`0` is left out. -/
theorem poissonMeasure_real_tail_zero (r : ℝ≥0) :
    Po(r).real {k | 0 < k} = 1 - exp (-(r : ℝ)) := by
  have hcompl : {k : ℕ | 0 < k} = ({0} : Set ℕ)ᶜ := by
    ext k
    simp only [mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
    omega
  rw [hcompl, probReal_compl_eq_one_sub .of_discrete, poissonMeasure_real_singleton]
  simp

/-! ### The closed form -/

/-- **The Poisson tail in closed form.** For a rate `r : ℝ≥0` and `n : ℕ`, the mass a Poisson law
assigns to `{k | n < k}` is the value `P(n + 1, r)` of the regularized lower incomplete gamma
function. -/
@[simp]
theorem poissonMeasure_tail_eq_regularizedGamma (r : ℝ≥0) (n : ℕ) :
    Po(r).real {k | n < k} = regularizedGamma (n + 1) (r : ℝ) := by
  have hr : (0 : ℝ) ≤ r := r.coe_nonneg
  have hcompl : {k : ℕ | n < k} = (Iic n : Set ℕ)ᶜ := by
    ext k
    simp
  have hIic : (Iic n : Set ℕ) = ↑(Finset.range (n + 1)) := by
    ext k
    simp
  rw [hcompl, probReal_compl_eq_one_sub .of_discrete, hIic, ← sum_measureReal_singleton]
  rw [← Nat.cast_succ]
  rw [regularizedGamma_natCast (Nat.succ_ne_zero n) hr, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [poissonMeasure_real_singleton]
  ring

/-- The cumulative mass of a Poisson law, complementary to
`TauCeti.Probability.poissonMeasure_tail_eq_regularizedGamma`. -/
@[simp]
theorem poissonMeasure_real_Iic (r : ℝ≥0) (n : ℕ) :
    Po(r).real (Iic n) = 1 - regularizedGamma (n + 1) (r : ℝ) := by
  have hcompl : (Iic n : Set ℕ) = {k | n < k}ᶜ := by
    ext k
    simp only [mem_Iic, mem_compl_iff, mem_ofPred_eq, not_lt]
  rw [hcompl, probReal_compl_eq_one_sub .of_discrete, poissonMeasure_tail_eq_regularizedGamma]

/-- The classical partial-sum form of `TauCeti.Probability.poissonMeasure_real_Iic`: the first
`n + 1` Poisson masses sum to `1 - P(n + 1, r)`. Expanding the summand with
`ProbabilityTheory.poissonMeasure_real_singleton` writes the left-hand side as
`∑ k ≤ n, exp (-r) * r ^ k / k !`. -/
theorem sum_range_poissonMeasure_real_singleton (r : ℝ≥0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Po(r).real {k} = 1 - regularizedGamma (n + 1) (r : ℝ) := by
  rw [← poissonMeasure_real_Iic]
  induction n with
  | zero =>
    rw [show Iic (0 : ℕ) = {0} from Iic_bot]
    simp
  | succ n ih =>
    have hsplit : (Iic (n + 1) : Set ℕ) = Iic n ∪ {n + 1} := by
      ext k
      simp only [mem_union, mem_singleton_iff, mem_Iic]
      omega
    have hdisj : Disjoint (Iic n : Set ℕ) {n + 1} := by
      rw [Set.disjoint_left]
      intro k hk hk'
      rw [mem_Iic] at hk
      rw [mem_singleton_iff] at hk'
      omega
    rw [Finset.sum_range_succ, ih, hsplit, measureReal_union hdisj .of_discrete]

/-! ### The cast law -/

/-- The cumulative distribution function of the real-valued Poisson law `Po(ℝ, r)` at a
nonnegative point: it is the step function `1 - P(⌊x⌋₊ + 1, r)`. -/
theorem cdf_map_cast_poissonMeasure (r : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    cdf Po(ℝ, r) x = 1 - regularizedGamma (⌊x⌋₊ + 1) (r : ℝ) := by
  rw [Measure.cdf_map_natCast _ hx, poissonMeasure_real_Iic]

/-- Below the origin the cumulative distribution function of `Po(ℝ, r)` vanishes: a Poisson law is
carried by the natural numbers. -/
theorem cdf_map_cast_poissonMeasure_of_neg (r : ℝ≥0) {x : ℝ} (hx : x < 0) :
    cdf Po(ℝ, r) x = 0 :=
  Measure.cdf_map_natCast_of_neg _ hx

/-! ### Random-variable corollaries -/

/-- A random variable with a Poisson law of rate `r` exceeds `n` with probability `P(n + 1, r)`. -/
theorem measureReal_lt_of_hasLaw_poissonMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} (hX : HasLaw X Po(r) P) (n : ℕ) :
    P.real {ω | n < X ω} = regularizedGamma (n + 1) (r : ℝ) := by
  rw [hX.measureReal_eq (p := fun k : ℕ => n < k) .of_discrete]
  exact poissonMeasure_tail_eq_regularizedGamma r n

/-- A random variable with a Poisson law of rate `r` is at most `n` with probability
`1 - P(n + 1, r)`. -/
theorem measureReal_le_of_hasLaw_poissonMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} (hX : HasLaw X Po(r) P) (n : ℕ) :
    P.real {ω | X ω ≤ n} = 1 - regularizedGamma (n + 1) (r : ℝ) := by
  rw [hX.measureReal_eq (p := fun k : ℕ => k ≤ n) .of_discrete, Iic_def]
  exact poissonMeasure_real_Iic r n

end TauCeti.Probability
