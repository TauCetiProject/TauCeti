/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Exact support of binomial laws

The binomial law on natural counts has support `Iic n` when the success probability is
strictly between zero and one. At probability zero its support is `{0}`, and at probability
one it is `{n}`. These descriptions also cover zero trials.

For a cast law, the support is the image of this finite set of counts. In particular, its real
support is a finite set of integers, rather than the interval between its extreme points.
We also characterize positive singleton masses, including both parameter boundaries.
-/

/-
The proofs use Mathlib's binomial singleton formula and the support theorem for continuous
pushforwards; no additional definition of the distribution is introduced.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-- A binomial count has positive mass exactly when it is at most the number of trials and
is compatible with deterministic success probabilities. -/
@[simp]
theorem binomial_singleton_pos_iff (n k : ℕ) (p : unitInterval) :
    0 < binomial n p {k} ↔
      k ≤ n ∧ (p ≠ 0 ∨ k = 0) ∧ (p ≠ 1 ∨ k = n) := by
  rw [binomial_singleton, ENNReal.ofReal_pos,
    (binomial_nonneg (n := n) (p := p) (k := k)).lt_iff_ne, ne_comm]
  simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, Nat.choose_eq_zero_iff,
    pow_eq_zero_iff']
  have hp0 : (p : ℝ) = 0 ↔ p = 0 := by simp
  have hp1 : 1 - (p : ℝ) = 0 ↔ p = 1 := by
    rw [sub_eq_zero, eq_comm]
    exact Set.Icc.coe_eq_one
  rw [hp0, hp1]
  grind

/-- The exact native support of the binomial law, including probabilities zero and one and
zero trials. -/
@[simp]
theorem support_binomial (n : ℕ) (p : unitInterval) :
    (binomial n p).support = if p = 0 then {0} else if p = 1 then {n} else Iic n := by
  ext k
  simp only [Measure.mem_support_iff_measure_singleton_pos, binomial_singleton_pos_iff]
  split_ifs <;> simp_all

/-- The support of a cast binomial law is the image of its finite native support.
The target may be any Borel T₁ additive monoid with one; injectivity of the cast is unnecessary. -/
@[simp]
theorem support_map_cast_binomial {R : Type*} [AddMonoidWithOne R] [TopologicalSpace R]
    [T1Space R] [MeasurableSpace R] [BorelSpace R] (n : ℕ) (p : unitInterval) :
    (Bin(R, n, p)).support =
      if p = 0 then {0} else if p = 1 then {(n : R)} else
        (Nat.cast : ℕ → R) '' Iic n := by
  have hfinite : (binomial n p).support.Finite := by
    rw [support_binomial]
    split_ifs <;> exact Set.toFinite _
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae continuous_of_discreteTopology,
    (hfinite.image _).isClosed.closure_eq, support_binomial]
  split_ifs <;> simp

end TauCeti.Probability
