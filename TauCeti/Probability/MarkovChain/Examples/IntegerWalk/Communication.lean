/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.Basic
public import TauCeti.Probability.MarkovChain.Period
public import TauCeti.Probability.Kernel.Reachability

/-!
# Communication and period of integer walks

For a nearest-neighbor walk with both step probabilities positive, every integer is
reachable from every other integer. More precisely, a time-`n` transition has positive
mass exactly at the binomial lattice points between `x - n` and `x + n`. These facts
allow irreducible-chain recurrence and invariant-probability results to be applied to
the integer walk.

At the deterministic parameters zero and one reachability is one-sided, and distinct
states do not communicate. The period is two when both steps are possible, and zero
at the deterministic endpoints, which have no positive return lengths. Thus none of
these integer walks is aperiodic. No recurrence classification is asserted here.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.2 and 1.6.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- With both step probabilities positive, the support of the time-`n` transition
is exactly the binomial lattice, including both endpoints. -/
theorem integerWalk_pow_apply_singleton_pos_iff {p : unitInterval}
    (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1) (n : ℕ) (x y : ℤ) :
    0 < (integerWalk p ^ n) x {y} ↔
      ∃ k : ℕ, k ≤ n ∧ y = x + 2 * (k : ℤ) - n := by
  constructor
  · intro h
    by_contra h'
    exact h.ne' (integerWalk_pow_apply_singleton_eq_zero p n x y h')
  · rintro ⟨k, hk, rfl⟩
    rw [integerWalk_pow_apply_singleton, ENNReal.ofReal_pos]
    exact mul_pos (mul_pos (by exact_mod_cast Nat.choose_pos hk) (pow_pos hp _))
      (pow_pos (sub_pos.mpr hp') _)

/-- If both steps are possible, every state is reachable from every other state. -/
theorem integerWalk_reaches {p : unitInterval} (hp : 0 < (p : ℝ))
    (hp' : (p : ℝ) < 1) (x y : ℤ) : (integerWalk p).Reaches x y := by
  rw [Kernel.reaches_def]
  by_cases hxy : x ≤ y
  · refine ⟨(y - x).toNat, (integerWalk_pow_apply_singleton_pos_iff hp hp' _ x y).2
      ⟨(y - x).toNat, le_rfl, ?_⟩⟩
    have := Int.toNat_of_nonneg (sub_nonneg.mpr hxy)
    omega
  · refine ⟨(x - y).toNat, (integerWalk_pow_apply_singleton_pos_iff hp hp' _ x y).2
      ⟨0, Nat.zero_le _, ?_⟩⟩
    have := Int.toNat_of_nonneg (by omega : 0 ≤ x - y)
    omega

/-- The deterministic left-moving walk reaches exactly the states to its left,
including its initial state. -/
-- Simplify before the endpoint kernel itself rewrites to a deterministic kernel.
@[simp↓]
theorem integerWalk_zero_reaches_iff (x y : ℤ) :
    (integerWalk 0).Reaches x y ↔ y ≤ x := by
  rw [integerWalk_zero, Kernel.reaches_deterministic]
  simp only [sub_eq_add_neg, add_right_iterate, nsmul_eq_mul, mul_neg, mul_one]
  constructor
  · rintro ⟨n, hn⟩
    omega
  · intro h
    exact ⟨(x - y).toNat, by have := Int.toNat_of_nonneg (sub_nonneg.mpr h); omega⟩

/-- The deterministic right-moving walk reaches exactly the states to its right,
including its initial state. -/
@[simp↓]
theorem integerWalk_one_reaches_iff (x y : ℤ) :
    (integerWalk 1).Reaches x y ↔ x ≤ y := by
  rw [integerWalk_one, Kernel.reaches_deterministic]
  simp only [add_right_iterate, nsmul_eq_mul, mul_one]
  constructor
  · rintro ⟨n, hn⟩
    omega
  · intro h
    exact ⟨(y - x).toNat, by have := Int.toNat_of_nonneg (sub_nonneg.mpr h); omega⟩

private lemma integerWalk_eq_endpoint_of_not {p : unitInterval}
    (hp : ¬(0 < (p : ℝ) ∧ (p : ℝ) < 1)) :
    integerWalk p = integerWalk 0 ∨ integerWalk p = integerWalk 1 := by
  have heq : p = 0 ∨ p = 1 := by
    simpa only [unitInterval.coe_pos, unitInterval.coe_lt_one,
      unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one, not_and_or,
      not_not] using hp
  exact heq.imp (congrArg integerWalk) (congrArg integerWalk)

/-- Distinct integers communicate exactly when both step probabilities are positive. -/
@[simp↓]
theorem integerWalk_communicates_iff (p : unitInterval) (x y : ℤ) :
    (integerWalk p).Communicates x y ↔ x = y ∨ 0 < (p : ℝ) ∧ (p : ℝ) < 1 := by
  by_cases hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1
  · rw [Kernel.communicates_def]
    exact iff_of_true ⟨integerWalk_reaches hp.1 hp.2 x y,
      integerWalk_reaches hp.1 hp.2 y x⟩ (Or.inr hp)
  · rw [or_iff_left hp]
    rcases integerWalk_eq_endpoint_of_not hp with h | h
    · rw [h, Kernel.communicates_def, integerWalk_zero_reaches_iff,
        integerWalk_zero_reaches_iff]
      exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
    · rw [h, Kernel.communicates_def, integerWalk_one_reaches_iff,
        integerWalk_one_reaches_iff]
      exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- The integer walk is irreducible for counting measure exactly at the
nondeterministic parameters. -/
@[simp↓]
theorem integerWalk_isIrreducible_iff (p : unitInterval) :
    Kernel.IsIrreducible Measure.count (integerWalk p) ↔
      0 < (p : ℝ) ∧ (p : ℝ) < 1 := by
  rw [Kernel.isIrreducible_count_iff_forall_communicates]
  constructor
  · intro h
    simpa using (integerWalk_communicates_iff p 0 1).1 (h 0 1)
  · intro h x y
    exact (integerWalk_communicates_iff p x y).2 (Or.inr h)

/-- At a nondeterministic parameter the positive return lengths are exactly the
positive even integers; at either deterministic endpoint there are none. -/
@[simp↓]
theorem integerWalk_returnLengths (p : unitInterval) (x : ℤ) :
    (integerWalk p).returnLengths x =
      if 0 < (p : ℝ) ∧ (p : ℝ) < 1 then {n | 0 < n ∧ Even n} else ∅ := by
  split_ifs with hp
  · ext n
    rw [Kernel.mem_returnLengths]
    simp only [Set.mem_ofPred_eq, integerWalk_pow_apply_singleton_pos_iff hp.1 hp.2]
    constructor
    · rintro ⟨hn, k, _, hk⟩
      exact ⟨hn, ⟨k, by omega⟩⟩
    · rintro ⟨hn, k, hk⟩
      exact ⟨hn, k, by omega, by omega⟩
  · rcases integerWalk_eq_endpoint_of_not hp with h | h
    · rw [h, integerWalk_zero]
      simpa only [sub_eq_add_neg] using
        Kernel.returnLengths_deterministic_add Measurable.of_discrete (by decide : (-1 : ℤ) ≠ 0) x
    · rw [h, integerWalk_one]
      exact Kernel.returnLengths_deterministic_add Measurable.of_discrete (by decide) x

/-- Every nondeterministic integer walk has period two. Deterministic drift has
period zero, using the gcd-of-the-empty-set convention. -/
@[simp↓]
theorem integerWalk_period (p : unitInterval) (x : ℤ) :
    (integerWalk p).period x = if 0 < (p : ℝ) ∧ (p : ℝ) < 1 then 2 else 0 := by
  split_ifs with hp
  · apply Nat.dvd_antisymm
    · apply Kernel.period_dvd_of_mem_returnLengths
      rw [integerWalk_returnLengths, ite_eq_left hp]
      exact ⟨by decide, ⟨1, by decide⟩⟩
    · apply Kernel.dvd_period_iff.mpr
      intro n hn
      rw [integerWalk_returnLengths, ite_eq_left hp] at hn
      exact even_iff_two_dvd.mp hn.2
  · rw [Kernel.period_eq_zero_iff, integerWalk_returnLengths, ite_eq_right hp]

end TauCeti.Probability
