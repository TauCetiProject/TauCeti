/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Real

/-!
# Rational numbers of bounded denominator in a bounded set

A bounded set of real numbers contains only finitely many rational numbers whose denominator is
at most a given bound `N`: such a rational `r` is determined by the pair `(r.num, r.den)`, and
both coordinates are bounded. This is the finiteness behind the fact that infinitely many rational
approximations to a real number must have unbounded denominators.

## Main results

* `Bornology.IsBounded.finite_setOf_rat_den_le`: for a bounded `s ⊆ ℝ` and `N : ℕ`, the rationals
  `r` with `r.den ≤ N` and `(r : ℝ) ∈ s` form a finite set.
-/

public section

namespace Bornology.IsBounded

/-- A bounded set of real numbers contains only finitely many rational numbers of denominator
at most `N`. -/
theorem finite_setOf_rat_den_le {s : Set ℝ} (hs : Bornology.IsBounded s) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ (r : ℝ) ∈ s}.Finite := by
  obtain ⟨C, hC⟩ := hs.exists_norm_le
  set M : ℤ := ⌈C * N⌉
  have hinj : Function.Injective fun r : ℚ ↦ (r.num, r.den) := fun a b hab ↦ by
    simp only [Prod.mk.injEq] at hab
    exact Rat.ext hab.1 hab.2
  refine ((Set.finite_Icc (-M) M).prod (Set.finite_Iic N)).preimage hinj.injOn |>.subset ?_
  rintro r ⟨hden, hr⟩
  have hnum : (r.num : ℝ) = r * r.den := by exact_mod_cast (Rat.mul_den_eq_num r).symm
  have habs : |(r.num : ℝ)| ≤ C * N := by
    rw [hnum, abs_mul, Nat.abs_cast]
    exact mul_le_mul (hC _ hr) (by exact_mod_cast hden) (Nat.cast_nonneg _)
      ((norm_nonneg _).trans (hC _ hr))
  have hM : (r.num : ℝ) ≤ M ∧ -(M : ℝ) ≤ r.num := by
    constructor <;> linarith [abs_le.mp habs, Int.le_ceil (C * N)]
  exact ⟨⟨by exact_mod_cast hM.2, by exact_mod_cast hM.1⟩, hden⟩

end Bornology.IsBounded
