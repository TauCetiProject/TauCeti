/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Rational numbers of bounded denominator in a bounded set

A bounded set in a normed division algebra over `ℝ` (such as `ℝ` itself, or `ℂ`) contains only
finitely many rational numbers whose denominator is at most a given bound `N`: such a rational
`r` is determined by the pair `(r.num, r.den)`, and both coordinates are bounded. This is the
finiteness behind the fact that infinitely many rational approximations to a real number must
have unbounded denominators.

## Main results

* `Bornology.IsBounded.finite_setOf_rat_den_le`: for a bounded set `s` in a normed division ring
  `K` that is a normed `ℝ`-algebra, and `N : ℕ`, the rationals `r` with `r.den ≤ N` and
  `(r : K) ∈ s` form a finite set.
-/

public section

namespace Bornology.IsBounded

/-- A bounded set in a normed division algebra over `ℝ` (for instance a bounded set of real or
complex numbers) contains only finitely many rational numbers of denominator at most `N`. -/
theorem finite_setOf_rat_den_le {K : Type*} [NormedDivisionRing K] [NormedAlgebra ℝ K]
    {s : Set K} (hs : Bornology.IsBounded s) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ (r : K) ∈ s}.Finite := by
  obtain ⟨C, hC⟩ := hs.exists_norm_le
  set M : ℤ := ⌈C * N⌉
  have hinj : Function.Injective fun r : ℚ ↦ (r.num, r.den) := fun a b hab ↦ by
    simp only [Prod.mk.injEq] at hab
    exact Rat.ext hab.1 hab.2
  refine ((Set.finite_Icc (-M) M).prod (Set.finite_Iic N)).preimage hinj.injOn |>.subset ?_
  rintro r ⟨hden, hr⟩
  have hrC : |(r : ℝ)| ≤ C := by
    rw [← Real.norm_eq_abs, ← norm_algebraMap' K, map_ratCast]
    exact hC _ hr
  have hnum : (r.num : ℝ) = r * r.den := by exact_mod_cast (Rat.mul_den_eq_num r).symm
  have habs : |(r.num : ℝ)| ≤ M := by
    rw [hnum, abs_mul, Nat.abs_cast]
    exact (mul_le_mul hrC (by exact_mod_cast hden) (Nat.cast_nonneg _)
      ((abs_nonneg _).trans hrC)).trans (Int.le_ceil _)
  have hM : |r.num| ≤ M := by exact_mod_cast habs
  exact ⟨abs_le.mp hM, hden⟩

end Bornology.IsBounded
