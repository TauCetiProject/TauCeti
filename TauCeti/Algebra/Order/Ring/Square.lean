/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Finset.Defs

/-! # Nonnegative square roots of square elements

A square in a linearly ordered ring has a nonnegative square root, by taking the absolute
value of any square root. Only compatibility of the order with addition is needed.

Since squares in a linearly ordered ring are nonnegative, `-1` is not a square there
(`TauCeti.not_isSquare_neg_one`). For the same reason a negated nonzero square `-c²` is never a
nonzero square `d²`. So if the nonzero values `c k` have pairwise distinct squares on the indices
in a set `s` and on those outside it, then `k ↦ -c k²` on `s` and `k ↦ c k²` off `s` is injective
(`TauCeti.injective_ite_neg_sq`).
-/

public section

/-- A square in a linearly ordered ring has a nonnegative square root. -/
theorem IsSquare.exists_nonneg_sq {R : Type*} [Ring R] [LinearOrder R]
    [IsOrderedAddMonoid R] {a : R} (ha : IsSquare a) : ∃ r : R, 0 ≤ r ∧ r ^ 2 = a := by
  obtain ⟨r, rfl⟩ := ha.exists_sq
  exact ⟨|r|, abs_nonneg r, sq_abs r⟩

namespace TauCeti

/-- `-1` is not a square in a nontrivial linearly ordered ring. -/
theorem not_isSquare_neg_one {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] :
    ¬IsSquare (-1 : R) :=
  fun h ↦ neg_one_lt_zero.not_ge h.nonneg

/-- If the values `c k` are nonzero and two indices that both lie in `s` or both lie outside it
have distinct squares `c k²`, then `k ↦ -c k²` on `s` and `k ↦ c k²` off `s` is injective. -/
theorem injective_ite_neg_sq {R ι : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq ι] (s : Finset ι) {c : ι → R}
    (hc : Pairwise fun k l ↦ (k ∈ s ↔ l ∈ s) → c k ^ 2 ≠ c l ^ 2) (hc0 : ∀ k, c k ≠ 0) :
    Function.Injective fun k ↦ if k ∈ s then -c k ^ 2 else c k ^ 2 := by
  intro k l e
  by_contra hkl
  have hk := sq_pos_of_ne_zero (hc0 k)
  have hl := sq_pos_of_ne_zero (hc0 l)
  have h := hc hkl
  by_cases hks : k ∈ s <;> by_cases hls : l ∈ s <;> simp only [hks, hls, ↓reduceIte] at h e
  · exact h (by simp) (neg_inj.1 e)
  · exact (neg_neg_of_pos hk).not_gt (e ▸ hl)
  · exact (neg_neg_of_pos hl).not_gt (e ▸ hk)
  · exact h (by simp) e

end TauCeti
