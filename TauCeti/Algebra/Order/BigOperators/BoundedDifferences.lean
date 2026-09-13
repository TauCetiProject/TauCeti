/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Fintype.BigOperators

/-!
# Bounded differences on a finite product

A function on a finite product `ι → β`, valued in a linearly ordered additive commutative group,
has *bounded differences* with bounds `c : ι → α` when changing a single coordinate `i`, leaving
the others fixed, moves the value by at most `c i`. `TauCeti.abs_sub_le_of_bounded_differences`
telescopes that coordinatewise hypothesis into a global one: any two points of the product, however
many coordinates they differ in, have values at most `∑ i, c i` apart.

The argument changes the coordinates one at a time, using `Function.update` to interpolate between
the two points, and adds up the resulting one-coordinate bounds with the triangle inequality. It
is stated for an arbitrary finite index type and does not require the bounds to be nonnegative.

This is the combinatorial half of McDiarmid's bounded-differences inequality, proved in
`TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences`; it involves no probability and is
kept separate from it.
-/

public section

namespace TauCeti

/-- **A function with bounded differences varies by at most the sum of its coordinate bounds.**
If changing coordinate `i` moves `f` by at most `c i`, then changing every coordinate moves it by
at most `∑ i, c i`. -/
theorem abs_sub_le_of_bounded_differences {ι : Type*} [Fintype ι] {α β : Type*}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (c : ι → α) (f : (ι → β) → α)
    (hbd : ∀ (i : ι) (x x' : ι → β), (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (x x' : ι → β) : |f x - f x'| ≤ ∑ i, c i := by
  classical
  have key : ∀ (s : Finset ι) (y y' : ι → β),
      (∀ l ∉ s, y l = y' l) → |f y - f y'| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro y y' h
        have hyy : y = y' := funext fun l => h l (by simp)
        rw [hyy, sub_self, abs_zero]
        simp
    | insert i s hi ih =>
        intro y y' h
        -- Interpolate between `y` and `y'` by correcting the coordinate `i` first.
        set y'' := Function.update y i (y' i) with hy''
        have h1 : |f y - f y''| ≤ c i := by
          apply hbd i
          intro l hl
          simp [hy'', Function.update_of_ne hl]
        have h2 : |f y'' - f y'| ≤ ∑ j ∈ s, c j := by
          apply ih
          intro l hl
          by_cases hli : l = i
          · subst hli
            simp [hy'']
          · rw [hy'', Function.update_of_ne hli]
            exact h l (by simp [Finset.mem_insert, hli, hl])
        calc
          |f y - f y'| ≤ |f y - f y''| + |f y'' - f y'| := abs_sub_le _ _ _
          _ ≤ c i + ∑ j ∈ s, c j := add_le_add h1 h2
          _ = ∑ j ∈ insert i s, c j := by simp [hi]
  simpa using key Finset.univ x x' (by simp)

end TauCeti
