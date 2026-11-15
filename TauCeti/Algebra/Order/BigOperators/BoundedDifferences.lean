/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Fintype.BigOperators

/-!
# Bounded differences on a finite product

A function on a finite product `∀ i, β i`, valued in a lattice-ordered additive commutative group
`α` (for instance a linearly ordered one such as `ℝ`), has *bounded differences* with bounds
`c : ι → α` when changing a single coordinate `i`, leaving the others fixed, moves the value by at
most `c i`. `TauCeti.abs_sub_le_of_bounded_differences` telescopes that coordinatewise hypothesis
into a global one: any two points of the product, however many coordinates they differ in, have
values at most `∑ i, c i` apart.

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
theorem abs_sub_le_of_bounded_differences {ι : Type*} [Fintype ι] {β : ι → Type*} {α : Type*}
    [AddCommGroup α] [Lattice α] [AddLeftMono α] (c : ι → α) (f : (∀ i, β i) → α)
    (hbd : ∀ (i : ι) (x x' : ∀ i, β i), (∀ l, l ≠ i → x l = x' l) → |f x - f x'| ≤ c i)
    (x x' : ∀ i, β i) : |f x - f x'| ≤ ∑ i, c i := by
  classical
  suffices key : ∀ (s : Finset ι) (y y' : ∀ i, β i),
      (∀ l ∉ s, y l = y' l) → |f y - f y'| ≤ ∑ i ∈ s, c i from key .univ x x' (by simp)
  intro s
  induction s using Finset.induction with
  | empty =>
    intro y y' h
    obtain rfl : y = y' := funext fun l => h l (Finset.notMem_empty l)
    simp
  | insert i s hi ih =>
    intro y y' h
    -- Interpolate between `y` and `y'` by correcting the coordinate `i` first.
    set y'' := Function.update y i (y' i)
    have h1 : |f y - f y''| ≤ c i := hbd i y y'' fun l hl => (Function.update_of_ne hl ..).symm
    have h2 : |f y'' - f y'| ≤ ∑ j ∈ s, c j := ih y'' y' fun l hl => by
      rcases eq_or_ne l i with rfl | hli
      · simp [y'']
      · simpa [y'', hli] using h l (by simp [hli, hl])
    rw [Finset.sum_insert hi, ← sub_add_sub_cancel (f y) (f y'')]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

end TauCeti
