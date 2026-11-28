/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.IntegralDomain
import TauCeti.Algebra.Group.Units.PowEq
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.GroupTheory.SpecificGroups.Cyclic.PowMonoidHom

/-!
# The number of solutions of `y ^ d = a` in a finite group with zero

Let `F` be a finite commutative group with zero whose units form a cyclic group, for instance a
finite field. Let `F` have `q` elements, let `d ≠ 0`, and write `d' = gcd(q - 1, d)`. A nonzero
`a ∈ F` has `d'` roots of `y ^ d = a` if `a ^ ((q - 1) / d') = 1`, and none otherwise; the
equation `y ^ d = 0` has the single root `0`. Summed over `x`, this counts the points of
`y ^ d = g(x)`:
`#{(x, y) : y ^ d = g(x)} = #{x : g(x) = 0} + d' · #{x : g(x) ^ ((q - 1) / d') = 1}`.

For a finite field `F` and `g = f` a polynomial, this reduces Stepanov's count of the points of
`y ^ d = f(x)` to the size of `{x : f(x) ^ ((q - 1) / d') = 1}`, which the auxiliary polynomial
bounds.

## Main results

* `TauCeti.natCard_pow_eq_of_ne_zero`: the number of roots of `y ^ d = a` for `a ≠ 0`.
* `TauCeti.card_filter_pow_eq_eq_card_filter_zero_add_mul`: the number of points of
  `y ^ d = g(x)`.

## Implementation notes

The roots of `y ^ d = a` with `a ≠ 0` are units (`Units.natCard_pow_eq_val`), and the unit group
`Fˣ` is cyclic of order `q - 1`. Mathlib's `IsCyclic.card_powMonoidHom_ker` gives
the `d'` elements of the kernel of the `d`-th power map, every nonempty fiber has as many
elements as the kernel (`MonoidHom.card_fiber_eq_card_ker`), and
`IsCyclic.mem_range_powMonoidHom_iff` decides which fibers are nonempty.

## References

* W. M. Schmidt, *Equations over Finite Fields: An Elementary Approach*, Lecture Notes in
  Mathematics 536, Springer (1976), Chapter I.
-/

public section

open Finset

namespace TauCeti

variable {F : Type*} [CommGroupWithZero F] [IsCyclic Fˣ]

/-- **The number of `d`-th roots of a nonzero element.** Let `F` be a finite commutative group
with zero whose units form a cyclic group, for instance a finite field. Let `F` have `q` elements,
and let `d ≠ 0`. A nonzero `a` has `gcd(q - 1, d)` roots of `y ^ d = a` if
`a ^ ((q - 1) / gcd(q - 1, d)) = 1`, and no root otherwise. -/
theorem natCard_pow_eq_of_ne_zero [Finite F] [DecidableEq F] {d : ℕ} (hd : d ≠ 0) {a : F}
    (ha : a ≠ 0) :
    Nat.card {y : F // y ^ d = a} =
      if a ^ ((Nat.card F - 1) / (Nat.card F - 1).gcd d) = 1 then (Nat.card F - 1).gcd d
      else 0 := by
  lift a to Fˣ using IsUnit.mk0 a ha
  have hunits : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hrange : a ∈ (powMonoidHom d : Fˣ →* Fˣ).range ↔
      (a : F) ^ ((Nat.card F - 1) / (Nat.card F - 1).gcd d) = 1 := by
    rw [IsCyclic.mem_range_powMonoidHom_iff, hunits, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
  rw [Units.natCard_pow_eq_val hd]
  split_ifs with h
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hrange.mpr h)
    rw [← hunits, ← IsCyclic.card_powMonoidHom_ker]
    exact MonoidHom.card_fiber_eq_card_ker _ hx
  · rw [Nat.card_eq_zero, isEmpty_subtype]
    exact Or.inl fun y hy => h (hrange.mp (MonoidHom.mem_range.mpr ⟨y, hy⟩))

/-- **The number of points of `y ^ d = g(x)`.** Let `F` be a finite commutative group with zero
whose units form a cyclic group, for instance a finite field. Let `F` have `q` elements, let
`d ≠ 0`, and write `d' = gcd(q - 1, d)`. For every function `g : F → F`, the number of pairs
`(x, y)` with `y ^ d = g(x)` is `#{x : g(x) = 0} + d' · #{x : g(x) ^ ((q - 1) / d') = 1}`. -/
theorem card_filter_pow_eq_eq_card_filter_zero_add_mul [Fintype F] [DecidableEq F] {d : ℕ}
    (hd : d ≠ 0) (g : F → F) :
    #{z : F × F | z.2 ^ d = g z.1} = #{x | g x = 0} + (Nat.card F - 1).gcd d *
      #{x | g x ^ ((Nat.card F - 1) / (Nat.card F - 1).gcd d) = 1} := by
  have hq : 0 < Nat.card F - 1 := Nat.sub_pos_of_lt Finite.one_lt_card
  have hk : (Nat.card F - 1) / (Nat.card F - 1).gcd d ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_left d hq) (Nat.gcd_pos_of_pos_left d hq)).ne'
  have hfiber (x : F) : #{y | y ^ d = g x} = (if g x = 0 then 1 else 0) + (Nat.card F - 1).gcd d *
      if g x ^ ((Nat.card F - 1) / (Nat.card F - 1).gcd d) = 1 then 1 else 0 := by
    by_cases hx : g x = 0
    · simp only [hx, zero_pow hk, zero_ne_one, ↓reduceIte, mul_zero, add_zero]
      exact card_eq_one.mpr ⟨0, by ext y; simp [pow_eq_zero_iff hd]⟩
    · rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, natCard_pow_eq_of_ne_zero hd hx]
      simp only [hx, ↓reduceIte, zero_add, mul_ite, mul_one, mul_zero]
  rw [card_filter, Fintype.sum_prod_type]
  simp_rw [← card_filter, hfiber, sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_id]

end TauCeti
