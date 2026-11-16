/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Order.PiLex

/-!
# Coordinate inclusions into a lexicographic product

For a family `α i` of partially ordered types with a `1`, indexed by a linear order, two elements
`Pi.mulSingle i a` and `Pi.mulSingle i b` of the lexicographic product `Lex (∀ i, α i)` differ at
the coordinate `i` only, so they compare as `a` and `b` do. In particular, for a family of partially
ordered monoids, the inclusion `a ↦ Pi.mulSingle i a` of the `i`-th factor into the lexicographic
product is an injective ordered monoid homomorphism.

## Main definitions

* `Pi.Lex.mulSingleOrderMonoidHom`, `Pi.Lex.singleOrderAddMonoidHom`: the inclusion of the `i`-th
  factor into the lexicographic product, as an ordered monoid homomorphism.

## Main results

* `Pi.toLex_mulSingle_le_toLex_mulSingle`, `Pi.toLex_mulSingle_lt_toLex_mulSingle`: two elements
  supported at the same coordinate compare lexicographically as their values there.
* `Pi.one_le_toLex_mulSingle`, `Pi.one_lt_toLex_mulSingle`, `Pi.toLex_mulSingle_le_one`,
  `Pi.toLex_mulSingle_lt_one`: comparisons with `1`.
-/

public section

namespace Pi

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι] [DecidableEq ι]

section One

variable [∀ i, One (α i)] [∀ i, PartialOrder (α i)] {i : ι} {a b : α i}

@[to_additive (attr := simp)]
theorem toLex_mulSingle_lt_toLex_mulSingle :
    toLex (mulSingle i a) < toLex (mulSingle i b) ↔ a < b := by
  refine ⟨fun ⟨j, _, hj⟩ => ?_, fun h => ⟨i, fun j hj => by simp [hj.ne], by simpa using h⟩⟩
  obtain rfl : j = i := by
    by_contra hji
    simp [hji] at hj
  simpa using hj

@[to_additive (attr := simp)]
theorem toLex_mulSingle_le_toLex_mulSingle :
    toLex (mulSingle i a) ≤ toLex (mulSingle i b) ↔ a ≤ b := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, toLex_inj, mulSingle_inj]
  exact or_congr_left toLex_mulSingle_lt_toLex_mulSingle

@[to_additive (attr := simp) toLex_single_nonneg]
theorem one_le_toLex_mulSingle : 1 ≤ toLex (mulSingle i a) ↔ 1 ≤ a := by
  simpa using toLex_mulSingle_le_toLex_mulSingle (i := i) (a := 1) (b := a)

@[to_additive (attr := simp) toLex_single_pos]
theorem one_lt_toLex_mulSingle : 1 < toLex (mulSingle i a) ↔ 1 < a := by
  simpa using toLex_mulSingle_lt_toLex_mulSingle (i := i) (a := 1) (b := a)

@[to_additive (attr := simp)]
theorem toLex_mulSingle_le_one : toLex (mulSingle i a) ≤ 1 ↔ a ≤ 1 := by
  simpa using toLex_mulSingle_le_toLex_mulSingle (i := i) (a := a) (b := 1)

@[to_additive (attr := simp)]
theorem toLex_mulSingle_lt_one : toLex (mulSingle i a) < 1 ↔ a < 1 := by
  simpa using toLex_mulSingle_lt_toLex_mulSingle (i := i) (a := a) (b := 1)

end One

namespace Lex

variable [∀ i, MulOneClass (α i)] [∀ i, PartialOrder (α i)]

variable (α) in
/-- The inclusion `a ↦ Pi.mulSingle i a` of the `i`-th factor into the lexicographic product, as
an ordered monoid homomorphism. -/
@[to_additive /-- The inclusion `a ↦ Pi.single i a` of the `i`-th factor into the lexicographic
product, as an ordered additive monoid homomorphism. -/]
def mulSingleOrderMonoidHom (i : ι) : α i →*o Lex (∀ i, α i) where
  toFun a := toLex (mulSingle i a)
  map_one' := by simp
  map_mul' a b := by simp [mulSingle_mul]
  monotone' _ _ := toLex_mulSingle_le_toLex_mulSingle.2

@[to_additive (attr := simp)]
theorem mulSingleOrderMonoidHom_apply (i : ι) (a : α i) :
    mulSingleOrderMonoidHom α i a = toLex (mulSingle i a) :=
  (rfl)

@[to_additive]
theorem mulSingleOrderMonoidHom_injective (i : ι) :
    Function.Injective (mulSingleOrderMonoidHom α i) :=
  fun _ _ h => mulSingle_injective i (toLex.injective h)

end Lex

end Pi
