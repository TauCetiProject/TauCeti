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

For a family `α i` of partially ordered monoids indexed by a linear order, the inclusion
`a ↦ Pi.mulSingle i a` of the `i`-th factor into the lexicographic product `Lex (∀ i, α i)` is
monotone: two elements of its image differ at the coordinate `i` only. It is therefore an ordered
monoid homomorphism, and it is injective.

## Main definitions

* `Pi.Lex.mulSingleOrderMonoidHom`, `Pi.Lex.singleOrderAddMonoidHom`: the inclusion of the `i`-th
  factor into the lexicographic product, as an ordered monoid homomorphism.
-/

public section

namespace Pi.Lex

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι] [∀ i, MulOneClass (α i)]
  [∀ i, PartialOrder (α i)]

/-- The inclusion `a ↦ Pi.mulSingle i a` of the `i`-th factor into the lexicographic product, as
an ordered monoid homomorphism. -/
@[to_additive /-- The inclusion `a ↦ Pi.single i a` of the `i`-th factor into the lexicographic
product, as an ordered additive monoid homomorphism. -/]
def mulSingleOrderMonoidHom (i : ι) : α i →*o Lex (∀ i, α i) where
  toFun a := toLex (Pi.mulSingle i a)
  map_one' := by simp
  map_mul' a b := by simp [Pi.mulSingle_mul]
  monotone' a b hab := by
    rcases hab.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact le_of_lt ⟨i, fun j hj => by simp [hj.ne], by simpa using hlt⟩

@[to_additive (attr := simp)]
theorem mulSingleOrderMonoidHom_apply (i : ι) (a : α i) :
    mulSingleOrderMonoidHom i a = toLex (Pi.mulSingle i a) :=
  (rfl)

@[to_additive]
theorem mulSingleOrderMonoidHom_injective (i : ι) :
    Function.Injective (mulSingleOrderMonoidHom (α := α) i) :=
  fun _ _ h => Pi.mulSingle_injective i (toLex.injective h)

end Pi.Lex
