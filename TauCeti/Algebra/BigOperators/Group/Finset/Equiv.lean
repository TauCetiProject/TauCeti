/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Reindexing iterated products along equivalences

`Fintype.prod_equiv` reindexes a product over a finite type along an equivalence. This file
iterates it: an iterated product `∏ x, ∏ y, f x y`, whose inner index type may depend on the outer
index, is unchanged when the outer index is reindexed along `e` and each inner index type `Y x`
along an equivalence with `Y' (e x)` (`Fintype.prod_equiv₂`); likewise for a four-fold product
whose three inner index types depend on the outermost index (`Fintype.prod_equiv₄`). Additively,
`Fintype.sum_equiv₂` and `Fintype.sum_equiv₄`.
-/

public section

namespace Fintype

variable {M : Type*} [CommMonoid M]

/-- An iterated product, the inner index type depending on the outer index, is invariant under
reindexing both indices. -/
@[to_additive /-- An iterated sum, the inner index type depending on the outer index, is
invariant under reindexing both indices. -/]
theorem prod_equiv₂ {X X' : Type*} {Y : X → Type*} {Y' : X' → Type*} [Fintype X] [Fintype X']
    [∀ x, Fintype (Y x)] [∀ x, Fintype (Y' x)] (eX : X ≃ X') (eY : ∀ x, Y x ≃ Y' (eX x))
    {f : ∀ x, Y x → M} {g : ∀ x, Y' x → M} (h : ∀ x y, f x y = g (eX x) (eY x y)) :
    ∏ x, ∏ y, f x y = ∏ x, ∏ y, g x y :=
  prod_equiv eX _ _ fun x ↦ prod_equiv (eY x) _ _ (h x)

/-- A four-fold iterated product, the three inner index types depending on the outermost index,
is invariant under reindexing all four indices. -/
@[to_additive /-- A four-fold iterated sum, the three inner index types depending on the
outermost index, is invariant under reindexing all four indices. -/]
theorem prod_equiv₄ {α α' : Type*} [Fintype α] [Fintype α'] {X Y Z : α → Type*}
    {X' Y' Z' : α' → Type*} [∀ t, Fintype (X t)] [∀ t, Fintype (Y t)] [∀ t, Fintype (Z t)]
    [∀ t, Fintype (X' t)] [∀ t, Fintype (Y' t)] [∀ t, Fintype (Z' t)] (e : α ≃ α')
    (eX : ∀ t, X t ≃ X' (e t)) (eY : ∀ t, Y t ≃ Y' (e t)) (eZ : ∀ t, Z t ≃ Z' (e t))
    {f : ∀ t, X t → Y t → Z t → M} {g : ∀ t, X' t → Y' t → Z' t → M}
    (h : ∀ t x y z, f t x y z = g (e t) (eX t x) (eY t y) (eZ t z)) :
    ∏ t, ∏ x, ∏ y, ∏ z, f t x y z = ∏ t, ∏ x, ∏ y, ∏ z, g t x y z :=
  prod_equiv₂ e eX fun t x ↦ prod_equiv₂ (eY t) (fun _ ↦ eZ t) (h t x)

end Fintype
