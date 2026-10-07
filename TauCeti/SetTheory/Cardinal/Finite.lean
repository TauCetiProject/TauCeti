/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The cardinality of a product with finitely many nontrivial factors

Mathlib's `Nat.card_pi` computes the cardinality of a product `∀ i, X i` over a finite index type.
This file allows an arbitrary index type, provided that all factors outside a finite set `s` have
exactly one element: the product then has the cardinality of its factors over `s`. Such products
arise as restricted-product-like objects, for instance a cohomology group of a product of modules
in which only finitely many factors contribute.

## Main results

* `Nat.card_pi_eq_prod_of_card_eq_one`: `Nat.card (∀ i, X i) = ∏ i ∈ s, Nat.card (X i)` when every
  factor outside `s` has cardinality one.
-/

public section

namespace Nat

/-- The cardinality of a product over an arbitrary index type is the product of the
cardinalities of the factors over a finite set `s`, when every factor outside `s` has exactly one
element. -/
theorem card_pi_eq_prod_of_card_eq_one {ι : Type*} {X : ι → Type*} (s : Finset ι)
    (hX : ∀ i ∉ s, Nat.card (X i) = 1) :
    Nat.card (∀ i, X i) = ∏ i ∈ s, Nat.card (X i) := by
  classical
  have h (i : {i // i ∉ s}) := Nat.card_eq_one_iff_unique.mp (hX i.1 i.2)
  have (i : {i // i ∉ s}) : Subsingleton (X i) := (h i).1
  have (i : {i // i ∉ s}) : Nonempty (X i) := (h i).2
  rw [Nat.card_congr (Equiv.piEquivPiSubtypeProd (· ∈ s) X), Nat.card_prod,
    Nat.card_unique (α := ∀ i : {i // i ∉ s}, X i), mul_one, Nat.card_pi]
  exact Finset.prod_coe_sort s fun i ↦ Nat.card (X i)

end Nat
