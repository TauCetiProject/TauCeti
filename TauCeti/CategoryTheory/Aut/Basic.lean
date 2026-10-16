/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# Automorphisms in a category

This file contains general bookkeeping lemmas for automorphisms of objects in a category.

## Main results

* `TauCeti.CategoryTheory.comp_aut_pow_hom_of_comp`: iterating an automorphism that reindexes a
  family of morphisms reindexes that family by the corresponding function iterate.
* `TauCeti.CategoryTheory.autMulEquivOfIso_hom`: the forward component of an automorphism
  transported along an isomorphism.
-/

public section

namespace TauCeti.CategoryTheory

open _root_.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {iota : Type*}

/-- The forward component of an automorphism transported along an isomorphism is the conjugate of
its forward component. -/
@[simp]
theorem autMulEquivOfIso_hom (h : X ≅ Y) (a : Aut X) :
    (Aut.autMulEquivOfIso h a).asIso.hom = h.inv ≫ a.asIso.hom ≫ h.hom :=
  rfl

/-- Iterating an automorphism which reindexes a family of morphisms reindexes that family by the
corresponding function iterate. -/
theorem comp_aut_pow_hom_of_comp (gamma : Aut X) (F : iota → (Y ⟶ X)) (s : iota → iota)
    (h : ∀ i, F i ≫ gamma.asIso.hom = F (s i)) (m : ℕ) (i : iota) :
    F i ≫ (gamma ^ m).asIso.hom = F ((s^[m]) i) := by
  induction m generalizing i with
  | zero =>
      rw [pow_zero, Function.iterate_zero_apply]
      rw [Aut.one_asIso, Iso.refl_hom, Category.comp_id]
  | succ m ih =>
      rw [pow_succ]
      rw [Aut.mul_asIso, Iso.trans_hom, ← Category.assoc, h, ih, Function.iterate_succ_apply]

end TauCeti.CategoryTheory
