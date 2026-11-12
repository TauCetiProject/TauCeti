/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Additive generators

An object `G` of a preadditive category with finite biproducts is an **additive generator** if
`add G = C`: every object is a direct summand of a finite biproduct `Gⁿ` of copies of `G`, that is,
lies in the additive closure `TauCeti.additiveClosure G`. In the category `mod A` of finitely
generated modules over an Artin algebra, an additive generator exists exactly when `A` is
representation-finite; its endomorphism ring is the Auslander algebra of `A`.

Additive generators are invariant under isomorphism and under adding direct summands, and an
equivalence of categories carries them to additive generators. In a Krull-Schmidt category they
are described through indecomposable objects, in
`TauCeti.CategoryTheory.Preadditive.KrullSchmidt.AdditiveGenerator`.

## Main definitions

* `TauCeti.IsAdditiveGenerator`: `add G = C`, every object is a direct summand of some `Gⁿ`.

## Main results

* `TauCeti.isAdditiveGenerator_def`, `TauCeti.isAdditiveGenerator_iff` and
  `TauCeti.additiveClosure_eq_top_iff`: the definition, unfolded, and as `add G = ⊤`.
* `CategoryTheory.Retract.isAdditiveGenerator` and `TauCeti.IsAdditiveGenerator.of_iso`: invariance
  under adding direct summands and under isomorphism.
* `CategoryTheory.Equivalence.isAdditiveGenerator_functor_obj_iff`: invariance under equivalence of
  categories.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- An object `G` is an **additive generator** if `add G = C`: every object is a direct summand of
a finite biproduct of copies of `G`. -/
def IsAdditiveGenerator (G : C) : Prop :=
  ∀ X : C, additiveClosure G X

/-- The definition of an additive generator: every object lies in `add G`. -/
theorem isAdditiveGenerator_def {G : C} : IsAdditiveGenerator G ↔ ∀ X : C, additiveClosure G X :=
  Iff.rfl

/-- The unfolded definition of an additive generator: every object is a retract of some `Gⁿ`. -/
theorem isAdditiveGenerator_iff {G : C} :
    IsAdditiveGenerator G ↔ ∀ X : C, ∃ n : ℕ, Nonempty (Retract X (⨁ fun _ : Fin n ↦ G)) :=
  forall_congr' fun _ ↦ additiveClosure_iff

/-- An object is an additive generator exactly when its additive closure is everything. -/
theorem additiveClosure_eq_top_iff {G : C} : additiveClosure G = ⊤ ↔ IsAdditiveGenerator G :=
  ⟨fun h _ ↦ h ▸ trivial, fun h ↦ top_le_iff.1 fun X _ ↦ h X⟩

namespace IsAdditiveGenerator

variable {G G' : C}

/-- Every object lies in the additive closure of an additive generator. -/
theorem additiveClosure (hG : IsAdditiveGenerator G) (X : C) : TauCeti.additiveClosure G X :=
  hG X

/-- The additive closure of an additive generator is everything. -/
theorem additiveClosure_eq_top (hG : IsAdditiveGenerator G) : TauCeti.additiveClosure G = ⊤ :=
  additiveClosure_eq_top_iff.2 hG

end IsAdditiveGenerator

/-- **An object having an additive generator as a direct summand is an additive generator.** -/
theorem _root_.CategoryTheory.Retract.isAdditiveGenerator {G G' : C} (h : Retract G G')
    (hG : IsAdditiveGenerator G) : IsAdditiveGenerator G' :=
  fun X ↦ additiveClosure_le_iff.2
    ((additiveClosure G').prop_of_retract h (additiveClosure_self G')) X (hG X)

namespace IsAdditiveGenerator

variable {G G' : C}

/-- **Additive generators are invariant under isomorphism.** -/
theorem of_iso (hG : IsAdditiveGenerator G) (e : G ≅ G') : IsAdditiveGenerator G' :=
  (Retract.ofIso e).isAdditiveGenerator hG

/-- Adding a direct summand to an additive generator gives an additive generator. -/
theorem biprod_left (hG : IsAdditiveGenerator G) : IsAdditiveGenerator (G ⊞ G') :=
  Retract.isAdditiveGenerator ⟨biprod.inl, biprod.fst, by simp⟩ hG

/-- Adding a direct summand to an additive generator gives an additive generator. -/
theorem biprod_right (hG : IsAdditiveGenerator G) : IsAdditiveGenerator (G' ⊞ G) :=
  Retract.isAdditiveGenerator ⟨biprod.inr, biprod.snd, by simp⟩ hG

end IsAdditiveGenerator

end TauCeti

namespace CategoryTheory.Equivalence

open Limits TauCeti

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type*} [Category* D] [Preadditive D] [HasFiniteBiproducts D]

/-- An equivalence of categories carries an additive generator to an additive generator. -/
theorem isAdditiveGenerator_functor_obj (e : C ≌ D) {G : C} (hG : IsAdditiveGenerator G) :
    IsAdditiveGenerator (e.functor.obj G) :=
  fun Y ↦ (additiveClosure _).prop_of_iso (e.counitIso.app Y)
    (additiveClosure_le_inverseImage e.functor G _ (hG _))

/-- **Additive generators are invariant under equivalence of categories.** -/
@[simp]
theorem isAdditiveGenerator_functor_obj_iff (e : C ≌ D) (G : C) :
    IsAdditiveGenerator (e.functor.obj G) ↔ IsAdditiveGenerator G :=
  ⟨fun hG ↦ (e.symm.isAdditiveGenerator_functor_obj hG).of_iso (e.unitIso.app G).symm,
    e.isAdditiveGenerator_functor_obj⟩

/-- Additive generators are invariant under the inverse of an equivalence of categories. -/
@[simp]
theorem isAdditiveGenerator_inverse_obj_iff (e : C ≌ D) (G : D) :
    IsAdditiveGenerator (e.inverse.obj G) ↔ IsAdditiveGenerator G :=
  e.symm.isAdditiveGenerator_functor_obj_iff G

end CategoryTheory.Equivalence
