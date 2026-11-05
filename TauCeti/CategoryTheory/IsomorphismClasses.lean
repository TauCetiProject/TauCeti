/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Functors on isomorphism classes

Mathlib's `CategoryTheory.isomorphismClasses` already supplies the action of functors on
isomorphism classes. Here we record its representative formula, invariance under natural
isomorphism, and injectivity for fully faithful functors. These facts allow comparisons of
presentations to descend to their spaces of objects up to isomorphism.
-/

public section

universe v u

namespace CategoryTheory.Functor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

-- The representative formula records the defining computation of Mathlib's bundled `Quot.map`.
/-- The map on isomorphism classes sends an object's class to the class of its image. -/
@[simp]
theorem isomorphismClasses_map_mk (F : C ⥤ D) (x : C) :
    @Eq (Quotient (isIsomorphicSetoid D))
      (isomorphismClasses.map F.toCatHom (Quotient.mk (isIsomorphicSetoid C) x))
      (Quotient.mk (isIsomorphicSetoid D) (F.obj x)) := (rfl)

/-- The map on isomorphism classes commutes with the quotient projections. -/
@[simp]
theorem isomorphismClasses_map_comp_mk (F : C ⥤ D) :
    (isomorphismClasses.map F.toCatHom :
      Quotient (isIsomorphicSetoid C) → Quotient (isIsomorphicSetoid D)) ∘
        Quotient.mk (isIsomorphicSetoid C) =
      Quotient.mk (isIsomorphicSetoid D) ∘ F.obj := by
  funext x
  exact F.isomorphismClasses_map_mk x

/-- Naturally isomorphic functors induce the same map on isomorphism classes. -/
theorem isomorphismClasses_map_eq_of_iso (F : C ⥤ D) {G : C ⥤ D} (e : F ≅ G) :
    isomorphismClasses.map F.toCatHom = isomorphismClasses.map G.toCatHom := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => exact Quotient.sound ⟨e.app x⟩

/-- A fully faithful functor induces an injection on isomorphism classes. -/
theorem isomorphismClasses_map_injective (F : C ⥤ D) [F.Full] [F.Faithful] :
    Function.Injective (isomorphismClasses.map F.toCatHom) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      intro h
      obtain ⟨e⟩ := Quotient.exact h
      exact Quotient.sound ⟨F.preimageIso e⟩

end CategoryTheory.Functor
