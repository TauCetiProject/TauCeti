/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Functors on isomorphism classes

Mathlib's `CategoryTheory.isomorphismClasses` already supplies the action of functors on
isomorphism classes. Here we record its representative formula, identity and composition laws,
invariance under natural isomorphism, injectivity for full functors reflecting isomorphisms, such
as fully faithful functors or full functors out of groupoids, and surjectivity for essentially
surjective functors. These facts allow comparisons of presentations to descend to their spaces of
objects up to isomorphism.
-/

public section

universe v u

namespace CategoryTheory.Functor

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

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

/-- The identity functor induces the identity morphism on isomorphism classes. -/
@[simp]
theorem isomorphismClasses_map_id :
    isomorphismClasses.map (𝟭 C).toCatHom = 𝟙 (isomorphismClasses.obj (Cat.of C)) := by
  have hid : (𝟭 C).toCatHom = 𝟙 (Cat.of C) :=
    Cat.Hom.ext (Cat.Hom.id_toFunctor (C := Cat.of C)).symm
  rw [hid, isomorphismClasses.map_id]

/-- Composing functors composes their induced morphisms on isomorphism classes. -/
@[simp]
theorem isomorphismClasses_map_comp (F : C ⥤ D) (G : D ⥤ E) :
    isomorphismClasses.map (F ⋙ G).toCatHom =
      isomorphismClasses.map F.toCatHom ≫ isomorphismClasses.map G.toCatHom := by
  have hcomp : (F ⋙ G).toCatHom = F.toCatHom ≫ G.toCatHom :=
    Cat.Hom.ext (Cat.Hom.comp_toFunctor F.toCatHom G.toCatHom).symm
  rw [hcomp, isomorphismClasses.map_comp]

/-- Naturally isomorphic functors induce the same map on isomorphism classes. -/
theorem isomorphismClasses_map_eq_of_iso (F : C ⥤ D) {G : C ⥤ D} (e : F ≅ G) :
    isomorphismClasses.map F.toCatHom = isomorphismClasses.map G.toCatHom := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => exact Quotient.sound ⟨e.app x⟩

/-- A full functor reflecting isomorphisms, for instance a fully faithful functor, induces an
injection on isomorphism classes. -/
theorem isomorphismClasses_map_injective (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms] :
    Function.Injective (isomorphismClasses.map F.toCatHom) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      intro h
      obtain ⟨e⟩ := Quotient.exact h
      -- The preimage of `e.hom` is an isomorphism because `F` reflects isomorphisms.
      have : IsIso (F.map (F.preimage e.hom)) := by rw [F.map_preimage]; infer_instance
      have := isIso_of_reflects_iso (F.preimage e.hom) F
      exact Quotient.sound ⟨asIso (F.preimage e.hom)⟩

/-- An essentially surjective functor induces a surjection on isomorphism classes. -/
theorem isomorphismClasses_map_surjective (F : C ⥤ D) [F.EssSurj] :
    Function.Surjective (isomorphismClasses.map F.toCatHom) := by
  intro q
  induction q using Quotient.inductionOn with
  | h y =>
    exact ⟨Quotient.mk _ (F.objPreimage y),
      (F.isomorphismClasses_map_mk _).trans (Quotient.sound ⟨F.objObjPreimageIso y⟩)⟩

end CategoryTheory.Functor
