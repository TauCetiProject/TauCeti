/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Maps out of the tensor unit under lax monoidal functors

A lax monoidal functor `F : V ⥤ W` sends a map `f : 𝟙_ V ⟶ v` out of the tensor unit to the map
`ε F ≫ F.map f : 𝟙_ W ⟶ F.obj v`. When this assignment is bijective for every `v`, transporting
an enrichment along `F` does not change the underlying ordinary category: this is the hypothesis
of Mathlib's `CategoryTheory.TransportEnrichment.enrichedOrdinaryCategory`.

This file records how the hypothesis is verified in practice: it is stable under composition of
lax monoidal functors, it holds for fully faithful functors with invertible unit, and it passes
from a functor to postcomposition with it on functor categories, with the pointwise monoidal
structures.
-/

public section

open CategoryTheory MonoidalCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Functor.LaxMonoidal

variable {V : Type u₁} [Category.{v₁} V] [MonoidalCategory V]
  {W : Type u₂} [Category.{v₂} W] [MonoidalCategory W]
  {U : Type u₃} [Category.{v₃} U] [MonoidalCategory U]

/-- If two lax monoidal functors induce bijections on maps out of the tensor unit, so does their
composite. -/
lemma bijective_ε_comp_map_comp (F : V ⥤ W) (G : W ⥤ U) [F.LaxMonoidal] [G.LaxMonoidal]
    (hF : ∀ v : V, Function.Bijective fun f : 𝟙_ V ⟶ v ↦ ε F ≫ F.map f)
    (hG : ∀ w : W, Function.Bijective fun f : 𝟙_ W ⟶ w ↦ ε G ≫ G.map f) (v : V) :
    Function.Bijective fun f : 𝟙_ V ⟶ v ↦ ε (F ⋙ G) ≫ (F ⋙ G).map f := by
  have h : (fun f : 𝟙_ V ⟶ v ↦ ε (F ⋙ G) ≫ (F ⋙ G).map f) =
      (fun g ↦ ε G ≫ G.map g) ∘ (fun f ↦ ε F ≫ F.map f) := by
    ext f
    simp
  rw [h]
  exact (hG (F.obj v)).comp (hF v)

/-- If a lax monoidal functor `F` induces bijections on maps out of the tensor unit, so does
postcomposition with `F` on functor categories, for the pointwise monoidal structures. -/
lemma bijective_ε_comp_map_whiskeringRight (J : Type u₄) [Category.{v₄} J] (F : V ⥤ W)
    [F.LaxMonoidal] (hF : ∀ v : V, Function.Bijective fun f : 𝟙_ V ⟶ v ↦ ε F ≫ F.map f)
    (X : J ⥤ V) :
    Function.Bijective fun f : 𝟙_ (J ⥤ V) ⟶ X ↦
      ε ((Functor.whiskeringRight J V W).obj F) ≫
        ((Functor.whiskeringRight J V W).obj F).map f := by
  refine ⟨fun f g h ↦ ?_, fun t ↦ ?_⟩
  · ext j
    exact (hF (X.obj j)).injective (congrArg (fun φ ↦ φ.app j) h)
  · choose s hs using fun j ↦ (hF (X.obj j)).surjective (t.app j)
    refine ⟨{ app := s, naturality := fun j k g ↦ (hF (X.obj k)).injective ?_ }, ?_⟩
    · have := t.naturality g
      dsimp at this hs ⊢
      rw [Category.id_comp, hs, Functor.map_comp, ← Category.assoc, hs, ← this, Category.id_comp]
    · ext j
      exact hs j

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Functor.FullyFaithful

variable {V : Type u₁} [Category.{v₁} V] [MonoidalCategory V]
  {W : Type u₂} [Category.{v₂} W] [MonoidalCategory W]

/-- A fully faithful lax monoidal functor with invertible unit induces bijections on maps out of
the tensor unit. -/
lemma bijective_ε_comp_map {F : V ⥤ W} [F.LaxMonoidal] (hF : F.FullyFaithful)
    [IsIso (LaxMonoidal.ε F)] (v : V) :
    Function.Bijective fun f : 𝟙_ V ⟶ v ↦ LaxMonoidal.ε F ≫ F.map f := by
  have hε : Function.Bijective fun g : F.obj (𝟙_ V) ⟶ F.obj v ↦ LaxMonoidal.ε F ≫ g :=
    ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun g ↦ ⟨CategoryTheory.inv (LaxMonoidal.ε F) ≫ g, by simp⟩⟩
  exact hε.comp (hF.map_bijective _ _)

end CategoryTheory.Functor.FullyFaithful
