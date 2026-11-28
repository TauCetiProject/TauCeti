/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Retract

/-!
# Restriction of additive functors

Precomposition with an additive functor induces a functor on additive functor categories.
When the precomposing functor is full and every target object is a retract of an image object,
restriction reflects additivity. This lets an equivalence on ordinary functor categories
restrict to the additive functors.
-/

public section

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] [Preadditive C] {D : Type*} [Category* D] [Preadditive D]
  {E : Type*} [Category* E] [Preadditive E]

/-- Precomposition with an additive functor on the categories of additive functors. -/
-- The source and target in `additiveWhiskeringLeft_map_hom` use the object formula by reduction.
@[expose]
def additiveWhiskeringLeft (J : C ⥤ D) [J.Additive] (E : Type*) [Category* E] [Preadditive E] :
    (D ⥤+ E) ⥤ (C ⥤+ E) :=
  ObjectProperty.lift _ ((additiveFunctor D E).ι ⋙ (whiskeringLeft C D E).obj J)
    (fun F ↦ (additiveFunctor_iff (J ⋙ F.obj)).2 inferInstance)

@[simp]
theorem additiveWhiskeringLeft_obj_obj (J : C ⥤ D) [J.Additive] (F : D ⥤+ E) :
    ((J.additiveWhiskeringLeft E).obj F).obj = J ⋙ F.obj :=
  (rfl)

@[simp]
theorem additiveWhiskeringLeft_map_hom (J : C ⥤ D) [J.Additive] {F G : D ⥤+ E} (φ : F ⟶ G) :
    ((J.additiveWhiskeringLeft E).map φ).hom = whiskerLeft J φ.hom :=
  (rfl)

instance (J : C ⥤ D) [J.Additive] : (J.additiveWhiskeringLeft E).Additive :=
  inferInstanceAs (ObjectProperty.lift _ (_ ⋙ (whiskeringLeft C D E).obj J) _).Additive

/-- If every object of the target of a full additive functor `J` is a retract of some `J.obj X`,
then additivity of a functor out of the target can be tested by precomposing with `J`. -/
theorem additive_of_full_comp_of_retract (J : C ⥤ D) [J.Full] [J.Additive]
    (hJ : ∀ X, ∃ Y, Nonempty (Retract X (J.obj Y))) (G : D ⥤ E)
    [(J ⋙ G).Additive] : G.Additive where
  map_add {X Y f g} := by
    obtain ⟨X', ⟨rX⟩⟩ := hJ X
    obtain ⟨Y', ⟨rY⟩⟩ := hJ Y
    obtain ⟨f', hf⟩ := J.map_surjective (rX.r ≫ f ≫ rY.i)
    obtain ⟨g', hg⟩ := J.map_surjective (rX.r ≫ g ≫ rY.i)
    have h : G.map (rX.r ≫ (f + g) ≫ rY.i) =
        G.map (rX.r ≫ f ≫ rY.i) + G.map (rX.r ≫ g ≫ rY.i) := by
      rw [Preadditive.add_comp, Preadditive.comp_add, ← hf, ← hg, ← J.map_add]
      exact (J ⋙ G).map_add
    rw [← cancel_epi (rX.map G).r, ← cancel_mono (rY.map G).i]
    simp only [Retract.map_r, Retract.map_i, Category.assoc, Preadditive.add_comp,
      Preadditive.comp_add]
    simpa only [Functor.map_comp] using h

/-- An equivalence given by precomposition with a full additive functor restricts to the additive
functor categories if every object of its target category is a retract of an image object. -/
theorem isEquivalence_additiveWhiskeringLeft_of_retract (J : C ⥤ D) [J.Full] [J.Additive]
    (hJ : ∀ X, ∃ Y, Nonempty (Retract X (J.obj Y)))
    [((whiskeringLeft C D E).obj J).IsEquivalence] :
    (J.additiveWhiskeringLeft E).IsEquivalence := by
  let : (additiveFunctor C E).IsClosedUnderIsomorphisms :=
    ⟨fun i h ↦ by
      have := (additiveFunctor_iff _).1 h
      exact Functor.additive_of_iso i⟩
  let e := ((whiskeringLeft C D E).obj J).asEquivalence
  have h : (additiveFunctor C E).inverseImage e.functor = additiveFunctor D E := by
    ext G
    exact ⟨fun (_ : (J ⋙ G).Additive) ↦ J.additive_of_full_comp_of_retract hJ G,
      fun (_ : G.Additive) ↦ (inferInstance : (J ⋙ G).Additive)⟩
  exact (e.congrFullSubcategory h).isEquivalence_functor

end CategoryTheory.Functor
