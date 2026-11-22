/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Binary products with a terminal object and base change along projections

Mathlib's `CategoryTheory.Limits.prod.leftUnitor` and `CategoryTheory.Limits.prod.rightUnitor`
identify `⊤_ C ⨯ X` and `X ⨯ ⊤_ C` with `X` for the chosen terminal object `⊤_ C`. This file gives
the same identifications, natural in `X`, for an arbitrary terminal object `T`.

It also gives `CategoryTheory.IsPullback.of_prod_snd_with_id`, the second-factor counterpart of
Mathlib's `CategoryTheory.IsPullback.of_prod_fst_with_id`, and deduces that `(X ⨯ -)` and `(- ⨯ X)`
preserve epimorphisms whenever epimorphisms in `C` are stable under base change.

## Main definitions and results

* `CategoryTheory.Limits.IsTerminal.prodRightUnitor`: the projections `X ⨯ T ⟶ X`, as a natural
  isomorphism `(- ⨯ T) ≅ 𝟭 C`.
* `CategoryTheory.Limits.IsTerminal.prodLeftUnitor`: the projections `T ⨯ X ⟶ X`, as a natural
  isomorphism `(T ⨯ -) ≅ 𝟭 C`.
* `CategoryTheory.IsPullback.of_prod_snd_with_id`: `prod.map (𝟙 X) f` is the base change of `f`
  along `prod.snd : X ⨯ B ⟶ B`.
* `CategoryTheory.Limits.preservesEpimorphisms_prod_functor_obj` and
  `CategoryTheory.Limits.preservesEpimorphisms_prod_functor_flip_obj`: `(X ⨯ -)` and `(- ⨯ X)`
  preserve epimorphisms when epimorphisms are stable under base change.
-/

public section

noncomputable section

universe v u

namespace CategoryTheory.Limits.IsTerminal

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {T : C} (hT : IsTerminal T)

/-- For a terminal object `T`, the projections `X ⨯ T ⟶ X` onto the first factor form a natural
isomorphism `(- ⨯ T) ≅ 𝟭 C`. -/
def prodRightUnitor : prod.functor.flip.obj T ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦ BinaryFan.rightUnitor hT (limit.isLimit (pair X T)))
    fun f ↦ prod.map_fst f (𝟙 T)

/-- The component of `prodRightUnitor` at `X` is the first projection `X ⨯ T ⟶ X`. -/
@[simp]
lemma prodRightUnitor_hom_app (X : C) : hT.prodRightUnitor.hom.app X = (prod.fst : X ⨯ T ⟶ X) := by
  rfl

/-- The inverse component of `prodRightUnitor` at `X` is `prod.lift (𝟙 X) (hT.from X)`. -/
@[simp]
lemma prodRightUnitor_inv_app (X : C) :
    hT.prodRightUnitor.inv.app X = (prod.lift (𝟙 X) (hT.from X) : X ⟶ X ⨯ T) := by
  apply (cancel_mono (hT.prodRightUnitor.hom.app X)).1
  rw [Iso.inv_hom_id_app, prodRightUnitor_hom_app]
  exact (prod.lift_fst (𝟙 X) (hT.from X)).symm

/-- For a terminal object `T`, the projections `T ⨯ X ⟶ X` onto the second factor form a natural
isomorphism `(T ⨯ -) ≅ 𝟭 C`. -/
def prodLeftUnitor : prod.functor.obj T ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦ BinaryFan.leftUnitor hT (limit.isLimit (pair T X)))
    fun f ↦ prod.map_snd (𝟙 T) f

/-- The component of `prodLeftUnitor` at `X` is the second projection `T ⨯ X ⟶ X`. -/
@[simp]
lemma prodLeftUnitor_hom_app (X : C) : hT.prodLeftUnitor.hom.app X = (prod.snd : T ⨯ X ⟶ X) := by
  rfl

/-- The inverse component of `prodLeftUnitor` at `X` is `prod.lift (hT.from X) (𝟙 X)`. -/
@[simp]
lemma prodLeftUnitor_inv_app (X : C) :
    hT.prodLeftUnitor.inv.app X = (prod.lift (hT.from X) (𝟙 X) : X ⟶ T ⨯ X) := by
  apply (cancel_mono (hT.prodLeftUnitor.hom.app X)).1
  rw [Iso.inv_hom_id_app, prodLeftUnitor_hom_app]
  exact (prod.lift_snd (hT.from X) (𝟙 X)).symm

end CategoryTheory.Limits.IsTerminal

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-- For any object `X` and morphism `f : A ⟶ B`, `prod.map (𝟙 X) f : X ⨯ A ⟶ X ⨯ B` is the base
change of `f` along `prod.snd : X ⨯ B ⟶ B`. This is the second-factor counterpart of
`CategoryTheory.IsPullback.of_prod_fst_with_id`. -/
lemma IsPullback.of_prod_snd_with_id {A B : C} (X : C) (f : A ⟶ B) [HasBinaryProduct X A]
    [HasBinaryProduct X B] :
    IsPullback prod.snd (prod.map (𝟙 X) f) f prod.snd where
  isLimit' := ⟨PullbackCone.isLimitAux' _ fun s ↦
    ⟨prod.lift (s.snd ≫ prod.fst) s.fst, by simp, by ext <;> simp [PullbackCone.condition],
      fun {m} h₁ h₂ ↦ by
        dsimp at m h₁ h₂ ⊢
        ext
        · simp [← h₂]
        · simpa using h₁⟩⟩

namespace Limits

/-- In a category with binary products whose epimorphisms are stable under base change, taking the
binary product `X ⨯ -` on the left preserves epimorphisms. -/
instance preservesEpimorphisms_prod_functor_obj [HasBinaryProducts C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] (X : C) :
    (prod.functor.obj X).PreservesEpimorphisms where
  preserves f _ := MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
    (IsPullback.of_prod_snd_with_id X f) ‹_›

/-- In a category with binary products whose epimorphisms are stable under base change, taking the
binary product `- ⨯ X` on the right preserves epimorphisms. -/
instance preservesEpimorphisms_prod_functor_flip_obj [HasBinaryProducts C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] (X : C) :
    (prod.functor.flip.obj X).PreservesEpimorphisms where
  preserves f _ := MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
    (IsPullback.of_prod_fst_with_id f X) ‹_›

end Limits

end CategoryTheory
