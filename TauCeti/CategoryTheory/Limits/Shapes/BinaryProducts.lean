/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Binary products with a terminal object

Mathlib's `CategoryTheory.Limits.prod.leftUnitor` and `CategoryTheory.Limits.prod.rightUnitor`
identify `⊤_ C ⨯ X` and `X ⨯ ⊤_ C` with `X` for the chosen terminal object `⊤_ C`. This file gives
the same identifications, natural in `X`, for an arbitrary terminal object `T`.

## Main definitions

* `CategoryTheory.Limits.IsTerminal.prodRightUnitor`: the projections `X ⨯ T ⟶ X`, as a natural
  isomorphism `(- ⨯ T) ≅ 𝟭 C`.
* `CategoryTheory.Limits.IsTerminal.prodLeftUnitor`: the projections `T ⨯ X ⟶ X`, as a natural
  isomorphism `(T ⨯ -) ≅ 𝟭 C`.
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
