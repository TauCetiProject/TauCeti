/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.RigidSignature.Basic

/-!
# Uniqueness for the free rigid monoidal category on a rigid signature

This file proves the uniqueness half of the universal property of `RigidSignature.FreeRigid S`:
strong monoidal functors out of `S.FreeRigid` into an arbitrary monoidal category `D` (not
required to be rigid) are determined up to unique monoidal natural isomorphism by their action on
the generating objects and coupons.

Because a strong monoidal functor carries every exact pairing in `S.FreeRigid` to an exact
pairing in `D`, and duals are unique up to unique isomorphism, any family of isomorphisms
`e : ∀ a, F.obj (of a) ≅ G.obj (of a)` at the generating objects extends canonically to all
formal rigid objects (`FreeRigid.wordIso`). When `e` is compatible with every coupon, these
components assemble into a monoidal natural isomorphism `FreeRigid.monoidalNatIso`. Moreover,
any two monoidal natural transformations between strong monoidal functors out of `S.FreeRigid`
that agree on the generating objects are equal (`FreeRigid.natTrans_ext`).

## Main definitions and results

* `TauCeti.RigidSignature.FreeRigid.natTrans_ext`: monoidal natural transformations between
  strong monoidal functors out of `S.FreeRigid` into any monoidal category are determined by
  their components at the generating objects.
* `TauCeti.RigidSignature.FreeRigid.wordIso`: canonical extension of generating-object
  isomorphisms `e` to all objects of `S.FreeRigid`.
* `TauCeti.RigidSignature.FreeRigid.map_comp_wordIso_hom`,
  `TauCeti.RigidSignature.FreeRigid.monoidalNatIso`,
  `TauCeti.RigidSignature.FreeRigid.wordIso_app_of_isMonoidal`, and
  `TauCeti.RigidSignature.FreeRigid.map_coupon_comp_wordIso_hom_of_isMonoidal`: naturality of
  `wordIso` whenever it respects the coupons, assembling into a monoidal natural isomorphism
  `F ≅ G`, and conversely recovering `wordIso` and coupon compatibility from any monoidal natural
  isomorphism.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
* A. Joyal and R. Street, *Planar diagrams and tensor algebra* (1988), §2.
* P. Selinger, *A survey of graphical languages for monoidal categories*, Lecture Notes in Physics
  813 (2011), §4.1.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.RigidSignature.FreeRigid

variable {S : RigidSignature.{u, v}} {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation between strong monoidal functors out of the free rigid
monoidal category on `S` (into any monoidal category `D`, not required to be rigid) is determined
by its components at the generating objects. -/
theorem natTrans_ext {F G : S.FreeRigid ⥤ D} [F.Monoidal] [G.Monoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β] (h : ∀ a, α.app (of a) = β.app (of a)) :
    α = β := by
  ext ⟨X⟩
  induction X with
  | of a => exact h a
  | unit =>
    rw [← cancel_epi (ε F)]
    exact (NatTrans.IsMonoidal.unit (τ := α)).trans (NatTrans.IsMonoidal.unit (τ := β)).symm
  | tensor X Y hX hY =>
    rw [← cancel_epi (μ F ⟨X⟩ ⟨Y⟩)]
    refine (NatTrans.IsMonoidal.tensor (τ := α) ⟨X⟩ ⟨Y⟩).trans ?_
    refine Eq.trans ?_ (NatTrans.IsMonoidal.tensor (τ := β) ⟨X⟩ ⟨Y⟩).symm
    rw [hX, hY]
  | rightDual X hX =>
    let : ExactPairing (⟨X⟩ : S.FreeRigid) (⟨X.rightDual⟩ : S.FreeRigid) :=
      (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
    exact NatTrans.app_right_eq_of_exactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩ hX
  | leftDual X hX =>
    let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) (⟨X⟩ : S.FreeRigid) :=
      (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
    exact NatTrans.app_left_eq_of_exactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩ hX

variable (F G : S.FreeRigid ⥤ D) [F.Monoidal] [G.Monoidal] (e : ∀ a, F.obj (of a) ≅ G.obj (of a))

/-- The isomorphism between the images of a formal rigid object expression under two strong
monoidal functors out of `S.FreeRigid` (into any monoidal category `D`), induced by isomorphisms
`e` at the generating objects, the monoidal comparisons of `F` and `G`, and the uniqueness of
right and left duals for the image exact pairings. -/
noncomputable def wordIso : ∀ X : RigidObject S.Obj, F.obj ⟨X⟩ ≅ G.obj ⟨X⟩
  | .of a => e a
  | .unit => (Functor.Monoidal.εIso F).symm ≪≫ Functor.Monoidal.εIso G
  | .tensor X Y =>
    (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (wordIso X ⊗ᵢ wordIso Y) ≪≫
      Functor.Monoidal.μIso G ⟨X⟩ ⟨Y⟩
  | .rightDual X =>
    letI : ExactPairing (⟨X⟩ : S.FreeRigid) (⟨X.rightDual⟩ : S.FreeRigid) :=
      (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
    rightDualIso (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩)
      (@exactPairingCongrLeft D _ _ _ _ _
        (G.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩) (wordIso X))
  | .leftDual X =>
    letI : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) (⟨X⟩ : S.FreeRigid) :=
      (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
    leftDualIso (F.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩)
      (@exactPairingCongrRight D _ _ _ _ _
        (G.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩) (wordIso X))

@[simp]
theorem wordIso_of (a : S.Obj) : wordIso F G e (of a).as = e a := by rfl

@[simp]
theorem wordIso_tensorUnit_hom : (wordIso F G e (𝟙_ S.FreeRigid).as).hom = η F ≫ ε G := by rfl

@[simp]
theorem wordIso_tensorUnit_inv : (wordIso F G e (𝟙_ S.FreeRigid).as).inv = η G ≫ ε F := by rfl

@[simp]
theorem wordIso_tensor_hom (X Y : S.FreeRigid) :
    (wordIso F G e (X ⊗ Y).as).hom =
      δ F X Y ≫ ((wordIso F G e X.as).hom ⊗ₘ (wordIso F G e Y.as).hom) ≫ μ G X Y := by rfl

@[simp]
theorem wordIso_tensor_inv (X Y : S.FreeRigid) :
    (wordIso F G e (X ⊗ Y).as).inv =
      δ G X Y ≫ ((wordIso F G e X.as).inv ⊗ₘ (wordIso F G e Y.as).inv) ≫ μ F X Y := by
  rw [← Category.assoc]
  rfl

theorem wordIso_rightDual (X : RigidObject S.Obj) :
    wordIso F G e X.rightDual =
      let : ExactPairing (⟨X⟩ : S.FreeRigid) (⟨X.rightDual⟩ : S.FreeRigid) :=
        (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
      rightDualIso (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩)
        (@exactPairingCongrLeft D _ _ _ _ _
          (G.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩) (wordIso F G e X)) := by
  rfl

theorem wordIso_leftDual (X : RigidObject S.Obj) :
    wordIso F G e X.leftDual =
      let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) (⟨X⟩ : S.FreeRigid) :=
        (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
      leftDualIso (F.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩)
        (@exactPairingCongrRight D _ _ _ _ _
          (G.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩) (wordIso F G e X)) := by
  rfl

variable {F G e}

private theorem wordIso_naturality_ε_right (X : S.FreeRigid) :
    F.map (@ExactPairing.evaluation S.FreeRigid _ _ X _ (RightRigidCategory.rightDual X).exact) ≫
        (wordIso F G e (𝟙_ S.FreeRigid).as).hom =
      (wordIso F G e ((RightRigidCategory.rightDual X).rightDual ⊗ X).as).hom ≫
        G.map (@ExactPairing.evaluation S.FreeRigid _ _ X _
          (RightRigidCategory.rightDual X).exact) := by
  let : ExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid) := (RightRigidCategory.rightDual X).exact
  simpa only [wordIso_tensorUnit_hom, wordIso_tensor_hom, rightDual_eq, wordIso_rightDual] using
    Functor.map_evaluation_naturality_of_mapExactPairing
      (ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation
        (F.mapExactPairing X ⟨X.as.rightDual⟩) (G.mapExactPairing X ⟨X.as.rightDual⟩)
        (wordIso F G e X.as))

private theorem wordIso_naturality_η_right (X : S.FreeRigid) :
    F.map (@ExactPairing.coevaluation S.FreeRigid _ _ X _
          (RightRigidCategory.rightDual X).exact) ≫
        (wordIso F G e (X ⊗ (RightRigidCategory.rightDual X).rightDual).as).hom =
      (wordIso F G e (𝟙_ S.FreeRigid).as).hom ≫
        G.map (@ExactPairing.coevaluation S.FreeRigid _ _ X _
          (RightRigidCategory.rightDual X).exact) := by
  let : ExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid) := (RightRigidCategory.rightDual X).exact
  simpa only [wordIso_tensorUnit_hom, wordIso_tensor_hom, rightDual_eq, wordIso_rightDual] using
    Functor.map_coevaluation_naturality_of_mapExactPairing
      (ExactPairing.coevaluation_comp_rightDualIso_congrLeft_tensorHom
        (F.mapExactPairing X ⟨X.as.rightDual⟩) (G.mapExactPairing X ⟨X.as.rightDual⟩)
        (wordIso F G e X.as))

private theorem wordIso_naturality_ε_left (X : S.FreeRigid) :
    F.map (@ExactPairing.evaluation S.FreeRigid _ _ _ X (LeftRigidCategory.leftDual X).exact) ≫
        (wordIso F G e (𝟙_ S.FreeRigid).as).hom =
      (wordIso F G e (X ⊗ (LeftRigidCategory.leftDual X).leftDual).as).hom ≫
        G.map (@ExactPairing.evaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) := by
  let : ExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X := (LeftRigidCategory.leftDual X).exact
  simpa only [wordIso_tensorUnit_hom, wordIso_tensor_hom, leftDual_eq, wordIso_leftDual] using
    Functor.map_evaluation_naturality_of_mapExactPairing
      (ExactPairing.leftDualIso_congrRight_tensorHom_evaluation
        (F.mapExactPairing ⟨X.as.leftDual⟩ X) (G.mapExactPairing ⟨X.as.leftDual⟩ X)
        (wordIso F G e X.as))

private theorem wordIso_naturality_η_left (X : S.FreeRigid) :
    F.map (@ExactPairing.coevaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) ≫
        (wordIso F G e ((LeftRigidCategory.leftDual X).leftDual ⊗ X).as).hom =
      (wordIso F G e (𝟙_ S.FreeRigid).as).hom ≫
        G.map (@ExactPairing.coevaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) := by
  let : ExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X := (LeftRigidCategory.leftDual X).exact
  simpa only [wordIso_tensorUnit_hom, wordIso_tensor_hom, leftDual_eq, wordIso_leftDual] using
    Functor.map_coevaluation_naturality_of_mapExactPairing
      (ExactPairing.coevaluation_comp_leftDualIso_congrRight_tensorHom
        (F.mapExactPairing ⟨X.as.leftDual⟩ X) (G.mapExactPairing ⟨X.as.leftDual⟩ X)
        (wordIso F G e X.as))

/- Composites with tensors of morphisms are folded into a single tensor of composites, so that
the tensorators cancel inside each tensor factor. -/
attribute [local simp] whiskerLeft_comp_tensorHom whiskerLeft_comp_tensorHom_assoc
  whiskerRight_comp_tensorHom whiskerRight_comp_tensorHom_assoc tensorHom_comp_whiskerLeft
  tensorHom_comp_whiskerLeft_assoc tensorHom_comp_whiskerRight tensorHom_comp_whiskerRight_assoc

/-- The isomorphisms `wordIso F G e` are natural as soon as they are natural with respect to
the coupons. -/
theorem map_comp_wordIso_hom
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))
    {X Y : S.FreeRigid} (f : X ⟶ Y) :
    F.map f ≫ (wordIso F G e Y.as).hom = (wordIso F G e X.as).hom ≫ G.map f := by
  induction f using Hom.inductionOn with
  | id X => simp
  | α_hom X Y Z =>
    rw [← cancel_epi (μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z),
      ← cancel_mono (δ G X (Y ⊗ Z) ≫ G.obj X ◁ δ G Y Z)]
    simp [← Functor.OplaxMonoidal.associativity]
  | α_inv X Y Z =>
    rw [← cancel_epi (F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z)),
      ← cancel_mono (δ G (X ⊗ Y) Z ≫ δ G X Y ▷ G.obj Z)]
    simp [← Functor.OplaxMonoidal.associativity_inv]
  | l_hom X =>
    rw [← cancel_epi (ε F ▷ F.obj X ≫ μ F (𝟙_ _) X)]
    have h : ε F ▷ F.obj X ≫ ((η F ≫ ε G) ⊗ₘ (wordIso F G e X.as).hom) =
        𝟙_ D ◁ (wordIso F G e X.as).hom ≫ ε G ▷ G.obj X := by
      rw [← tensorHom_id, tensorHom_comp_tensorHom, Functor.Monoidal.ε_η_assoc,
        Category.id_comp, tensorHom_def']
    rw [Category.assoc, ← Functor.LaxMonoidal.left_unitality_assoc, ← leftUnitor_naturality,
      Category.assoc, wordIso_tensor_hom, wordIso_tensorUnit_hom, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, Category.assoc, reassoc_of% h,
      ← Functor.LaxMonoidal.left_unitality]
  | l_inv X =>
    rw [← cancel_mono (δ G (𝟙_ _) X ≫ η G ▷ G.obj X)]
    have h : ((η F ≫ ε G) ⊗ₘ (wordIso F G e X.as).hom) ≫ η G ▷ G.obj X =
        η F ▷ F.obj X ≫ 𝟙_ D ◁ (wordIso F G e X.as).hom := by
      rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.assoc, Functor.Monoidal.ε_η,
        Category.comp_id, Category.comp_id, MonoidalCategory.tensorHom_def]
    rw [Category.assoc, wordIso_tensor_hom, wordIso_tensorUnit_hom, Category.assoc,
      Category.assoc, Category.assoc, Functor.Monoidal.μ_δ_assoc, h,
      ← Functor.OplaxMonoidal.left_unitality_assoc, ← Functor.OplaxMonoidal.left_unitality,
      leftUnitor_inv_naturality]
  | ρ_hom X =>
    rw [← cancel_epi (F.obj X ◁ ε F ≫ μ F X (𝟙_ _))]
    have h : F.obj X ◁ ε F ≫ ((wordIso F G e X.as).hom ⊗ₘ (η F ≫ ε G)) =
        (wordIso F G e X.as).hom ▷ 𝟙_ D ≫ G.obj X ◁ ε G := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom, Functor.Monoidal.ε_η_assoc,
        Category.id_comp, MonoidalCategory.tensorHom_def]
    rw [Category.assoc, ← Functor.LaxMonoidal.right_unitality_assoc, ← rightUnitor_naturality,
      Category.assoc, wordIso_tensor_hom, wordIso_tensorUnit_hom, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, Category.assoc, reassoc_of% h,
      ← Functor.LaxMonoidal.right_unitality]
  | ρ_inv X =>
    rw [← cancel_mono (δ G X (𝟙_ _) ≫ G.obj X ◁ η G)]
    have h : ((wordIso F G e X.as).hom ⊗ₘ (η F ≫ ε G)) ≫ G.obj X ◁ η G =
        F.obj X ◁ η F ≫ (wordIso F G e X.as).hom ▷ 𝟙_ D := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.assoc, Functor.Monoidal.ε_η,
        Category.comp_id, Category.comp_id, tensorHom_def']
    rw [Category.assoc, wordIso_tensor_hom, wordIso_tensorUnit_hom, Category.assoc,
      Category.assoc, Category.assoc, Functor.Monoidal.μ_δ_assoc, h,
      ← Functor.OplaxMonoidal.right_unitality_assoc, ← Functor.OplaxMonoidal.right_unitality,
      rightUnitor_inv_naturality]
  | η_right X => exact wordIso_naturality_η_right X
  | ε_right X => exact wordIso_naturality_ε_right X
  | η_left X => exact wordIso_naturality_η_left X
  | ε_left X => exact wordIso_naturality_ε_left X
  | coupon g => exact he g
  | comp f g hf hg =>
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg, reassoc_of% hf]
  | whiskerLeft X f hf =>
    simp only [wordIso_tensor_hom, Functor.Monoidal.map_whiskerLeft, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerLeft_comp_tensorHom_assoc,
      tensorHom_comp_whiskerLeft_assoc, hf]
  | whiskerRight f X hf =>
    simp only [wordIso_tensor_hom, Functor.Monoidal.map_whiskerRight, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerRight_comp_tensorHom_assoc,
      tensorHom_comp_whiskerRight_assoc, hf]

/-- For a monoidal natural isomorphism `α : F ≅ G` between strong monoidal functors out of
`S.FreeRigid`, `wordIso` applied to its components at the generating objects recovers all its
components. -/
@[simp]
theorem wordIso_app_of_isMonoidal (α : F ≅ G) [α.hom.IsMonoidal] (X : RigidObject S.Obj) :
    wordIso F G (fun a ↦ α.app (of a)) X = α.app ⟨X⟩ := by
  induction X with
  | of a => rfl
  | unit =>
    ext
    change (wordIso F G (fun a ↦ α.app (of a)) (𝟙_ S.FreeRigid).as).hom =
      α.hom.app (𝟙_ S.FreeRigid)
    rw [wordIso_tensorUnit_hom, ← NatTrans.IsMonoidal.app_unit_comp_η α.hom, Category.assoc,
      Functor.Monoidal.η_ε, Category.comp_id]
  | tensor X Y ihX ihY =>
    ext
    change (wordIso F G (fun a ↦ α.app (of a)) ((⟨X⟩ : S.FreeRigid) ⊗ ⟨Y⟩).as).hom =
      α.hom.app ((⟨X⟩ : S.FreeRigid) ⊗ ⟨Y⟩)
    rw [wordIso_tensor_hom]
    simp only [congrArg Iso.hom ihX, congrArg Iso.hom ihY, Iso.app_hom,
      NatTrans.IsMonoidal.δ_comp_tensor_assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  | rightDual X ih =>
    ext
    rw [wordIso_rightDual]
    dsimp only
    rw [ih]
    let : ExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩ :=
      (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
    let : ExactPairing (G.obj ⟨X⟩) (G.obj ⟨X.rightDual⟩) :=
      G.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩
    refine ExactPairing.rightHom_ext (X := G.obj ⟨X⟩) ?_
    rw [← cancel_epi (F.obj ⟨X.rightDual⟩ ◁ α.hom.app ⟨X⟩), ← tensorHom_def'_assoc,
      ← tensorHom_def'_assoc]
    have h₁ := ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation
      (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩)
      (G.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩) (α.app ⟨X⟩)
    have h₂ := NatTrans.tensorHom_app_comp_mapExactPairing_evaluation α.hom
      (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩
    exact h₁.trans h₂.symm
  | leftDual X ih =>
    ext
    rw [wordIso_leftDual]
    dsimp only
    rw [ih]
    let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩ :=
      (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
    let : ExactPairing (G.obj ⟨X.leftDual⟩) (G.obj ⟨X⟩) :=
      G.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩
    refine ExactPairing.leftDualHom_ext (Y := G.obj ⟨X⟩) ?_
    rw [← cancel_epi (α.hom.app ⟨X⟩ ▷ F.obj ⟨X.leftDual⟩), ← tensorHom_def_assoc,
      ← tensorHom_def_assoc]
    have h₁ := ExactPairing.leftDualIso_congrRight_tensorHom_evaluation
      (F.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩)
      (G.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩) (α.app ⟨X⟩)
    have h₂ := NatTrans.tensorHom_app_comp_mapExactPairing_evaluation α.hom
      (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩
    exact h₁.trans h₂.symm

/-- The generating components of a monoidal natural isomorphism `α : F ≅ G` satisfy the coupon
compatibility condition for `wordIso`. -/
theorem map_coupon_comp_wordIso_hom_of_isMonoidal (α : F ≅ G) [α.hom.IsMonoidal]
    (g : S.Coupon) :
    F.map (coupon g) ≫ (wordIso F G (fun a ↦ α.app (of a)) (S.tgt g)).hom =
      (wordIso F G (fun a ↦ α.app (of a)) (S.src g)).hom ≫ G.map (coupon g) := by
  simp only [wordIso_app_of_isMonoidal, Iso.app_hom]
  exact α.hom.naturality (coupon g)

/-- Two strong monoidal functors out of the free rigid monoidal category on `S` (into an arbitrary
monoidal category `D`) that agree up to isomorphisms `e` on the generating objects, compatibly
with every coupon, are isomorphic by a monoidal natural isomorphism extending `e`. -/
noncomputable def monoidalNatIso
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g)) :
    F ≅ G :=
  NatIso.ofComponents (fun X ↦ wordIso F G e X.as) fun f ↦ map_comp_wordIso_hom he f

variable (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
  (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeRigid) :
    (monoidalNatIso he).hom.app X = (wordIso F G e X.as).hom := by rfl

@[simp]
theorem monoidalNatIso_inv_app (X : S.FreeRigid) :
    (monoidalNatIso he).inv.app X = (wordIso F G e X.as).inv := by rfl

instance : NatTrans.IsMonoidal (monoidalNatIso he).hom where
  unit := by
    rw [monoidalNatIso_hom_app, wordIso_tensorUnit_hom, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    rw [monoidalNatIso_hom_app, wordIso_tensor_hom, Functor.Monoidal.μ_δ_assoc,
      monoidalNatIso_hom_app, monoidalNatIso_hom_app]

end TauCeti.RigidSignature.FreeRigid
