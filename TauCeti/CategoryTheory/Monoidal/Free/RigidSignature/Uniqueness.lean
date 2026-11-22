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

* `TauCeti.RigidObject.projectObjIso` and `TauCeti.RigidSignature.FreeRigid.mapWordIso`:
  canonical transport of formal rigid objects along generator isomorphisms and comparisons between
  functor images of words and evaluations on generator images.
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

namespace TauCeti.RigidObject

section ProjectObjIso

variable {α : Type u} {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RigidCategory D]
  {f g h : α → D}

/-- The isomorphism between the evaluations of a formal rigid object expression induced by
isomorphisms `e a : f a ≅ g a` of the interpretations of its generators. -/
noncomputable def projectObjIso (e : ∀ a, f a ≅ g a) :
    ∀ X : RigidObject α, projectObj f X ≅ projectObj g X
  | .of a => e a
  | .unit => Iso.refl _
  | .tensor X Y => projectObjIso e X ⊗ᵢ projectObjIso e Y
  | .rightDual X =>
    rightDualIso (RightRigidCategory.rightDual (projectObj f X)).exact
      (@exactPairingCongrLeft D _ _ _ _ _
        (RightRigidCategory.rightDual (projectObj g X)).exact (projectObjIso e X))
  | .leftDual X =>
    leftDualIso (LeftRigidCategory.leftDual (projectObj f X)).exact
      (@exactPairingCongrRight D _ _ _ _ _
        (LeftRigidCategory.leftDual (projectObj g X)).exact (projectObjIso e X))

@[simp]
theorem projectObjIso_of (e : ∀ a, f a ≅ g a) (a : α) : projectObjIso e (.of a) = e a :=
  (rfl)

@[simp]
theorem projectObjIso_unit (e : ∀ a, f a ≅ g a) :
    projectObjIso e .unit = Iso.refl (𝟙_ D) :=
  (rfl)

@[simp]
theorem projectObjIso_tensor (e : ∀ a, f a ≅ g a) (X Y : RigidObject α) :
    projectObjIso e (X.tensor Y) = projectObjIso e X ⊗ᵢ projectObjIso e Y :=
  (rfl)

theorem projectObjIso_rightDual (e : ∀ a, f a ≅ g a) (X : RigidObject α) :
    projectObjIso e X.rightDual =
      rightDualIso (RightRigidCategory.rightDual (projectObj f X)).exact
        (@exactPairingCongrLeft D _ _ _ _ _
          (RightRigidCategory.rightDual (projectObj g X)).exact (projectObjIso e X)) :=
  (rfl)

theorem projectObjIso_leftDual (e : ∀ a, f a ≅ g a) (X : RigidObject α) :
    projectObjIso e X.leftDual =
      leftDualIso (LeftRigidCategory.leftDual (projectObj f X)).exact
        (@exactPairingCongrRight D _ _ _ _ _
          (LeftRigidCategory.leftDual (projectObj g X)).exact (projectObjIso e X)) :=
  (rfl)

@[simp]
theorem projectObjIso_refl (X : RigidObject α) :
    projectObjIso (fun a ↦ Iso.refl (f a)) X = Iso.refl (projectObj f X) := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor X Y ihX ihY =>
    dsimp only [projectObjIso, projectObj]
    rw [ihX, ihY]
    ext
    simp
  | rightDual X ih =>
    dsimp only [projectObjIso, projectObj]
    ext
    let : ExactPairing (projectObj f X) (projectObj f X.rightDual) :=
      (RightRigidCategory.rightDual (projectObj f X)).exact
    refine ExactPairing.rightHom_ext (X := projectObj f X) ?_
    have hev := ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation
      (RightRigidCategory.rightDual (projectObj f X)).exact
      (RightRigidCategory.rightDual (projectObj f X)).exact
      (projectObjIso (fun a ↦ Iso.refl (f a)) X)
    rw [ih, Iso.refl_hom, tensorHom_id] at hev
    rw [ih]
    refine hev.trans ?_
    rw [Iso.refl_hom, id_whiskerRight, Category.id_comp]
  | leftDual X ih =>
    dsimp only [projectObjIso, projectObj]
    ext
    let : ExactPairing (projectObj f X.leftDual) (projectObj f X) :=
      (LeftRigidCategory.leftDual (projectObj f X)).exact
    refine ExactPairing.leftDualHom_ext (Y := projectObj f X) ?_
    have hev := ExactPairing.leftDualIso_congrRight_tensorHom_evaluation
      (LeftRigidCategory.leftDual (projectObj f X)).exact
      (LeftRigidCategory.leftDual (projectObj f X)).exact
      (projectObjIso (fun a ↦ Iso.refl (f a)) X)
    rw [ih, Iso.refl_hom, id_tensorHom] at hev
    rw [ih]
    refine hev.trans ?_
    rw [Iso.refl_hom, MonoidalCategory.whiskerLeft_id, Category.id_comp]

@[simp]
theorem projectObjIso_trans (e : ∀ a, f a ≅ g a) (e' : ∀ a, g a ≅ h a) (X : RigidObject α) :
    projectObjIso (fun a ↦ e a ≪≫ e' a) X = projectObjIso e X ≪≫ projectObjIso e' X := by
  induction X with
  | of _ => rfl
  | unit => exact (Iso.refl_trans _).symm
  | tensor X Y ihX ihY =>
    dsimp only [projectObjIso, projectObj]
    rw [ihX, ihY]
    ext
    simp
  | rightDual X ih =>
    ext
    let pF := (RightRigidCategory.rightDual (projectObj f X)).exact
    let pG := (RightRigidCategory.rightDual (projectObj g X)).exact
    let pH := (RightRigidCategory.rightDual (projectObj h X)).exact
    let : ExactPairing (projectObj h X) (projectObj h X.rightDual) := pH
    refine ExactPairing.rightHom_ext (X := projectObj h X) ?_
    rw [← cancel_epi ((projectObj f X.rightDual) ◁ (projectObjIso (fun a ↦ e a ≪≫ e' a) X).hom),
      ← tensorHom_def'_assoc, ← tensorHom_def'_assoc]
    have h₁ : ((projectObjIso (fun a ↦ e a ≪≫ e' a) X.rightDual).hom ⊗ₘ
          (projectObjIso (fun a ↦ e a ≪≫ e' a) X).hom) ≫
        @ExactPairing.evaluation D _ _ (projectObj h X) (projectObj h X.rightDual) pH =
        @ExactPairing.evaluation D _ _ (projectObj f X) (projectObj f X.rightDual) pF :=
      ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation pF pH
        (projectObjIso (fun a ↦ e a ≪≫ e' a) X)
    have h₂ : ((projectObjIso e X.rightDual).hom ⊗ₘ (projectObjIso e X).hom) ≫
        @ExactPairing.evaluation D _ _ (projectObj g X) (projectObj g X.rightDual) pG =
        @ExactPairing.evaluation D _ _ (projectObj f X) (projectObj f X.rightDual) pF :=
      ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation pF pG (projectObjIso e X)
    have h₃ : ((projectObjIso e' X.rightDual).hom ⊗ₘ (projectObjIso e' X).hom) ≫
        @ExactPairing.evaluation D _ _ (projectObj h X) (projectObj h X.rightDual) pH =
        @ExactPairing.evaluation D _ _ (projectObj g X) (projectObj g X.rightDual) pG :=
      ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation pG pH (projectObjIso e' X)
    refine h₁.trans ?_
    rw [← h₂, ← h₃, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      ← Iso.trans_hom, ← Iso.trans_hom, ← ih]
  | leftDual X ih =>
    ext
    let pF := (LeftRigidCategory.leftDual (projectObj f X)).exact
    let pG := (LeftRigidCategory.leftDual (projectObj g X)).exact
    let pH := (LeftRigidCategory.leftDual (projectObj h X)).exact
    let : ExactPairing (projectObj h X.leftDual) (projectObj h X) := pH
    refine ExactPairing.leftDualHom_ext (Y := projectObj h X) ?_
    rw [← cancel_epi ((projectObjIso (fun a ↦ e a ≪≫ e' a) X).hom ▷ (projectObj f X.leftDual)),
      ← tensorHom_def_assoc, ← tensorHom_def_assoc]
    have h₁ : ((projectObjIso (fun a ↦ e a ≪≫ e' a) X).hom ⊗ₘ
          (projectObjIso (fun a ↦ e a ≪≫ e' a) X.leftDual).hom) ≫
        @ExactPairing.evaluation D _ _ (projectObj h X.leftDual) (projectObj h X) pH =
        @ExactPairing.evaluation D _ _ (projectObj f X.leftDual) (projectObj f X) pF :=
      ExactPairing.leftDualIso_congrRight_tensorHom_evaluation pF pH
        (projectObjIso (fun a ↦ e a ≪≫ e' a) X)
    have h₂ : ((projectObjIso e X).hom ⊗ₘ (projectObjIso e X.leftDual).hom) ≫
        @ExactPairing.evaluation D _ _ (projectObj g X.leftDual) (projectObj g X) pG =
        @ExactPairing.evaluation D _ _ (projectObj f X.leftDual) (projectObj f X) pF :=
      ExactPairing.leftDualIso_congrRight_tensorHom_evaluation pF pG (projectObjIso e X)
    have h₃ : ((projectObjIso e' X).hom ⊗ₘ (projectObjIso e' X.leftDual).hom) ≫
        @ExactPairing.evaluation D _ _ (projectObj h X.leftDual) (projectObj h X) pH =
        @ExactPairing.evaluation D _ _ (projectObj g X.leftDual) (projectObj g X) pG :=
      ExactPairing.leftDualIso_congrRight_tensorHom_evaluation pG pH (projectObjIso e' X)
    refine h₁.trans ?_
    rw [← h₂, ← h₃, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      ← Iso.trans_hom, ← ih]
    rfl

@[simp]
theorem projectObjIso_symm (e : ∀ a, f a ≅ g a) (X : RigidObject α) :
    projectObjIso (fun a ↦ (e a).symm) X = (projectObjIso e X).symm := by
  ext
  rw [← cancel_epi (projectObjIso e X).hom, Iso.symm_hom, Iso.hom_inv_id]
  have h := congrArg Iso.hom (projectObjIso_trans e (fun a ↦ (e a).symm) X)
  have hrefl : projectObjIso (fun a ↦ e a ≪≫ (e a).symm) X = Iso.refl (projectObj f X) := by
    refine Eq.trans ?_ (projectObjIso_refl X)
    exact congrArg (fun k ↦ projectObjIso k X) (funext fun a ↦ Iso.self_symm_id (e a))
  exact h.symm.trans (congrArg Iso.hom hrefl)

end ProjectObjIso

end TauCeti.RigidObject

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
  | unit => exact NatTrans.IsMonoidal.app_tensorUnit_eq
  | tensor X Y hX hY => exact NatTrans.IsMonoidal.app_tensor_eq hX hY
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
  | .unit => Functor.Monoidal.unitIso F G
  | .tensor X Y => Functor.Monoidal.tensorIso F G (wordIso X) (wordIso Y)
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

theorem wordIso_unit : wordIso F G e .unit = Functor.Monoidal.unitIso F G := (rfl)

theorem wordIso_tensor (X Y : RigidObject S.Obj) :
    wordIso F G e (X.tensor Y) =
      Functor.Monoidal.tensorIso F G (wordIso F G e X) (wordIso F G e Y) :=
  (rfl)

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
  have h := Functor.map_evaluation_naturality_of_mapExactPairing
    (ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation
      (F.mapExactPairing X ⟨X.as.rightDual⟩) (G.mapExactPairing X ⟨X.as.rightDual⟩)
      (wordIso F G e X.as))
  exact (congrArg _ (wordIso_tensorUnit_hom F G e)).trans <| h.trans <|
    congrArg (· ≫ _) (wordIso_tensor_hom F G e (RightRigidCategory.rightDual X).rightDual X).symm

private theorem wordIso_naturality_η_right (X : S.FreeRigid) :
    F.map (@ExactPairing.coevaluation S.FreeRigid _ _ X _
          (RightRigidCategory.rightDual X).exact) ≫
        (wordIso F G e (X ⊗ (RightRigidCategory.rightDual X).rightDual).as).hom =
      (wordIso F G e (𝟙_ S.FreeRigid).as).hom ≫
        G.map (@ExactPairing.coevaluation S.FreeRigid _ _ X _
          (RightRigidCategory.rightDual X).exact) := by
  let : ExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid) := (RightRigidCategory.rightDual X).exact
  have h := Functor.map_coevaluation_naturality_of_mapExactPairing
    (ExactPairing.coevaluation_comp_rightDualIso_congrLeft_tensorHom
      (F.mapExactPairing X ⟨X.as.rightDual⟩) (G.mapExactPairing X ⟨X.as.rightDual⟩)
      (wordIso F G e X.as))
  refine (congrArg _
    (wordIso_tensor_hom F G e X (RightRigidCategory.rightDual X).rightDual)).trans ?_
  exact h.trans <| congrArg (· ≫ _) (wordIso_tensorUnit_hom F G e).symm

private theorem wordIso_naturality_ε_left (X : S.FreeRigid) :
    F.map (@ExactPairing.evaluation S.FreeRigid _ _ _ X (LeftRigidCategory.leftDual X).exact) ≫
        (wordIso F G e (𝟙_ S.FreeRigid).as).hom =
      (wordIso F G e (X ⊗ (LeftRigidCategory.leftDual X).leftDual).as).hom ≫
        G.map (@ExactPairing.evaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) := by
  let : ExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X := (LeftRigidCategory.leftDual X).exact
  have h := Functor.map_evaluation_naturality_of_mapExactPairing
    (ExactPairing.leftDualIso_congrRight_tensorHom_evaluation
      (F.mapExactPairing ⟨X.as.leftDual⟩ X) (G.mapExactPairing ⟨X.as.leftDual⟩ X)
      (wordIso F G e X.as))
  exact (congrArg _ (wordIso_tensorUnit_hom F G e)).trans <| h.trans <|
    congrArg (· ≫ _) (wordIso_tensor_hom F G e X (LeftRigidCategory.leftDual X).leftDual).symm

private theorem wordIso_naturality_η_left (X : S.FreeRigid) :
    F.map (@ExactPairing.coevaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) ≫
        (wordIso F G e ((LeftRigidCategory.leftDual X).leftDual ⊗ X).as).hom =
      (wordIso F G e (𝟙_ S.FreeRigid).as).hom ≫
        G.map (@ExactPairing.coevaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) := by
  let : ExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X := (LeftRigidCategory.leftDual X).exact
  have h := Functor.map_coevaluation_naturality_of_mapExactPairing
    (ExactPairing.coevaluation_comp_leftDualIso_congrRight_tensorHom
      (F.mapExactPairing ⟨X.as.leftDual⟩ X) (G.mapExactPairing ⟨X.as.leftDual⟩ X)
      (wordIso F G e X.as))
  exact (congrArg _ (wordIso_tensor_hom F G e (LeftRigidCategory.leftDual X).leftDual X)).trans <|
    h.trans <| congrArg (· ≫ _) (wordIso_tensorUnit_hom F G e).symm

/-- The isomorphisms `wordIso F G e` are natural as soon as they are natural with respect to
the coupons. -/
theorem map_comp_wordIso_hom
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))
    {X Y : S.FreeRigid} (f : X ⟶ Y) :
    F.map f ≫ (wordIso F G e Y.as).hom = (wordIso F G e X.as).hom ≫ G.map f := by
  have hunit : (wordIso F G e (𝟙_ S.FreeRigid).as).hom = η F ≫ ε G :=
    wordIso_tensorUnit_hom F G e
  have htensor : ∀ A B : S.FreeRigid,
      (wordIso F G e (A ⊗ B).as).hom =
        δ F A B ≫ ((wordIso F G e A.as).hom ⊗ₘ (wordIso F G e B.as).hom) ≫ μ G A B :=
    wordIso_tensor_hom F G e
  induction f using Hom.inductionOn with
  | id X => simp
  | α_hom X Y Z =>
    exact Functor.Monoidal.associator_hom_naturality_of_tensor
      (e := fun Z ↦ (wordIso F G e Z.as).hom) htensor X Y Z
  | α_inv X Y Z =>
    exact Functor.Monoidal.map_iso_inv_comp_eq_of_map_iso_hom (α_ X Y Z)
      (Functor.Monoidal.associator_hom_naturality_of_tensor
        (e := fun Z ↦ (wordIso F G e Z.as).hom) htensor X Y Z)
  | l_hom X =>
    exact Functor.Monoidal.leftUnitor_hom_naturality_of_unit_tensor
      (e := fun Z ↦ (wordIso F G e Z.as).hom) hunit htensor X
  | l_inv X =>
    exact Functor.Monoidal.map_iso_inv_comp_eq_of_map_iso_hom (λ_ X)
      (Functor.Monoidal.leftUnitor_hom_naturality_of_unit_tensor
        (e := fun Z ↦ (wordIso F G e Z.as).hom) hunit htensor X)
  | ρ_hom X =>
    exact Functor.Monoidal.rightUnitor_hom_naturality_of_unit_tensor
      (e := fun Z ↦ (wordIso F G e Z.as).hom) hunit htensor X
  | ρ_inv X =>
    exact Functor.Monoidal.map_iso_inv_comp_eq_of_map_iso_hom (ρ_ X)
      (Functor.Monoidal.rightUnitor_hom_naturality_of_unit_tensor
        (e := fun Z ↦ (wordIso F G e Z.as).hom) hunit htensor X)
  | η_right X => exact wordIso_naturality_η_right X
  | ε_right X => exact wordIso_naturality_ε_right X
  | η_left X => exact wordIso_naturality_η_left X
  | ε_left X => exact wordIso_naturality_ε_left X
  | coupon g => exact he g
  | comp f g hf hg =>
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg, reassoc_of% hf]
  | whiskerLeft X f hf =>
    exact Functor.Monoidal.whiskerLeft_naturality_of_tensor
      (e := fun Z ↦ (wordIso F G e Z.as).hom) htensor X hf
  | whiskerRight f X hf =>
    exact Functor.Monoidal.whiskerRight_naturality_of_tensor
      (e := fun Z ↦ (wordIso F G e Z.as).hom) htensor X hf

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
    exact (wordIso_tensorUnit_hom F G _).trans
      (NatTrans.IsMonoidal.app_tensorUnit_eq_η_comp_ε α.hom).symm
  | tensor X Y ihX ihY =>
    ext
    refine (wordIso_tensor_hom F G _ ⟨X⟩ ⟨Y⟩).trans ?_
    rw [congrArg Iso.hom ihX, congrArg Iso.hom ihY, Iso.app_hom, Iso.app_hom]
    exact (NatTrans.IsMonoidal.app_tensor_eq_δ_comp_tensor_comp_μ α.hom ⟨X⟩ ⟨Y⟩).symm
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

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso he).hom.app (of a) = (e a).hom := by rfl

@[simp]
theorem monoidalNatIso_inv_app (X : S.FreeRigid) :
    (monoidalNatIso he).inv.app X = (wordIso F G e X.as).inv := by rfl

instance isMonoidal_monoidalNatIso_hom : NatTrans.IsMonoidal (monoidalNatIso he).hom :=
  NatTrans.IsMonoidal.of_unit_tensor _ (wordIso_tensorUnit_hom F G e) (wordIso_tensor_hom F G e)

section MapWordIso

variable [RigidCategory D]

/-- The comparison between the image of a formal rigid object expression under a strong monoidal
functor `F` out of the free rigid category and the expression evaluated on the images of the
generating objects, built from the monoidal comparisons of `F` and uniqueness of duals. -/
noncomputable def mapWordIso (F : S.FreeRigid ⥤ D) [F.Monoidal] :
    ∀ X : RigidObject S.Obj, F.obj ⟨X⟩ ≅ RigidObject.projectObj (fun a ↦ F.obj (of a)) X
  | .of _ => Iso.refl _
  | .unit => (Functor.Monoidal.εIso F).symm
  | .tensor X Y => (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (mapWordIso F X ⊗ᵢ mapWordIso F Y)
  | .rightDual X =>
    let : ExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩ :=
      (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
    rightDualIso (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩)
      (@exactPairingCongrLeft D _ _ _ _ _
        (RightRigidCategory.rightDual
          (RigidObject.projectObj (fun a ↦ F.obj (of a)) X)).exact (mapWordIso F X))
  | .leftDual X =>
    let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩ :=
      (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
    leftDualIso (F.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩)
      (@exactPairingCongrRight D _ _ _ _ _
        (LeftRigidCategory.leftDual
          (RigidObject.projectObj (fun a ↦ F.obj (of a)) X)).exact (mapWordIso F X))

section Computation

variable (F : S.FreeRigid ⥤ D) [F.Monoidal]

@[simp]
theorem mapWordIso_of (a : S.Obj) : mapWordIso F (.of a) = Iso.refl (F.obj (of a)) :=
  (rfl)

@[simp]
theorem mapWordIso_tensorUnit_hom : (mapWordIso F .unit).hom = η F :=
  (rfl)

@[simp]
theorem mapWordIso_tensor_hom (X Y : RigidObject S.Obj) :
    (mapWordIso F (X.tensor Y)).hom =
      δ F ⟨X⟩ ⟨Y⟩ ≫ ((mapWordIso F X).hom ⊗ₘ (mapWordIso F Y).hom) :=
  (rfl)

@[simp]
theorem mapWordIso_tensorUnit_inv : (mapWordIso F .unit).inv = ε F :=
  (rfl)

@[simp]
theorem mapWordIso_tensor_inv (X Y : RigidObject S.Obj) :
    (mapWordIso F (X.tensor Y)).inv =
      ((mapWordIso F X).inv ⊗ₘ (mapWordIso F Y).inv) ≫ μ F ⟨X⟩ ⟨Y⟩ :=
  (rfl)

theorem mapWordIso_rightDual (X : RigidObject S.Obj) :
    mapWordIso F X.rightDual =
      let : ExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩ :=
        (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
      rightDualIso (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩)
        (@exactPairingCongrLeft D _ _ _ _ _
          (RightRigidCategory.rightDual
            (RigidObject.projectObj (fun a ↦ F.obj (of a)) X)).exact (mapWordIso F X)) :=
  (rfl)

theorem mapWordIso_leftDual (X : RigidObject S.Obj) :
    mapWordIso F X.leftDual =
      let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩ :=
        (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
      leftDualIso (F.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩)
        (@exactPairingCongrRight D _ _ _ _ _
          (LeftRigidCategory.leftDual
            (RigidObject.projectObj (fun a ↦ F.obj (of a)) X)).exact (mapWordIso F X)) :=
  (rfl)

end Computation

/-- For the strong monoidal functor `lift fo fc`, whose monoidal and dual comparisons are
identities, the comparison `mapWordIso` is the identity. -/
@[simp]
theorem mapWordIso_lift (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon,
      RigidObject.projectObj fo (S.src g) ⟶ RigidObject.projectObj fo (S.tgt g))
    (X : RigidObject S.Obj) :
    mapWordIso (lift fo fc) X = Iso.refl (RigidObject.projectObj fo X) := by
  ext
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor X Y ihX ihY =>
    refine (mapWordIso_tensor_hom (lift fo fc) X Y).trans ?_
    rw [ihX, ihY, Iso.refl_hom, Iso.refl_hom]
    exact (Category.id_comp _).trans (id_tensorHom_id _ _)
  | rightDual X ih =>
    let : ExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩ :=
      (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
    let pF := (lift fo fc).mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩
    let pP : ExactPairing (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X)
        (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X.rightDual) :=
      (RightRigidCategory.rightDual
        (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X)).exact
    let : ExactPairing (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X)
        (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X.rightDual) := pP
    refine ExactPairing.rightHom_ext
      (X := RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X) ?_
    have hev : (rightDualIso pF (exactPairingCongrLeft (mapWordIso (lift fo fc) X))).hom ▷
        RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X ≫
        @ExactPairing.evaluation _ _ _ _ _ pP =
        @ExactPairing.evaluation _ _ _ (RigidObject.projectObj fo X)
          (RigidObject.projectObj fo X.rightDual) pF := by
      refine (congrArg (· ≫ @ExactPairing.evaluation _ _ _ _ _ pP)
        (tensorHom_id _ _).symm).trans ?_
      refine (congrArg (fun k ↦ (_ ⊗ₘ k) ≫ @ExactPairing.evaluation _ _ _ _ _ pP)
        (ih.trans (Iso.refl_hom _)).symm).trans ?_
      exact ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation pF pP
        (mapWordIso (lift fo fc) X)
    refine (congrArg (fun k ↦ k ▷
          RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X ≫
        @ExactPairing.evaluation _ _ _ _ _ pP)
      (congrArg Iso.hom (mapWordIso_rightDual (lift fo fc) X))).trans ?_
    refine hev.trans ?_
    have heq : @ExactPairing.evaluation _ _ _ (RigidObject.projectObj fo X)
        (RigidObject.projectObj fo X.rightDual) pF =
        @ExactPairing.evaluation _ _ _
          (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X)
          (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X.rightDual) pP :=
      ((lift fo fc).mapExactPairing_evaluation (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩).trans
        ((congrArg (· ≫ _ ≫ _) (lift_μ fo fc _ _)).trans
          ((congrArg (fun k ↦ _ ≫ _ ≫ k) (lift_η fo fc)).trans
            ((Category.id_comp _).trans ((Category.comp_id _).trans
              (lift_map_evaluation_right fo fc ⟨X⟩)))))
    refine heq.trans ?_
    exact (Category.id_comp _).symm.trans (congrArg (· ≫ _)
      ((id_whiskerRight _ _).symm.trans (congrArg (· ▷ _) (Iso.refl_hom _).symm)))
  | leftDual X ih =>
    let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩ :=
      (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
    let pF := (lift fo fc).mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩
    let pP : ExactPairing (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X.leftDual)
        (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X) :=
      (LeftRigidCategory.leftDual
        (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X)).exact
    let : ExactPairing (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X.leftDual)
        (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X) := pP
    refine ExactPairing.leftDualHom_ext
      (Y := RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X) ?_
    have hev : RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X ◁
        (leftDualIso pF (exactPairingCongrRight (mapWordIso (lift fo fc) X))).hom ≫
        @ExactPairing.evaluation _ _ _ _ _ pP =
        @ExactPairing.evaluation _ _ _ (RigidObject.projectObj fo X.leftDual)
          (RigidObject.projectObj fo X) pF := by
      refine (congrArg (· ≫ @ExactPairing.evaluation _ _ _ _ _ pP)
        (id_tensorHom _ _).symm).trans ?_
      refine (congrArg (fun k ↦ (k ⊗ₘ _) ≫ @ExactPairing.evaluation _ _ _ _ _ pP)
        (ih.trans (Iso.refl_hom _)).symm).trans ?_
      exact ExactPairing.leftDualIso_congrRight_tensorHom_evaluation pF pP
        (mapWordIso (lift fo fc) X)
    refine (congrArg (fun k ↦
          RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X ◁ k ≫
        @ExactPairing.evaluation _ _ _ _ _ pP)
      (congrArg Iso.hom (mapWordIso_leftDual (lift fo fc) X))).trans ?_
    refine hev.trans ?_
    have heq : @ExactPairing.evaluation _ _ _ (RigidObject.projectObj fo X.leftDual)
        (RigidObject.projectObj fo X) pF =
        @ExactPairing.evaluation _ _ _
          (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X.leftDual)
          (RigidObject.projectObj (fun a ↦ (lift fo fc).obj (of a)) X) pP :=
      ((lift fo fc).mapExactPairing_evaluation (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩).trans
        ((congrArg (· ≫ _ ≫ _) (lift_μ fo fc _ _)).trans
          ((congrArg (fun k ↦ _ ≫ _ ≫ k) (lift_η fo fc)).trans
            ((Category.id_comp _).trans ((Category.comp_id _).trans
              (lift_map_evaluation_left fo fc ⟨X⟩)))))
    refine heq.trans ?_
    exact (Category.id_comp _).symm.trans (congrArg (· ≫ _)
      ((MonoidalCategory.whiskerLeft_id _ _).symm.trans (congrArg (_ ◁ ·) (Iso.refl_hom _).symm)))

/-- The isomorphisms `wordIso F G e` between two strong monoidal functors out of the free rigid
category are the comparisons `mapWordIso` composed with the extension of `e` to formal rigid
object expressions. -/
theorem wordIso_eq_mapWordIso (F G : S.FreeRigid ⥤ D) [F.Monoidal] [G.Monoidal]
    (e : ∀ a, F.obj (of a) ≅ G.obj (of a)) (X : RigidObject S.Obj) :
    wordIso F G e X =
      mapWordIso F X ≪≫ RigidObject.projectObjIso e X ≪≫ (mapWordIso G X).symm := by
  ext
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]
  induction X with
  | of a =>
    refine (congrArg Iso.hom (wordIso_of F G e a)).trans ?_
    rw [mapWordIso_of, mapWordIso_of, RigidObject.projectObjIso_of, Iso.refl_hom, Iso.refl_inv]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  | unit =>
    rw [wordIso_unit, Functor.Monoidal.unitIso_hom, mapWordIso_tensorUnit_hom,
      mapWordIso_tensorUnit_inv, RigidObject.projectObjIso_unit, Iso.refl_hom]
    exact congrArg (η F ≫ ·) (Category.id_comp _).symm
  | tensor X Y ihX ihY =>
    rw [wordIso_tensor, Functor.Monoidal.tensorIso_hom, mapWordIso_tensor_hom,
      mapWordIso_tensor_inv, RigidObject.projectObjIso_tensor, tensorIso_hom, ihX, ihY,
      ← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    conv_lhs => simp only [Category.assoc]
    exact (Category.assoc _ _ _).symm
  | rightDual X ih =>
    let : ExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩ :=
      (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
    let pF : ExactPairing (F.obj ⟨X⟩) (F.obj ⟨X.rightDual⟩) :=
      F.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩
    let pG : ExactPairing (G.obj ⟨X⟩) (G.obj ⟨X.rightDual⟩) :=
      G.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩
    let pPF := (RightRigidCategory.rightDual
      (RigidObject.projectObj (fun a ↦ F.obj (of a)) X)).exact
    let pPG := (RightRigidCategory.rightDual
      (RigidObject.projectObj (fun a ↦ G.obj (of a)) X)).exact
    refine ExactPairing.rightHom_ext (X := G.obj ⟨X⟩) ?_
    rw [← cancel_epi (F.obj ⟨X.rightDual⟩ ◁ (wordIso F G e X).hom), ← tensorHom_def'_assoc,
      ← tensorHom_def'_assoc]
    have hw : ((wordIso F G e X.rightDual).hom ⊗ₘ (wordIso F G e X).hom) ≫
        @ExactPairing.evaluation D _ _ (G.obj ⟨X⟩) (G.obj ⟨X.rightDual⟩) pG =
        @ExactPairing.evaluation D _ _ (F.obj ⟨X⟩) (F.obj ⟨X.rightDual⟩) pF :=
      ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation pF pG (wordIso F G e X)
    have hmF : ((mapWordIso F X.rightDual).hom ⊗ₘ (mapWordIso F X).hom) ≫
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ F.obj (of a)) X)
          (RigidObject.projectObj (fun a ↦ F.obj (of a)) X.rightDual) pPF =
        @ExactPairing.evaluation D _ _ (F.obj ⟨X⟩) (F.obj ⟨X.rightDual⟩) pF :=
      ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation pF pPF (mapWordIso F X)
    have he : ((RigidObject.projectObjIso e X.rightDual).hom ⊗ₘ
          (RigidObject.projectObjIso e X).hom) ≫
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ G.obj (of a)) X)
          (RigidObject.projectObj (fun a ↦ G.obj (of a)) X.rightDual) pPG =
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ F.obj (of a)) X)
          (RigidObject.projectObj (fun a ↦ F.obj (of a)) X.rightDual) pPF :=
      ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation pPF pPG
        (RigidObject.projectObjIso e X)
    have hmG : ((mapWordIso G X.rightDual).hom ⊗ₘ (mapWordIso G X).hom) ≫
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ G.obj (of a)) X)
          (RigidObject.projectObj (fun a ↦ G.obj (of a)) X.rightDual) pPG =
        @ExactPairing.evaluation D _ _ (G.obj ⟨X⟩) (G.obj ⟨X.rightDual⟩) pG :=
      ExactPairing.rightDualIso_congrLeft_tensorHom_evaluation pG pPG (mapWordIso G X)
    have hmG' : ((mapWordIso G X.rightDual).inv ⊗ₘ (mapWordIso G X).inv) ≫
        @ExactPairing.evaluation D _ _ (G.obj ⟨X⟩) (G.obj ⟨X.rightDual⟩) pG =
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ G.obj (of a)) X)
          (RigidObject.projectObj (fun a ↦ G.obj (of a)) X.rightDual) pPG := by
      refine (congrArg (((mapWordIso G X.rightDual).inv ⊗ₘ (mapWordIso G X).inv) ≫ ·)
        hmG.symm).trans ?_
      refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _))).trans ?_
      exact (congrArg (fun k ↦ (k ⊗ₘ _) ≫ _) (Iso.inv_hom_id _)).trans
        ((congrArg (fun k ↦ (_ ⊗ₘ k) ≫ _) (Iso.inv_hom_id _)).trans
          ((congrArg (· ≫ _) (id_tensorHom_id _ _)).trans (Category.id_comp _)))
    refine hw.trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ @ExactPairing.evaluation D _ _ _ _ pG)
      (congrArg (· ⊗ₘ (wordIso F G e X).hom) rfl)).symm
    have hstep : (((mapWordIso F X.rightDual).hom ≫ (RigidObject.projectObjIso e X.rightDual).hom ≫
          (mapWordIso G X.rightDual).inv) ⊗ₘ
          ((mapWordIso F X).hom ≫ (RigidObject.projectObjIso e X).hom ≫ (mapWordIso G X).inv)) ≫
        @ExactPairing.evaluation D _ _ (G.obj ⟨X⟩) (G.obj ⟨X.rightDual⟩) pG =
        @ExactPairing.evaluation D _ _ (F.obj ⟨X⟩) (F.obj ⟨X.rightDual⟩) pF := by
      rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        ← MonoidalCategory.tensorHom_comp_tensorHom_assoc, hmG', he, hmF]
    exact hstep.symm.trans (congrArg (fun k ↦ ((_ ⊗ₘ k) ≫ _)) ih.symm)
  | leftDual X ih =>
    let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩ :=
      (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
    let pF : ExactPairing (F.obj ⟨X.leftDual⟩) (F.obj ⟨X⟩) :=
      F.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩
    let pG : ExactPairing (G.obj ⟨X.leftDual⟩) (G.obj ⟨X⟩) :=
      G.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩
    let pPF := (LeftRigidCategory.leftDual
      (RigidObject.projectObj (fun a ↦ F.obj (of a)) X)).exact
    let pPG := (LeftRigidCategory.leftDual
      (RigidObject.projectObj (fun a ↦ G.obj (of a)) X)).exact
    refine ExactPairing.leftDualHom_ext (Y := G.obj ⟨X⟩) ?_
    rw [← cancel_epi ((wordIso F G e X).hom ▷ F.obj ⟨X.leftDual⟩), ← tensorHom_def_assoc,
      ← tensorHom_def_assoc]
    have hw : ((wordIso F G e X).hom ⊗ₘ (wordIso F G e X.leftDual).hom) ≫
        @ExactPairing.evaluation D _ _ (G.obj ⟨X.leftDual⟩) (G.obj ⟨X⟩) pG =
        @ExactPairing.evaluation D _ _ (F.obj ⟨X.leftDual⟩) (F.obj ⟨X⟩) pF :=
      ExactPairing.leftDualIso_congrRight_tensorHom_evaluation pF pG (wordIso F G e X)
    have hmF : ((mapWordIso F X).hom ⊗ₘ (mapWordIso F X.leftDual).hom) ≫
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ F.obj (of a)) X.leftDual)
          (RigidObject.projectObj (fun a ↦ F.obj (of a)) X) pPF =
        @ExactPairing.evaluation D _ _ (F.obj ⟨X.leftDual⟩) (F.obj ⟨X⟩) pF :=
      ExactPairing.leftDualIso_congrRight_tensorHom_evaluation pF pPF (mapWordIso F X)
    have he : ((RigidObject.projectObjIso e X).hom ⊗ₘ
          (RigidObject.projectObjIso e X.leftDual).hom) ≫
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ G.obj (of a)) X.leftDual)
          (RigidObject.projectObj (fun a ↦ G.obj (of a)) X) pPG =
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ F.obj (of a)) X.leftDual)
          (RigidObject.projectObj (fun a ↦ F.obj (of a)) X) pPF :=
      ExactPairing.leftDualIso_congrRight_tensorHom_evaluation pPF pPG
        (RigidObject.projectObjIso e X)
    have hmG : ((mapWordIso G X).hom ⊗ₘ (mapWordIso G X.leftDual).hom) ≫
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ G.obj (of a)) X.leftDual)
          (RigidObject.projectObj (fun a ↦ G.obj (of a)) X) pPG =
        @ExactPairing.evaluation D _ _ (G.obj ⟨X.leftDual⟩) (G.obj ⟨X⟩) pG :=
      ExactPairing.leftDualIso_congrRight_tensorHom_evaluation pG pPG (mapWordIso G X)
    have hmG' : ((mapWordIso G X).inv ⊗ₘ (mapWordIso G X.leftDual).inv) ≫
        @ExactPairing.evaluation D _ _ (G.obj ⟨X.leftDual⟩) (G.obj ⟨X⟩) pG =
        @ExactPairing.evaluation D _ _ (RigidObject.projectObj (fun a ↦ G.obj (of a)) X.leftDual)
          (RigidObject.projectObj (fun a ↦ G.obj (of a)) X) pPG := by
      refine (congrArg (((mapWordIso G X).inv ⊗ₘ (mapWordIso G X.leftDual).inv) ≫ ·)
        hmG.symm).trans ?_
      refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _))).trans ?_
      exact (congrArg (fun k ↦ (k ⊗ₘ _) ≫ _) (Iso.inv_hom_id _)).trans
        ((congrArg (fun k ↦ (_ ⊗ₘ k) ≫ _) (Iso.inv_hom_id _)).trans
          ((congrArg (· ≫ _) (id_tensorHom_id _ _)).trans (Category.id_comp _)))
    refine hw.trans ?_
    have hstep : (((mapWordIso F X).hom ≫ (RigidObject.projectObjIso e X).hom ≫
          (mapWordIso G X).inv) ⊗ₘ
          ((mapWordIso F X.leftDual).hom ≫ (RigidObject.projectObjIso e X.leftDual).hom ≫
            (mapWordIso G X.leftDual).inv)) ≫
        @ExactPairing.evaluation D _ _ (G.obj ⟨X.leftDual⟩) (G.obj ⟨X⟩) pG =
        @ExactPairing.evaluation D _ _ (F.obj ⟨X.leftDual⟩) (F.obj ⟨X⟩) pF := by
      rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        ← MonoidalCategory.tensorHom_comp_tensorHom_assoc, hmG', he, hmF]
    exact hstep.symm.trans (congrArg (fun k ↦ ((k ⊗ₘ _) ≫ _)) ih.symm)

/-- From a lift to a strong monoidal functor `G`, `wordIso` is the extension of the isomorphisms
of generators to formal rigid objects followed by the inverse of `mapWordIso G`. -/
theorem wordIso_lift_left {fo : S.Obj → D}
    (fc : ∀ g : S.Coupon,
      RigidObject.projectObj fo (S.src g) ⟶ RigidObject.projectObj fo (S.tgt g))
    (G : S.FreeRigid ⥤ D) [G.Monoidal] (e : ∀ a, fo a ≅ G.obj (of a))
    (X : RigidObject S.Obj) :
    wordIso (lift fo fc) G e X = RigidObject.projectObjIso e X ≪≫ (mapWordIso G X).symm := by
  refine (wordIso_eq_mapWordIso (lift fo fc) G e X).trans ?_
  rw [mapWordIso_lift]
  exact Iso.refl_trans _

/-- Between two lifts, `wordIso` is the extension of the isomorphisms of generators to formal
rigid object expressions. -/
@[simp]
theorem wordIso_lift_lift {fo fo' : S.Obj → D}
    (fc : ∀ g : S.Coupon,
      RigidObject.projectObj fo (S.src g) ⟶ RigidObject.projectObj fo (S.tgt g))
    (fc' : ∀ g : S.Coupon,
      RigidObject.projectObj fo' (S.src g) ⟶ RigidObject.projectObj fo' (S.tgt g))
    (e : ∀ a, fo a ≅ fo' a) (X : RigidObject S.Obj) :
    wordIso (lift fo fc) (lift fo' fc') e X = RigidObject.projectObjIso e X := by
  refine (wordIso_lift_left fc (lift fo' fc') e X).trans ?_
  rw [mapWordIso_lift]
  exact (congrArg (RigidObject.projectObjIso e X ≪≫ ·) (Iso.refl_symm _)).trans (Iso.trans_refl _)

/-- From the lift of the generator images of `F` to `F`, `wordIso` of the identities is the
inverse of the comparison `mapWordIso F`. -/
theorem wordIso_lift_refl (F : S.FreeRigid ⥤ D) [F.Monoidal]
    (fc : ∀ g : S.Coupon,
      RigidObject.projectObj (fun a ↦ F.obj (of a)) (S.src g) ⟶
        RigidObject.projectObj (fun a ↦ F.obj (of a)) (S.tgt g))
    (X : RigidObject S.Obj) :
    wordIso (lift (fun a ↦ F.obj (of a)) fc) F (fun a ↦ Iso.refl (F.obj (of a))) X =
      (mapWordIso F X).symm := by
  refine (wordIso_lift_left fc F _ X).trans ?_
  rw [RigidObject.projectObjIso_refl]
  exact Iso.refl_trans _

/-- The extension to formal rigid object expressions of the components of a monoidal natural
isomorphism at the generating objects is its component at the object, conjugated by the
comparisons `mapWordIso`. -/
theorem projectObjIso_app {F G : S.FreeRigid ⥤ D} [F.Monoidal] [G.Monoidal] (α : F ≅ G)
    [NatTrans.IsMonoidal α.hom] (X : RigidObject S.Obj) :
    RigidObject.projectObjIso (fun a ↦ α.app (of a)) X =
      (mapWordIso F X).symm ≪≫ α.app ⟨X⟩ ≪≫ mapWordIso G X := by
  rw [← wordIso_app_of_isMonoidal α X, wordIso_eq_mapWordIso]
  ext
  simp

end MapWordIso

end TauCeti.RigidSignature.FreeRigid
