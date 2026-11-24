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
  | .unit => Functor.Monoidal.isoAppUnit F G
  | .tensor X Y => Functor.Monoidal.isoAppTensor F G (wordIso X) (wordIso Y)
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

theorem wordIso_unit : wordIso F G e .unit = Functor.Monoidal.isoAppUnit F G := (rfl)

theorem wordIso_tensor (X Y : RigidObject S.Obj) :
    wordIso F G e (X.tensor Y) =
      Functor.Monoidal.isoAppTensor F G (wordIso F G e X) (wordIso F G e Y) :=
  (rfl)

@[simp]
theorem wordIso_tensorUnit_hom : (wordIso F G e (𝟙_ S.FreeRigid).as).hom = η F ≫ ε G :=
  Functor.Monoidal.isoAppUnit_hom F G

@[simp]
theorem wordIso_tensorUnit_inv : (wordIso F G e (𝟙_ S.FreeRigid).as).inv = η G ≫ ε F :=
  Functor.Monoidal.isoAppUnit_inv F G

@[simp]
theorem wordIso_tensor_hom (X Y : S.FreeRigid) :
    (wordIso F G e (X ⊗ Y).as).hom =
      δ F X Y ≫ ((wordIso F G e X.as).hom ⊗ₘ (wordIso F G e Y.as).hom) ≫ μ G X Y :=
  Functor.Monoidal.isoAppTensor_hom F G _ _

@[simp]
theorem wordIso_tensor_inv (X Y : S.FreeRigid) :
    (wordIso F G e (X ⊗ Y).as).inv =
      δ G X Y ≫ ((wordIso F G e X.as).inv ⊗ₘ (wordIso F G e Y.as).inv) ≫ μ F X Y :=
  Functor.Monoidal.isoAppTensor_inv F G _ _

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

end TauCeti.RigidSignature.FreeRigid
