/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Universal property of the free rigid category on a duality signature

This file establishes the functorial universal property of `DualitySignature.FreeRigid S` into an
arbitrary (not necessarily strict) rigid monoidal category `D`:

* `FreeRigid.lift fo fc`: the universal strong monoidal functor determined by images `fo` of the
  generating objects and `fc` of the coupons, with identity unit and tensor comparisons and identity
  dual comparisons `FreeRigid.lift_mapRightDualIso` and `FreeRigid.lift_mapLeftDualIso`.
* `FreeRigid.natTrans_ext`: monoidal natural transformations from a strong monoidal functor out of
  `S.FreeRigid` to a lax monoidal functor into an arbitrary monoidal category are determined by
  their components at the generating objects.
* `FreeRigid.monoidalNatIso` and `FreeRigid.eq_monoidalNatIso`: two strong monoidal functors into an
  arbitrary monoidal category that agree up to isomorphism on generating objects compatibly with
  coupons are uniquely monoidally naturally isomorphic.

## Design notes and attribution

The universal lift and uniqueness construction parallel `TauCeti.TensorSignature.FreeMonoidal`
(modeled on Markus Himmel's `Mathlib/CategoryTheory/Monoidal/Free/Basic.lean`), extended to right
and left duality via `ExactPairing.rightMateIso`, `ExactPairing.leftMateIso`,
`Functor.mapRightDualIso`, `Functor.mapLeftDualIso`, and `NatTrans.app_right_eq_of_exactPairing`.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991).
* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, unpublished manuscript (1988).
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §4.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti.DualitySignature.FreeRigid

variable {S : DualitySignature.{u, v}}

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RigidCategory D] (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon, RigidObject.projectObj fo (S.src g) ⟶ RigidObject.projectObj fo (S.tgt g))

/-- Interpret a formal morphism expression in `D`, given interpretations `fo` of generating objects
and `fc` of coupons. Auxiliary definition for `FreeRigid.liftMap`. -/
private noncomputable def liftMapAux :
    ∀ {X Y : RigidObject S.Obj}, Hom X Y →
      (RigidObject.projectObj fo X ⟶ RigidObject.projectObj fo Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, Hom.α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, Hom.l_hom _ => (λ_ _).hom
  | _, _, Hom.l_inv _ => (λ_ _).inv
  | _, _, Hom.ρ_hom _ => (ρ_ _).hom
  | _, _, Hom.ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.rightCoevaluation X =>
    η_ (RigidObject.projectObj fo X) ((RigidObject.projectObj fo X)ᘁ)
  | _, _, Hom.rightEvaluation X =>
    ε_ (RigidObject.projectObj fo X) ((RigidObject.projectObj fo X)ᘁ)
  | _, _, Hom.leftCoevaluation X =>
    η_ (ᘁ(RigidObject.projectObj fo X)) (RigidObject.projectObj fo X)
  | _, _, Hom.leftEvaluation X =>
    ε_ (ᘁ(RigidObject.projectObj fo X)) (RigidObject.projectObj fo X)
  | _, _, Hom.coupon g => fc g
  | _, _, Hom.comp f g => liftMapAux f ≫ liftMapAux g
  | _, _, Hom.whiskerLeft X p => RigidObject.projectObj fo X ◁ liftMapAux p
  | _, _, Hom.whiskerRight p X => liftMapAux p ▷ RigidObject.projectObj fo X
  | _, _, Hom.tensor f g => liftMapAux f ⊗ₘ liftMapAux g

/-- The interpretation of formal morphism expressions respects the monoidal and zigzag axioms. -/
private theorem liftMapAux_sound {X Y : RigidObject S.Obj} {f g : Hom X Y} (h : HomEquiv f g) :
    liftMapAux fo fc f = liftMapAux fo fc g := by
  induction h with
  | refl => rfl
  | symm _ _ _ hfg => exact hfg.symm
  | trans _ _ hfg hgh => exact hfg.trans hgh
  | comp _ _ hf hg => simp only [liftMapAux, hf, hg]
  | whiskerLeft _ _ _ _ hf => dsimp only [liftMapAux]; rw [hf]
  | whiskerRight _ _ _ _ hf => dsimp only [liftMapAux]; rw [hf]
  | tensor _ _ hf hg => dsimp only [liftMapAux]; rw [hf, hg]
  | tensorHom_def => exact MonoidalCategory.tensorHom_def _ _
  | comp_id => exact Category.comp_id _
  | id_comp => exact Category.id_comp _
  | assoc => exact Category.assoc _ _ _
  | id_tensorHom_id => exact MonoidalCategory.id_tensorHom_id _ _
  | tensorHom_comp_tensorHom => exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  | whiskerLeft_id => exact MonoidalCategory.whiskerLeft_id _ _
  | id_whiskerRight => exact MonoidalCategory.id_whiskerRight _ _
  | α_hom_inv | ρ_hom_inv | l_hom_inv => exact Iso.hom_inv_id _
  | α_inv_hom | ρ_inv_hom | l_inv_hom => exact Iso.inv_hom_id _
  | associator_naturality => exact MonoidalCategory.associator_naturality _ _ _
  | ρ_naturality => exact MonoidalCategory.rightUnitor_naturality _
  | l_naturality => exact MonoidalCategory.leftUnitor_naturality _
  | pentagon => exact MonoidalCategory.pentagon _ _ _ _
  | triangle => exact MonoidalCategory.triangle _ _
  | right_coevaluation_evaluation X =>
    exact ExactPairing.coevaluation_evaluation _ ((RigidObject.projectObj fo X)ᘁ)
  | right_evaluation_coevaluation X =>
    exact ExactPairing.evaluation_coevaluation _ ((RigidObject.projectObj fo X)ᘁ)
  | left_coevaluation_evaluation X =>
    exact ExactPairing.coevaluation_evaluation (ᘁ(RigidObject.projectObj fo X)) _
  | left_evaluation_coevaluation X =>
    exact ExactPairing.evaluation_coevaluation (ᘁ(RigidObject.projectObj fo X)) _

/-- The interpretation of morphisms of `S.FreeRigid`, given the images `fo` of generating objects
and `fc` of coupons. This is the morphism map of `FreeRigid.lift`; compute it via the `lift_map_*`
lemmas. -/
noncomputable def liftMap {X Y : S.FreeRigid} (f : X ⟶ Y) :
    RigidObject.projectObj fo X.as ⟶ RigidObject.projectObj fo Y.as :=
  Quotient.lift (liftMapAux fo fc) (fun _ _ h ↦ liftMapAux_sound fo fc h) f

theorem liftMap_id (X : S.FreeRigid) : liftMap fo fc (𝟙 X) = 𝟙 _ := by rfl

theorem liftMap_comp {X Y Z : S.FreeRigid} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftMap fo fc (f ≫ g) = liftMap fo fc f ≫ liftMap fo fc g := by
  induction f using Quotient.inductionOn; induction g using Quotient.inductionOn; rfl

/-- The universal strong monoidal functor out of `S.FreeRigid` into an arbitrary rigid monoidal
category `D`, determined by the images `fo` of generating objects and `fc` of coupons. Its unit,
tensor and dual comparison isomorphisms are all identities. -/
@[expose] noncomputable def lift : S.FreeRigid ⥤ D where
  obj X := RigidObject.projectObj fo X.as
  map := liftMap fo fc
  map_id := liftMap_id fo fc
  map_comp := liftMap_comp fo fc

@[simp] theorem lift_obj_of (a : S.Obj) : (lift fo fc).obj (of a) = fo a := rfl

@[simp] theorem lift_obj_tensor (X Y : S.FreeRigid) :
    (lift fo fc).obj (X ⊗ Y) = (lift fo fc).obj X ⊗ (lift fo fc).obj Y := rfl

@[simp] theorem lift_obj_tensorUnit : (lift fo fc).obj (𝟙_ S.FreeRigid) = 𝟙_ D := rfl

@[simp] theorem lift_obj_rightDual (X : S.FreeRigid) :
    (lift fo fc).obj (Xᘁ) = ((lift fo fc).obj X)ᘁ := rfl

@[simp] theorem lift_obj_leftDual (X : S.FreeRigid) :
    (lift fo fc).obj (ᘁX) = ᘁ((lift fo fc).obj X) := rfl

@[simp] theorem lift_map_coupon (g : S.Coupon) : (lift fo fc).map (coupon g) = fc g := by rfl

@[simp] theorem lift_map_whiskerLeft (X : S.FreeRigid) {Y₁ Y₂ : S.FreeRigid} (f : Y₁ ⟶ Y₂) :
    (lift fo fc).map (X ◁ f) = (lift fo fc).obj X ◁ (lift fo fc).map f := by
  induction f using Quotient.inductionOn; rfl

@[simp] theorem lift_map_whiskerRight {X₁ X₂ : S.FreeRigid} (f : X₁ ⟶ X₂) (Y : S.FreeRigid) :
    (lift fo fc).map (f ▷ Y) = (lift fo fc).map f ▷ (lift fo fc).obj Y := by
  induction f using Quotient.inductionOn; rfl

@[simp] theorem lift_map_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeRigid} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (lift fo fc).map (f ⊗ₘ g) = (lift fo fc).map f ⊗ₘ (lift fo fc).map g := by
  induction f using Quotient.inductionOn; induction g using Quotient.inductionOn; rfl

@[simp] theorem lift_map_associator_hom (X Y Z : S.FreeRigid) :
    (lift fo fc).map (α_ X Y Z).hom =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).hom := by rfl

@[simp] theorem lift_map_associator_inv (X Y Z : S.FreeRigid) :
    (lift fo fc).map (α_ X Y Z).inv =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).inv := by rfl

/- The unitor lemmas are not `@[simp]`: Mathlib's `Functor.LaxMonoidal.left_unitality` and
`right_unitality` rewrite their right-hand sides back into `(lift fo fc).map` of a unitor. -/
theorem lift_map_leftUnitor_hom (X : S.FreeRigid) :
    (lift fo fc).map (λ_ X).hom = (λ_ ((lift fo fc).obj X)).hom := by rfl

theorem lift_map_leftUnitor_inv (X : S.FreeRigid) :
    (lift fo fc).map (λ_ X).inv = (λ_ ((lift fo fc).obj X)).inv := by rfl

theorem lift_map_rightUnitor_hom (X : S.FreeRigid) :
    (lift fo fc).map (ρ_ X).hom = (ρ_ ((lift fo fc).obj X)).hom := by rfl

theorem lift_map_rightUnitor_inv (X : S.FreeRigid) :
    (lift fo fc).map (ρ_ X).inv = (ρ_ ((lift fo fc).obj X)).inv := by rfl

@[simp] theorem lift_map_rightCoevaluation (X : S.FreeRigid) :
    (lift fo fc).map (η_ X (Xᘁ)) = η_ ((lift fo fc).obj X) (((lift fo fc).obj X)ᘁ) := by rfl

@[simp] theorem lift_map_rightEvaluation (X : S.FreeRigid) :
    (lift fo fc).map (ε_ X (Xᘁ)) = ε_ ((lift fo fc).obj X) (((lift fo fc).obj X)ᘁ) := by rfl

@[simp] theorem lift_map_leftCoevaluation (X : S.FreeRigid) :
    (lift fo fc).map (η_ (ᘁX) X) = η_ (ᘁ((lift fo fc).obj X)) ((lift fo fc).obj X) := by rfl

@[simp] theorem lift_map_leftEvaluation (X : S.FreeRigid) :
    (lift fo fc).map (ε_ (ᘁX) X) = ε_ (ᘁ((lift fo fc).obj X)) ((lift fo fc).obj X) := by rfl

noncomputable instance : (lift fo fc).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by intros; dsimp only [Iso.refl_hom, lift_obj_tensor]; simp
      μIso_hom_natural_right := by intros; dsimp only [Iso.refl_hom, lift_obj_tensor]; simp
      associativity := by intros; dsimp only [Iso.refl_hom, lift_obj_tensor]; simp
      left_unitality := by
        intros; dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
        simp [lift_map_leftUnitor_hom]
      right_unitality := by
        intros; dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
        simp [lift_map_rightUnitor_hom] }

@[simp] theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc) = 𝟙 _ := by rfl

@[simp] theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc) = 𝟙 _ := by rfl

@[simp] theorem lift_μ (X Y : S.FreeRigid) :
    Functor.LaxMonoidal.μ (lift fo fc) X Y = 𝟙 _ := by rfl

@[simp] theorem lift_δ (X Y : S.FreeRigid) :
    Functor.OplaxMonoidal.δ (lift fo fc) X Y = 𝟙 _ := by rfl

/-- Because `lift fo fc` strictly preserves chosen right duals and their evaluations, its right-dual
comparison isomorphism is the identity. -/
@[simp]
theorem lift_mapRightDualIso (X : S.FreeRigid) :
    (lift fo fc).mapRightDualIso X (_hFX := RightRigidCategory.rightDual ((lift fo fc).obj X)) =
      Iso.refl _ := by
  ext
  refine ExactPairing.rightHom_ext (X := (lift fo fc).obj X)
    (Y := @HasRightDual.rightDual _ _ _ ((lift fo fc).obj X) (RightRigidCategory.rightDual _)) ?_
  refine ((lift fo fc).mapRightDualIso_hom_whiskerRight_evaluation X
    (_hFX := RightRigidCategory.rightDual _)).trans ?_
  dsimp only [Iso.refl_hom, lift_obj_rightDual]
  simp

/-- Because `lift fo fc` strictly preserves chosen left duals and their evaluations, its left-dual
comparison isomorphism is the identity. -/
@[simp]
theorem lift_mapLeftDualIso (X : S.FreeRigid) :
    (lift fo fc).mapLeftDualIso X (_hFY := LeftRigidCategory.leftDual ((lift fo fc).obj X)) =
      Iso.refl _ := by
  ext
  refine ExactPairing.leftDualHom_ext
    (X := @HasLeftDual.leftDual _ _ _ ((lift fo fc).obj X) (LeftRigidCategory.leftDual _))
    (Y := (lift fo fc).obj X) ?_
  refine ((lift fo fc).whiskerLeft_mapLeftDualIso_hom_evaluation X
    (_hFY := LeftRigidCategory.leftDual _)).trans ?_
  dsimp only [Iso.refl_hom, lift_obj_leftDual]
  simp

end Lift

section Uniqueness

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- A monoidal natural transformation from a strong monoidal functor out of `S.FreeRigid` to a lax
monoidal functor into an arbitrary monoidal category is determined by its components at the
generating objects. No rigidity assumption on the target category `D` is required. -/
theorem natTrans_ext {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {F G : S.FreeRigid ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
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
    exact NatTrans.app_right_eq_of_exactPairing (⟨X⟩ : S.FreeRigid) ((⟨X⟩ : S.FreeRigid)ᘁ) hX
  | leftDual X hX =>
    exact NatTrans.app_left_eq_of_exactPairing (ᘁ(⟨X⟩ : S.FreeRigid)) (⟨X⟩ : S.FreeRigid) hX

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
variable (F G : S.FreeRigid ⥤ D) [F.Monoidal] [G.Monoidal] (e : ∀ a, F.obj (of a) ≅ G.obj (of a))

/-- The canonical isomorphism between the images of a formal rigid object expression under two
strong monoidal functors `F, G : S.FreeRigid ⥤ D`, built from isomorphisms `e` at the generating
objects together with the unit and tensor comparisons of `F` and `G` and adjoint mates for the
image exact pairings. -/
noncomputable def objIso : ∀ X : RigidObject S.Obj, F.obj ⟨X⟩ ≅ G.obj ⟨X⟩
  | .of a => e a
  | .unit => (Functor.Monoidal.εIso F).symm ≪≫ Functor.Monoidal.εIso G
  | .tensor X Y =>
    (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (objIso X ⊗ᵢ objIso Y) ≪≫
      Functor.Monoidal.μIso G ⟨X⟩ ⟨Y⟩
  | .rightDual X =>
    ExactPairing.rightMateIso
      (G.mapExactPairing (⟨X⟩ : S.FreeRigid) ((⟨X⟩ : S.FreeRigid)ᘁ))
      (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ((⟨X⟩ : S.FreeRigid)ᘁ))
      (objIso X).symm
  | .leftDual X =>
    ExactPairing.leftMateIso
      (G.mapExactPairing (ᘁ(⟨X⟩ : S.FreeRigid)) (⟨X⟩ : S.FreeRigid))
      (F.mapExactPairing (ᘁ(⟨X⟩ : S.FreeRigid)) (⟨X⟩ : S.FreeRigid))
      (objIso X).symm

@[simp] theorem objIso_of (a : S.Obj) : objIso F G e (of a).as = e a := by rfl

@[simp] theorem objIso_tensorUnit_hom :
    (objIso F G e (𝟙_ S.FreeRigid).as).hom = η F ≫ ε G := by rfl

@[simp] theorem objIso_tensorUnit_inv :
    (objIso F G e (𝟙_ S.FreeRigid).as).inv = η G ≫ ε F := by rfl

@[simp] theorem objIso_tensor_hom (X Y : S.FreeRigid) :
    (objIso F G e (X ⊗ Y).as).hom =
      δ F X Y ≫ ((objIso F G e X.as).hom ⊗ₘ (objIso F G e Y.as).hom) ≫ μ G X Y := by rfl

@[simp] theorem objIso_tensor_inv (X Y : S.FreeRigid) :
    (objIso F G e (X ⊗ Y).as).inv =
      δ G X Y ≫ ((objIso F G e X.as).inv ⊗ₘ (objIso F G e Y.as).inv) ≫ μ F X Y :=
  Category.assoc _ _ _

theorem objIso_rightDual (X : S.FreeRigid) :
    objIso F G e (Xᘁ).as =
      ExactPairing.rightMateIso (G.mapExactPairing X (Xᘁ)) (F.mapExactPairing X (Xᘁ))
        (objIso F G e X.as).symm := by rfl

theorem objIso_leftDual (X : S.FreeRigid) :
    objIso F G e (ᘁX).as =
      ExactPairing.leftMateIso (G.mapExactPairing (ᘁX) X) (F.mapExactPairing (ᘁX) X)
        (objIso F G e X.as).symm := by rfl

@[simp] theorem objIso_rightDual_hom (X : S.FreeRigid) :
    (objIso F G e (Xᘁ).as).hom =
      ExactPairing.rightMate (G.mapExactPairing X (Xᘁ)) (F.mapExactPairing X (Xᘁ))
        (objIso F G e X.as).inv :=
  ExactPairing.rightMateIso_hom _ _ _

@[simp] theorem objIso_rightDual_inv (X : S.FreeRigid) :
    (objIso F G e (Xᘁ).as).inv =
      ExactPairing.rightMate (F.mapExactPairing X (Xᘁ)) (G.mapExactPairing X (Xᘁ))
        (objIso F G e X.as).hom :=
  ExactPairing.rightMateIso_inv _ _ _

@[simp] theorem objIso_leftDual_hom (X : S.FreeRigid) :
    (objIso F G e (ᘁX).as).hom =
      ExactPairing.leftMate (G.mapExactPairing (ᘁX) X) (F.mapExactPairing (ᘁX) X)
        (objIso F G e X.as).inv :=
  ExactPairing.leftMateIso_hom _ _ _

@[simp] theorem objIso_leftDual_inv (X : S.FreeRigid) :
    (objIso F G e (ᘁX).as).inv =
      ExactPairing.leftMate (F.mapExactPairing (ᘁX) X) (G.mapExactPairing (ᘁX) X)
        (objIso F G e X.as).hom :=
  ExactPairing.leftMateIso_inv _ _ _

variable {F G e}

attribute [local simp] whiskerLeft_comp_tensorHom whiskerLeft_comp_tensorHom_assoc
  whiskerRight_comp_tensorHom whiskerRight_comp_tensorHom_assoc tensorHom_comp_whiskerLeft
  tensorHom_comp_whiskerLeft_assoc tensorHom_comp_whiskerRight tensorHom_comp_whiskerRight_assoc

private theorem map_rightCoevaluation_comp_objIso_hom (X : S.FreeRigid) :
    F.map (η_ X (Xᘁ)) ≫ (objIso F G e (X ⊗ Xᘁ).as).hom =
      (objIso F G e (𝟙_ S.FreeRigid).as).hom ≫ G.map (η_ X (Xᘁ)) := by
  rw [← cancel_epi (ε F), ← cancel_mono (δ G X (Xᘁ))]
  simpa using ExactPairing.coevaluation_comp_tensorHom_rightMate
    (G.mapExactPairing X (Xᘁ)) (F.mapExactPairing X (Xᘁ)) (objIso F G e X.as).symm

private theorem map_rightEvaluation_comp_objIso_hom (X : S.FreeRigid) :
    F.map (ε_ X (Xᘁ)) ≫ (objIso F G e (𝟙_ S.FreeRigid).as).hom =
      (objIso F G e (Xᘁ ⊗ X).as).hom ≫ G.map (ε_ X (Xᘁ)) := by
  rw [← cancel_epi (μ F (Xᘁ) X), ← cancel_mono (η G)]
  simpa using (ExactPairing.tensorHom_rightMate_comp_evaluation
    (G.mapExactPairing X (Xᘁ)) (F.mapExactPairing X (Xᘁ)) (objIso F G e X.as).symm).symm

private theorem map_leftCoevaluation_comp_objIso_hom (X : S.FreeRigid) :
    F.map (η_ (ᘁX) X) ≫ (objIso F G e ((ᘁX) ⊗ X).as).hom =
      (objIso F G e (𝟙_ S.FreeRigid).as).hom ≫ G.map (η_ (ᘁX) X) := by
  rw [← cancel_epi (ε F), ← cancel_mono (δ G (ᘁX) X)]
  simpa using ExactPairing.coevaluation_comp_tensorHom_leftMate
    (G.mapExactPairing (ᘁX) X) (F.mapExactPairing (ᘁX) X) (objIso F G e X.as).symm

private theorem map_leftEvaluation_comp_objIso_hom (X : S.FreeRigid) :
    F.map (ε_ (ᘁX) X) ≫ (objIso F G e (𝟙_ S.FreeRigid).as).hom =
      (objIso F G e (X ⊗ ᘁX).as).hom ≫ G.map (ε_ (ᘁX) X) := by
  rw [← cancel_epi (μ F X (ᘁX)), ← cancel_mono (η G)]
  simpa using (ExactPairing.tensorHom_leftMate_comp_evaluation
    (G.mapExactPairing (ᘁX) X) (F.mapExactPairing (ᘁX) X) (objIso F G e X.as).symm).symm

/-- The family `objIso F G e` is natural with respect to all morphisms of `S.FreeRigid` as soon as
it is natural with respect to every coupon. -/
theorem map_comp_objIso_hom
    (he : ∀ g, F.map (coupon g) ≫ (objIso F G e (S.tgt g)).hom =
      (objIso F G e (S.src g)).hom ≫ G.map (coupon g))
    {X Y : S.FreeRigid} (f : X ⟶ Y) :
    F.map f ≫ (objIso F G e Y.as).hom = (objIso F G e X.as).hom ≫ G.map f := by
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
    rw [← cancel_epi (ε F ▷ F.obj X ≫ μ F (𝟙_ _) X)]; simp; simp [tensorHom_def']
  | l_inv X =>
    rw [← cancel_mono (δ G (𝟙_ _) X ≫ η G ▷ G.obj X)]; simp
    simp [MonoidalCategory.tensorHom_def, ← Functor.OplaxMonoidal.left_unitality]
  | ρ_hom X =>
    rw [← cancel_epi (F.obj X ◁ ε F ≫ μ F X (𝟙_ _))]; simp; simp [MonoidalCategory.tensorHom_def]
  | ρ_inv X =>
    rw [← cancel_mono (δ G X (𝟙_ _) ≫ G.obj X ◁ η G)]; simp
    simp [tensorHom_def', ← Functor.OplaxMonoidal.right_unitality]
  | rightCoevaluation X => exact map_rightCoevaluation_comp_objIso_hom X
  | rightEvaluation X => exact map_rightEvaluation_comp_objIso_hom X
  | leftCoevaluation X => exact map_leftCoevaluation_comp_objIso_hom X
  | leftEvaluation X => exact map_leftEvaluation_comp_objIso_hom X
  | coupon g => exact he g
  | comp _ _ hf hg =>
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg, reassoc_of% hf]
  | whiskerLeft X _ hf =>
    simp only [objIso_tensor_hom, Functor.Monoidal.map_whiskerLeft, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerLeft_comp_tensorHom_assoc,
      tensorHom_comp_whiskerLeft_assoc, hf]
  | whiskerRight _ X hf =>
    simp only [objIso_tensor_hom, Functor.Monoidal.map_whiskerRight, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerRight_comp_tensorHom_assoc,
      tensorHom_comp_whiskerRight_assoc, hf]

/-- Two strong monoidal functors out of `S.FreeRigid` into an arbitrary monoidal category `D` that
agree up to isomorphisms `e` on the generating objects, compatibly with every coupon, are isomorphic
by a monoidal natural isomorphism extending `e`. -/
noncomputable def monoidalNatIso
    (he : ∀ g, F.map (coupon g) ≫ (objIso F G e (S.tgt g)).hom =
      (objIso F G e (S.src g)).hom ≫ G.map (coupon g)) :
    F ≅ G :=
  NatIso.ofComponents (fun X ↦ objIso F G e X.as) fun f ↦ map_comp_objIso_hom he f

variable (he : ∀ g, F.map (coupon g) ≫ (objIso F G e (S.tgt g)).hom =
  (objIso F G e (S.src g)).hom ≫ G.map (coupon g))

@[simp] theorem monoidalNatIso_hom_app (X : S.FreeRigid) :
    (monoidalNatIso he).hom.app X = (objIso F G e X.as).hom := by rfl

@[simp] theorem monoidalNatIso_inv_app (X : S.FreeRigid) :
    (monoidalNatIso he).inv.app X = (objIso F G e X.as).inv := by rfl

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso he).hom.app (of a) = (e a).hom := by rfl

theorem monoidalNatIso_inv_app_of (a : S.Obj) :
    (monoidalNatIso he).inv.app (of a) = (e a).inv := by rfl

instance : NatTrans.IsMonoidal (monoidalNatIso he).hom where
  unit := by
    rw [monoidalNatIso_hom_app, objIso_tensorUnit_hom, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    rw [monoidalNatIso_hom_app, objIso_tensor_hom, Functor.Monoidal.μ_δ_assoc,
      monoidalNatIso_hom_app, monoidalNatIso_hom_app]

/-- Uniqueness of the monoidal natural isomorphism extending `e` on the generating objects. -/
theorem eq_monoidalNatIso {α : F ≅ G} [NatTrans.IsMonoidal α.hom]
    (hα : ∀ a, α.hom.app (of a) = (e a).hom) :
    α = monoidalNatIso he := by
  ext1
  exact natTrans_ext fun a ↦ (hα a).trans (monoidalNatIso_hom_app_of he a).symm

end Uniqueness

end TauCeti.DualitySignature.FreeRigid
