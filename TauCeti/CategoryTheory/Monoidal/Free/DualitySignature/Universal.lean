/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core
public import TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.Basic
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Universal property of the free rigid category on a duality signature

Functorial universal property of `DualitySignature.FreeRigid S` into an arbitrary rigid monoidal
category `D`:

* `FreeRigid.lift fo fc`: universal strong monoidal functor determined by images `fo` of
  generators and `fc` of coupons, with identity comparisons (`FreeRigid.lift_mapRightDualIso`,
  `FreeRigid.lift_mapLeftDualIso`).
* `FreeRigid.natTrans_ext`, `FreeRigid.monoidalNatIso`, `FreeRigid.eq_monoidalNatIso`: monoidal
  natural transformations `F ⟶ G` (for `G` lax) out of `S.FreeRigid` are determined on generators,
  and strong monoidal functors agreeing up to isomorphism compatibly with coupons are uniquely
  monoidally naturally isomorphic.
* `FreeRigid.mapObjIso`, `FreeRigid.objIso_eq_mapObjIso`: canonical boundary comparisons factoring
  `objIso` through `RigidObject.evalIso`.
* `DualitySignature.Interpretation` and `DualitySignature.Interpretation.equivCoreMonoidalFunctor`:
  groupoid equivalence between interpretations of `S` in `D` and strong monoidal functors
  `S.FreeRigid ⥤ D`.

## Design notes and attribution

Parallels `TauCeti.TensorSignature.FreeMonoidal` and `TauCeti.TensorSignature.Interpretation`
(modeled on Markus Himmel's `Mathlib/CategoryTheory/Monoidal/Free/Basic.lean`), extended via
`ExactPairing.rightMateIso`, `ExactPairing.leftMateIso`, `Functor.mapRightDualIso`,
`Functor.mapLeftDualIso`, and `NatTrans.app_right_eq_of_exactPairing`.

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
  (fc : ∀ g : S.Coupon, RigidObject.eval fo (S.src g) ⟶ RigidObject.eval fo (S.tgt g))

/-- Interpret a formal morphism expression in `D`, given interpretations `fo` of generating objects
and `fc` of coupons. Auxiliary definition for `FreeRigid.liftMap`. -/
private noncomputable def liftMapAux :
    ∀ {X Y : RigidObject S.Obj}, Hom X Y → (RigidObject.eval fo X ⟶ RigidObject.eval fo Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, Hom.α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, Hom.l_hom _ => (λ_ _).hom
  | _, _, Hom.l_inv _ => (λ_ _).inv
  | _, _, Hom.ρ_hom _ => (ρ_ _).hom
  | _, _, Hom.ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.rightCoevaluation X => η_ (RigidObject.eval fo X) ((RigidObject.eval fo X)ᘁ)
  | _, _, Hom.rightEvaluation X => ε_ (RigidObject.eval fo X) ((RigidObject.eval fo X)ᘁ)
  | _, _, Hom.leftCoevaluation X => η_ (ᘁ(RigidObject.eval fo X)) (RigidObject.eval fo X)
  | _, _, Hom.leftEvaluation X => ε_ (ᘁ(RigidObject.eval fo X)) (RigidObject.eval fo X)
  | _, _, Hom.coupon g => fc g
  | _, _, Hom.comp f g => liftMapAux f ≫ liftMapAux g
  | _, _, Hom.whiskerLeft X p => RigidObject.eval fo X ◁ liftMapAux p
  | _, _, Hom.whiskerRight p X => liftMapAux p ▷ RigidObject.eval fo X
  | _, _, Hom.tensor f g => liftMapAux f ⊗ₘ liftMapAux g

/-- The interpretation of formal morphism expressions respects the monoidal and zigzag axioms. -/
private theorem liftMapAux_sound {X Y : RigidObject S.Obj} {f g : Hom X Y} (h : HomEquiv f g) :
    liftMapAux fo fc f = liftMapAux fo fc g := by
  induction h with
  | refl => rfl
  | symm _ _ _ hfg => exact hfg.symm
  | trans _ _ hfg hgh => exact hfg.trans hgh
  | comp _ _ hf hg => simp only [liftMapAux, hf, hg]
  | whiskerLeft _ _ _ _ hf | whiskerRight _ _ _ _ hf => dsimp only [liftMapAux]; rw [hf]
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
  | right_coevaluation_evaluation X | left_coevaluation_evaluation X =>
    dsimp only [liftMapAux, RigidObject.eval]; exact ExactPairing.coevaluation_evaluation _ _
  | right_evaluation_coevaluation X | left_evaluation_coevaluation X =>
    dsimp only [liftMapAux, RigidObject.eval]; exact ExactPairing.evaluation_coevaluation _ _

/-- The interpretation of morphisms of `S.FreeRigid`, given the images `fo` of generating objects
and `fc` of coupons. This is the morphism map of `FreeRigid.lift`; compute it via the `lift_map_*`
lemmas. -/
noncomputable def liftMap {X Y : S.FreeRigid} (f : X ⟶ Y) :
    RigidObject.eval fo X.as ⟶ RigidObject.eval fo Y.as :=
  Quotient.lift (liftMapAux fo fc) (fun _ _ h ↦ liftMapAux_sound fo fc h) f

theorem liftMap_id (X : S.FreeRigid) : liftMap fo fc (𝟙 X) = 𝟙 _ := by rfl
theorem liftMap_comp {X Y Z : S.FreeRigid} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftMap fo fc (f ≫ g) = liftMap fo fc f ≫ liftMap fo fc g := by
  induction f using Quotient.inductionOn; induction g using Quotient.inductionOn; rfl

/-- The universal strong monoidal functor out of `S.FreeRigid` into an arbitrary rigid monoidal
category `D`, determined by the images `fo` of generating objects and `fc` of coupons. Its unit,
tensor and dual comparison isomorphisms are all identities. -/
@[expose] noncomputable def lift : S.FreeRigid ⥤ D where
  obj X := RigidObject.eval fo X.as
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
@[simp] theorem lift_map_associator_hom (X Y Z : S.FreeRigid) : (lift fo fc).map (α_ X Y Z).hom =
    (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).hom := by rfl
@[simp] theorem lift_map_associator_inv (X Y Z : S.FreeRigid) : (lift fo fc).map (α_ X Y Z).inv =
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
    { εIso := Iso.refl _, μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by intros; dsimp only [Iso.refl_hom, lift_obj_tensor]; simp
      μIso_hom_natural_right := by intros; dsimp only [Iso.refl_hom, lift_obj_tensor]; simp
      associativity := by intros; dsimp only [Iso.refl_hom, lift_obj_tensor]; simp
      left_unitality := by intros; dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
                           simp [lift_map_leftUnitor_hom]
      right_unitality := by intros; dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
                            simp [lift_map_rightUnitor_hom] }

@[simp] theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc) = 𝟙 _ := by rfl
@[simp] theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc) = 𝟙 _ := by rfl
@[simp] theorem lift_μ (X Y : S.FreeRigid) : Functor.LaxMonoidal.μ (lift fo fc) X Y = 𝟙 _ := by rfl
@[simp] theorem lift_δ (X Y : S.FreeRigid) : Functor.OplaxMonoidal.δ (lift fo fc) X Y = 𝟙 _ := rfl

/-- Because `lift fo fc` strictly preserves chosen right duals and their evaluations, its right-dual
comparison isomorphism is the identity. -/
@[simp] theorem lift_mapRightDualIso (X : S.FreeRigid) :
    (lift fo fc).mapRightDualIso X (_hFX := RightRigidCategory.rightDual ((lift fo fc).obj X)) =
      Iso.refl _ := by
  ext; refine ExactPairing.rightHom_ext (X := (lift fo fc).obj X)
    (Y := @HasRightDual.rightDual _ _ _ ((lift fo fc).obj X) (RightRigidCategory.rightDual _)) ?_
  refine ((lift fo fc).mapRightDualIso_hom_whiskerRight_evaluation X
    (_hFX := RightRigidCategory.rightDual _)).trans (by simp [lift_obj_rightDual])

/-- Because `lift fo fc` strictly preserves chosen left duals and their evaluations, its left-dual
comparison isomorphism is the identity. -/
@[simp] theorem lift_mapLeftDualIso (X : S.FreeRigid) :
    (lift fo fc).mapLeftDualIso X (_hFY := LeftRigidCategory.leftDual ((lift fo fc).obj X)) =
      Iso.refl _ := by
  ext; refine ExactPairing.leftDualHom_ext
    (X := @HasLeftDual.leftDual _ _ _ ((lift fo fc).obj X) (LeftRigidCategory.leftDual _))
    (Y := (lift fo fc).obj X) ?_
  refine ((lift fo fc).whiskerLeft_mapLeftDualIso_hom_evaluation X
    (_hFY := LeftRigidCategory.leftDual _)).trans (by simp [lift_obj_leftDual])

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
    refine Eq.trans ?_ (NatTrans.IsMonoidal.tensor (τ := β) ⟨X⟩ ⟨Y⟩).symm; rw [hX, hY]
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
  | .tensor X Y => (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (objIso X ⊗ᵢ objIso Y) ≪≫
      Functor.Monoidal.μIso G ⟨X⟩ ⟨Y⟩
  | .rightDual X => ExactPairing.rightMateIso
      (G.mapExactPairing (⟨X⟩ : S.FreeRigid) ((⟨X⟩ : S.FreeRigid)ᘁ))
      (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ((⟨X⟩ : S.FreeRigid)ᘁ)) (objIso X).symm
  | .leftDual X => ExactPairing.leftMateIso
      (G.mapExactPairing (ᘁ(⟨X⟩ : S.FreeRigid)) (⟨X⟩ : S.FreeRigid))
      (F.mapExactPairing (ᘁ(⟨X⟩ : S.FreeRigid)) (⟨X⟩ : S.FreeRigid)) (objIso X).symm

@[simp] theorem objIso_of (a : S.Obj) : objIso F G e (of a).as = e a := by rfl
@[simp] theorem objIso_tensorUnit_hom :
    (objIso F G e (𝟙_ S.FreeRigid).as).hom = η F ≫ ε G := by rfl
@[simp] theorem objIso_tensorUnit_inv :
    (objIso F G e (𝟙_ S.FreeRigid).as).inv = η G ≫ ε F := by rfl
@[simp] theorem objIso_tensor_hom (X Y : S.FreeRigid) : (objIso F G e (X ⊗ Y).as).hom =
    δ F X Y ≫ ((objIso F G e X.as).hom ⊗ₘ (objIso F G e Y.as).hom) ≫ μ G X Y := by rfl
@[simp] theorem objIso_tensor_inv (X Y : S.FreeRigid) :
    (objIso F G e (X ⊗ Y).as).inv =
      δ G X Y ≫ ((objIso F G e X.as).inv ⊗ₘ (objIso F G e Y.as).inv) ≫ μ F X Y :=
  Category.assoc _ _ _
theorem objIso_rightDual (X : S.FreeRigid) : objIso F G e (Xᘁ).as = ExactPairing.rightMateIso
    (G.mapExactPairing X (Xᘁ)) (F.mapExactPairing X (Xᘁ)) (objIso F G e X.as).symm := by rfl
theorem objIso_leftDual (X : S.FreeRigid) : objIso F G e (ᘁX).as = ExactPairing.leftMateIso
    (G.mapExactPairing (ᘁX) X) (F.mapExactPairing (ᘁX) X) (objIso F G e X.as).symm := by rfl
@[simp] theorem objIso_rightDual_hom (X : S.FreeRigid) : (objIso F G e (Xᘁ).as).hom =
    ExactPairing.rightMate (G.mapExactPairing X (Xᘁ)) (F.mapExactPairing X (Xᘁ))
      (objIso F G e X.as).inv := ExactPairing.rightMateIso_hom _ _ _
@[simp] theorem objIso_rightDual_inv (X : S.FreeRigid) : (objIso F G e (Xᘁ).as).inv =
    ExactPairing.rightMate (F.mapExactPairing X (Xᘁ)) (G.mapExactPairing X (Xᘁ))
      (objIso F G e X.as).hom := ExactPairing.rightMateIso_inv _ _ _
@[simp] theorem objIso_leftDual_hom (X : S.FreeRigid) : (objIso F G e (ᘁX).as).hom =
    ExactPairing.leftMate (G.mapExactPairing (ᘁX) X) (F.mapExactPairing (ᘁX) X)
      (objIso F G e X.as).inv := ExactPairing.leftMateIso_hom _ _ _
@[simp] theorem objIso_leftDual_inv (X : S.FreeRigid) : (objIso F G e (ᘁX).as).inv =
    ExactPairing.leftMate (F.mapExactPairing (ᘁX) X) (G.mapExactPairing (ᘁX) X)
      (objIso F G e X.as).hom := ExactPairing.leftMateIso_inv _ _ _

variable {F G e}

attribute [local simp] whiskerLeft_comp_tensorHom whiskerLeft_comp_tensorHom_assoc
  whiskerRight_comp_tensorHom whiskerRight_comp_tensorHom_assoc tensorHom_comp_whiskerLeft
  tensorHom_comp_whiskerLeft_assoc tensorHom_comp_whiskerRight tensorHom_comp_whiskerRight_assoc

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
    rw [← cancel_mono (δ G (𝟙_ _) X ≫ η G ▷ G.obj X)]
    simp; simp [MonoidalCategory.tensorHom_def, ← Functor.OplaxMonoidal.left_unitality]
  | ρ_hom X =>
    rw [← cancel_epi (F.obj X ◁ ε F ≫ μ F X (𝟙_ _))]; simp; simp [MonoidalCategory.tensorHom_def]
  | ρ_inv X =>
    rw [← cancel_mono (δ G X (𝟙_ _) ≫ G.obj X ◁ η G)]
    simp; simp [tensorHom_def', ← Functor.OplaxMonoidal.right_unitality]
  | rightCoevaluation X =>
    rw [← cancel_epi (ε F), ← cancel_mono (δ G X (Xᘁ))]
    simpa using ExactPairing.coevaluation_comp_tensorHom_rightMate
      (G.mapExactPairing X (Xᘁ)) (F.mapExactPairing X (Xᘁ)) (objIso F G e X.as).symm
  | rightEvaluation X =>
    rw [← cancel_epi (μ F (Xᘁ) X), ← cancel_mono (η G)]
    simpa using (ExactPairing.tensorHom_rightMate_comp_evaluation
      (G.mapExactPairing X (Xᘁ)) (F.mapExactPairing X (Xᘁ)) (objIso F G e X.as).symm).symm
  | leftCoevaluation X =>
    rw [← cancel_epi (ε F), ← cancel_mono (δ G (ᘁX) X)]
    simpa using ExactPairing.coevaluation_comp_tensorHom_leftMate
      (G.mapExactPairing (ᘁX) X) (F.mapExactPairing (ᘁX) X) (objIso F G e X.as).symm
  | leftEvaluation X =>
    rw [← cancel_epi (μ F X (ᘁX)), ← cancel_mono (η G)]
    simpa using (ExactPairing.tensorHom_leftMate_comp_evaluation
      (G.mapExactPairing (ᘁX) X) (F.mapExactPairing (ᘁX) X) (objIso F G e X.as).symm).symm
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
      (objIso F G e (S.src g)).hom ≫ G.map (coupon g)) : F ≅ G :=
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

instance isMonoidal_monoidalNatIso_hom : NatTrans.IsMonoidal (monoidalNatIso he).hom where
  unit := by rw [monoidalNatIso_hom_app, objIso_tensorUnit_hom, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    rw [monoidalNatIso_hom_app, objIso_tensor_hom, Functor.Monoidal.μ_δ_assoc,
      monoidalNatIso_hom_app, monoidalNatIso_hom_app]

/-- Uniqueness of the monoidal natural isomorphism extending `e` on the generating objects. -/
theorem eq_monoidalNatIso {α : F ≅ G} [NatTrans.IsMonoidal α.hom]
    (hα : ∀ a, α.hom.app (of a) = (e a).hom) : α = monoidalNatIso he := by
  ext1; exact natTrans_ext fun a ↦ (hα a).trans (monoidalNatIso_hom_app_of he a).symm

/-- A monoidal natural isomorphism between strong monoidal functors out of `S.FreeRigid` is
the `objIso` of its components at the generating objects. -/
theorem objIso_app {F G : S.FreeRigid ⥤ D} [F.Monoidal] [G.Monoidal] (α : F ≅ G)
    [NatTrans.IsMonoidal α.hom] (X : RigidObject S.Obj) :
    objIso F G (fun a ↦ α.app (of a)) X = α.app ⟨X⟩ := by
  ext
  induction X with
  | of a => exact congrArg Iso.hom (objIso_of F G _ a)
  | unit =>
    refine (objIso_tensorUnit_hom F G _).trans ?_
    rw [← NatTrans.IsMonoidal.unit (τ := α.hom), Functor.Monoidal.η_ε_assoc, Iso.app_hom]; rfl
  | tensor X Y hX hY =>
    refine (objIso_tensor_hom F G _ ⟨X⟩ ⟨Y⟩).trans ?_; dsimp only
    rw [hX, hY, Iso.app_hom, Iso.app_hom, ← NatTrans.IsMonoidal.tensor,
      Functor.Monoidal.δ_μ_assoc, Iso.app_hom]; rfl
  | rightDual X hX =>
    refine (objIso_rightDual_hom F G _ ⟨X⟩).trans ?_
    have hinv : (objIso F G (fun a ↦ α.app (of a)) X).inv = α.inv.app ⟨X⟩ :=
      congrArg Iso.inv (Iso.ext hX)
    rw [hinv, ← Category.id_comp (ExactPairing.rightMate _ _ _),
      ← α.hom_inv_id_app (⟨X⟩ᘁ), Category.assoc]
    exact (congrArg (α.hom.app (⟨X⟩ᘁ) ≫ ·)
      (NatTrans.app_comp_rightMate_mapExactPairing α.inv ⟨X⟩ (⟨X⟩ᘁ))).trans (Category.comp_id _)
  | leftDual X hX =>
    refine (objIso_leftDual_hom F G _ ⟨X⟩).trans ?_
    have hinv : (objIso F G (fun a ↦ α.app (of a)) X).inv = α.inv.app ⟨X⟩ :=
      congrArg Iso.inv (Iso.ext hX)
    rw [hinv, ← Category.id_comp (ExactPairing.leftMate _ _ _),
      ← α.hom_inv_id_app (ᘁ⟨X⟩), Category.assoc]
    exact (congrArg (α.hom.app (ᘁ⟨X⟩) ≫ ·)
      (NatTrans.app_comp_leftMate_mapExactPairing α.inv (ᘁ⟨X⟩) ⟨X⟩)).trans (Category.comp_id _)

end Uniqueness

section MapObjIso

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RigidCategory D]

/-- The canonical boundary isomorphism between the image of a formal rigid object `X` under a
strong monoidal functor `F : S.FreeRigid ⥤ D` and `RigidObject.eval (fun a ↦ F.obj (of a)) X`,
built from the unit, tensor, right-dual and left-dual comparison isomorphisms of `F`. -/
noncomputable def mapObjIso (F : S.FreeRigid ⥤ D) [F.Monoidal] :
    ∀ X : RigidObject S.Obj, F.obj ⟨X⟩ ≅ RigidObject.eval (fun a ↦ F.obj (of a)) X
  | .of _ => Iso.refl _
  | .unit => (Functor.Monoidal.εIso F).symm
  | .tensor X Y => (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (mapObjIso F X ⊗ᵢ mapObjIso F Y)
  | .rightDual X => F.mapRightDualIso ⟨X⟩ ≪≫ (mapObjIso F X).symm.rightAdjointMate
  | .leftDual X => F.mapLeftDualIso ⟨X⟩ ≪≫ (mapObjIso F X).symm.leftAdjointMate

@[simp] theorem mapObjIso_of (F : S.FreeRigid ⥤ D) [F.Monoidal] (a : S.Obj) :
    mapObjIso F (.of a) = Iso.refl (F.obj (of a)) := (rfl)
@[simp] theorem mapObjIso_tensorUnit_hom (F : S.FreeRigid ⥤ D) [F.Monoidal] :
    (mapObjIso F .unit).hom = η F := (rfl)
@[simp] theorem mapObjIso_tensorUnit_inv (F : S.FreeRigid ⥤ D) [F.Monoidal] :
    (mapObjIso F .unit).inv = ε F := (rfl)
@[simp] theorem mapObjIso_tensor_hom (F : S.FreeRigid ⥤ D) [F.Monoidal] (X Y : RigidObject S.Obj) :
    (mapObjIso F (X.tensor Y)).hom =
      δ F ⟨X⟩ ⟨Y⟩ ≫ ((mapObjIso F X).hom ⊗ₘ (mapObjIso F Y).hom) := (rfl)
@[simp] theorem mapObjIso_tensor_inv (F : S.FreeRigid ⥤ D) [F.Monoidal] (X Y : RigidObject S.Obj) :
    (mapObjIso F (X.tensor Y)).inv =
      ((mapObjIso F X).inv ⊗ₘ (mapObjIso F Y).inv) ≫ μ F ⟨X⟩ ⟨Y⟩ := (rfl)
@[simp] theorem mapObjIso_rightDual (F : S.FreeRigid ⥤ D) [F.Monoidal] (X : RigidObject S.Obj) :
    mapObjIso F X.rightDual =
      F.mapRightDualIso ⟨X⟩ ≪≫ (mapObjIso F X).symm.rightAdjointMate := by rfl
@[simp] theorem mapObjIso_leftDual (F : S.FreeRigid ⥤ D) [F.Monoidal] (X : RigidObject S.Obj) :
    mapObjIso F X.leftDual =
      F.mapLeftDualIso ⟨X⟩ ≪≫ (mapObjIso F X).symm.leftAdjointMate := by rfl

/-- For the universal lift `lift fo fc`, whose unit, tensor and dual comparisons are identities,
the boundary isomorphism `mapObjIso` is the identity. -/
@[simp] theorem mapObjIso_lift (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon, RigidObject.eval fo (S.src g) ⟶ RigidObject.eval fo (S.tgt g))
    (X : RigidObject S.Obj) :
    mapObjIso (lift fo fc) X = Iso.refl (RigidObject.eval fo X) := by
  induction X with
  | of _ | unit => rfl
  | tensor _ _ ihX ihY =>
    ext; refine (mapObjIso_tensor_hom (lift fo fc) _ _).trans ?_
    rw [ihX, ihY, Iso.refl_hom, Iso.refl_hom, lift_δ]
    exact (Category.id_comp _).trans (id_tensorHom_id _ _)
  | rightDual X ih =>
    ext; erw [mapObjIso_rightDual, lift_mapRightDualIso, ih, Iso.trans_hom, Iso.refl_hom,
      Category.id_comp, Iso.rightAdjointMate_hom, Iso.symm_hom, Iso.refl_inv]
    exact rightAdjointMate_id
  | leftDual X ih =>
    ext; erw [mapObjIso_leftDual, lift_mapLeftDualIso, ih, Iso.trans_hom, Iso.refl_hom,
      Category.id_comp, Iso.leftAdjointMate_hom, Iso.symm_hom, Iso.refl_inv]
    exact leftAdjointMate_id

/-- The isomorphism `objIso F G e` factors through the boundary comparisons `mapObjIso` and
`RigidObject.evalIso e`. -/
theorem objIso_eq_mapObjIso (F G : S.FreeRigid ⥤ D) [F.Monoidal] [G.Monoidal]
    (e : ∀ a, F.obj (of a) ≅ G.obj (of a)) (X : RigidObject S.Obj) :
    objIso F G e X = mapObjIso F X ≪≫ RigidObject.evalIso e X ≪≫ (mapObjIso G X).symm := by
  induction X with
  | of a =>
    ext; refine (congrArg Iso.hom (objIso_of F G e a)).trans ?_
    change (e a).hom = 𝟙 (F.obj (of a)) ≫ (e a).hom ≫ 𝟙 (G.obj (of a))
    rw [Category.id_comp, Category.comp_id]
  | unit =>
    ext; refine (objIso_tensorUnit_hom F G e).trans ?_
    change η F ≫ ε G = η F ≫ 𝟙 (𝟙_ D) ≫ ε G; rw [Category.id_comp]
  | tensor X Y hX hY =>
    ext; refine (objIso_tensor_hom F G e ⟨X⟩ ⟨Y⟩).trans ?_
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]; dsimp only [RigidObject.eval]
    rw [mapObjIso_tensor_hom, mapObjIso_tensor_inv, RigidObject.evalIso_tensor, tensorIso_hom,
      hX, hY]
    simp only [Iso.trans_hom, Iso.symm_hom, ← MonoidalCategory.tensorHom_comp_tensorHom,
      Category.assoc]
  | rightDual X hX =>
    ext; refine (objIso_rightDual_hom F G e ⟨X⟩).trans ?_
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]; dsimp only [RigidObject.eval]
    rw [mapObjIso_rightDual, mapObjIso_rightDual, RigidObject.evalIso_rightDual, Iso.trans_hom,
      Iso.trans_inv, ← Category.assoc, ← Category.assoc, Iso.eq_comp_inv]
    refine ExactPairing.rightHom_ext (X := G.obj ⟨X⟩) (Y := (G.obj ⟨X⟩)ᘁ) ?_
    have hinv : (objIso F G e X).inv =
        (mapObjIso G X).hom ≫ (RigidObject.evalIso e X).inv ≫ (mapObjIso F X).inv := by
      rw [hX]; simp
    rw [comp_whiskerRight, Category.assoc, G.mapRightDualIso_hom_whiskerRight_evaluation ⟨X⟩,
      ← Functor.mapExactPairing_evaluation (F := G) ⟨X⟩ (⟨X⟩ᘁ),
      ExactPairing.rightMate_comp_evaluation, hinv]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Iso.rightAdjointMate_hom, Iso.rightAdjointMate_inv, Iso.symm_inv, Iso.symm_hom]
    rw [rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
      F.mapRightDualIso_hom_whiskerRight_evaluation ⟨X⟩,
      ← Functor.mapExactPairing_evaluation (F := F) ⟨X⟩ (⟨X⟩ᘁ)]
  | leftDual X hX =>
    ext; refine (objIso_leftDual_hom F G e ⟨X⟩).trans ?_
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]; dsimp only [RigidObject.eval]
    rw [mapObjIso_leftDual, mapObjIso_leftDual, RigidObject.evalIso_leftDual, Iso.trans_hom,
      Iso.trans_inv, ← Category.assoc, ← Category.assoc, Iso.eq_comp_inv]
    refine ExactPairing.leftDualHom_ext (X := ᘁ(G.obj ⟨X⟩)) (Y := G.obj ⟨X⟩) ?_
    have hinv : (objIso F G e X).inv =
        (mapObjIso G X).hom ≫ (RigidObject.evalIso e X).inv ≫ (mapObjIso F X).inv := by
      rw [hX]; simp
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      G.whiskerLeft_mapLeftDualIso_hom_evaluation ⟨X⟩,
      ← Functor.mapExactPairing_evaluation (F := G) (ᘁ⟨X⟩) ⟨X⟩,
      ExactPairing.leftMate_comp_evaluation, hinv]
    simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc,
      Iso.leftAdjointMate_hom, Iso.leftAdjointMate_inv, Iso.symm_inv, Iso.symm_hom]
    rw [leftAdjointMate_comp_evaluation, whisker_exchange_assoc, whisker_exchange_assoc,
      whisker_exchange_assoc, leftAdjointMate_comp_evaluation, whisker_exchange_assoc,
      whisker_exchange_assoc, leftAdjointMate_comp_evaluation, whisker_exchange_assoc,
      F.whiskerLeft_mapLeftDualIso_hom_evaluation ⟨X⟩,
      ← Functor.mapExactPairing_evaluation (F := F) (ᘁ⟨X⟩) ⟨X⟩]

@[simp] theorem objIso_lift_lift {fo fo' : S.Obj → D}
    (fc : ∀ g : S.Coupon, RigidObject.eval fo (S.src g) ⟶ RigidObject.eval fo (S.tgt g))
    (fc' : ∀ g : S.Coupon, RigidObject.eval fo' (S.src g) ⟶ RigidObject.eval fo' (S.tgt g))
    (e : ∀ a, fo a ≅ fo' a) (X : RigidObject S.Obj) :
    objIso (lift fo fc) (lift fo' fc') e X = RigidObject.evalIso e X := by
  refine (objIso_eq_mapObjIso (lift fo fc) (lift fo' fc') e X).trans ?_
  rw [mapObjIso_lift, mapObjIso_lift]; erw [Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]; rfl

theorem objIso_lift_refl (F : S.FreeRigid ⥤ D) [F.Monoidal]
    (fc : ∀ g : S.Coupon, RigidObject.eval (fun a ↦ F.obj (of a)) (S.src g) ⟶
      RigidObject.eval (fun a ↦ F.obj (of a)) (S.tgt g)) (X : RigidObject S.Obj) :
    objIso (lift (fun a ↦ F.obj (of a)) fc) F (fun a ↦ Iso.refl (F.obj (of a))) X =
      (mapObjIso F X).symm := by
  refine (objIso_eq_mapObjIso (lift _ fc) F _ X).trans ?_
  erw [mapObjIso_lift, RigidObject.evalIso_refl, Iso.refl_trans, Iso.refl_trans]

theorem evalIso_app {F G : S.FreeRigid ⥤ D} [F.Monoidal] [G.Monoidal] (α : F ≅ G)
    [NatTrans.IsMonoidal α.hom] (X : RigidObject S.Obj) :
    RigidObject.evalIso (fun a ↦ α.app (of a)) X =
      (mapObjIso F X).symm ≪≫ α.app ⟨X⟩ ≪≫ mapObjIso G X := by
  rw [← objIso_app α X, objIso_eq_mapObjIso]; ext; simp

end MapObjIso

end FreeRigid

section Interpretation

variable (S : DualitySignature.{u, v}) (D : Type u') [Category.{v'} D] [MonoidalCategory D]
  [RigidCategory D]

/-- An interpretation of a duality signature `S` in a rigid monoidal category `D`: an object of
`D` for every generating object and, for every coupon, a morphism between the evaluations of its
source and target rigid expressions. -/
structure Interpretation where
  /-- The interpretations of the generating objects. -/
  obj : S.Obj → D
  /-- The interpretations of the coupons. -/
  coupon (g : S.Coupon) : RigidObject.eval obj (S.src g) ⟶ RigidObject.eval obj (S.tgt g)

namespace Interpretation

variable {S D}

/-- A morphism of interpretations: isomorphisms of the interpretations of the generating objects
which commute with the interpretations of the coupons after extension by `RigidObject.evalIso`. -/
@[ext]
structure Hom (I J : Interpretation S D) where
  /-- The isomorphisms between the interpretations of the generating objects. -/
  iso (a : S.Obj) : I.obj a ≅ J.obj a
  /-- Compatibility with the coupons. -/
  comm (g : S.Coupon) : I.coupon g ≫ (RigidObject.evalIso iso (S.tgt g)).hom =
    (RigidObject.evalIso iso (S.src g)).hom ≫ J.coupon g

/-- The groupoid of interpretations of `S` in `D`. -/
noncomputable instance : Groupoid (Interpretation S D) where
  Hom := Hom
  id I := ⟨fun a ↦ Iso.refl (I.obj a), fun g ↦ by simp⟩
  comp φ ψ := ⟨fun a ↦ φ.iso a ≪≫ ψ.iso a, fun g ↦ by simp [reassoc_of% φ.comm, ψ.comm]⟩
  inv φ := ⟨fun a ↦ (φ.iso a).symm, fun g ↦ by
    rw [RigidObject.evalIso_symm, RigidObject.evalIso_symm, Iso.symm_hom, Iso.symm_hom,
      Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, φ.comm]⟩
  inv_comp φ := Hom.ext (funext fun a ↦ (φ.iso a).symm_self_id)
  comp_inv φ := Hom.ext (funext fun a ↦ (φ.iso a).self_symm_id)

@[ext] theorem hom_ext {I J : Interpretation S D} {φ ψ : I ⟶ J}
    (h : ∀ a, (φ.iso a).hom = (ψ.iso a).hom) : φ = ψ :=
  Hom.ext (funext fun a ↦ Iso.ext (h a))

@[simp] theorem id_iso (I : Interpretation S D) (a : S.Obj) :
    Hom.iso (𝟙 I) a = Iso.refl (I.obj a) := (rfl)
@[simp] theorem comp_iso {I J K : Interpretation S D} (φ : I ⟶ J) (ψ : J ⟶ K) (a : S.Obj) :
    (φ ≫ ψ).iso a = φ.iso a ≪≫ ψ.iso a := (rfl)
@[simp] theorem inv_iso {I J : Interpretation S D} (φ : I ⟶ J) (a : S.Obj) :
    (inv φ).iso a = (φ.iso a).symm := by rw [← Groupoid.inv_eq_inv]; rfl

open FreeRigid

theorem lift_map_coupon_comp_objIso_hom {I J : Interpretation S D} (φ : I ⟶ J) (g : S.Coupon) :
    (lift I.obj I.coupon).map (FreeRigid.coupon g) ≫
        (objIso (lift I.obj I.coupon) (lift J.obj J.coupon) φ.iso (S.tgt g)).hom =
      (objIso (lift I.obj I.coupon) (lift J.obj J.coupon) φ.iso (S.src g)).hom ≫
        (lift J.obj J.coupon).map (FreeRigid.coupon g) := by
  rw [objIso_lift_lift, objIso_lift_lift, lift_map_coupon, lift_map_coupon]; exact φ.comm g

variable (S D)

/-- Extension of interpretations of `S` to strong monoidal functors out of `S.FreeRigid` via
`FreeRigid.lift` and `FreeRigid.monoidalNatIso`. -/
@[expose, simps obj_of]
noncomputable def extension : Interpretation S D ⥤ Core (MonoidalFunctor S.FreeRigid D) where
  obj I := ⟨.of (lift I.obj I.coupon)⟩
  map φ := ⟨@MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) (.of _)
    (monoidalNatIso (lift_map_coupon_comp_objIso_hom φ))
    (isMonoidal_monoidalNatIso_hom (lift_map_coupon_comp_objIso_hom φ))⟩
  map_id _ := Core.hom_ext <| MonoidalFunctor.hom_ext <| natTrans_ext fun a ↦
    monoidalNatIso_hom_app_of _ a
  map_comp φ ψ := Core.hom_ext <| MonoidalFunctor.hom_ext <| natTrans_ext fun a ↦
    (monoidalNatIso_hom_app_of (lift_map_coupon_comp_objIso_hom (φ ≫ ψ)) a).trans <|
      congrArg₂ (· ≫ ·) (monoidalNatIso_hom_app_of (lift_map_coupon_comp_objIso_hom φ) a).symm
        (monoidalNatIso_hom_app_of (lift_map_coupon_comp_objIso_hom ψ) a).symm

variable {S D} in
@[simp] theorem extension_map_iso_hom_hom_hom_app_of {I J : Interpretation S D} (φ : I ⟶ J)
    (a : S.Obj) : ((extension S D).map φ).iso.hom.hom.hom.app (of a) = (φ.iso a).hom :=
  monoidalNatIso_hom_app_of (lift_map_coupon_comp_objIso_hom φ) a

/-- Restriction of strong monoidal functors out of `S.FreeRigid` to interpretations of `S`,
transporting coupons along `FreeRigid.mapObjIso`. -/
@[expose, simps obj_obj obj_coupon map_iso]
noncomputable def restriction : Core (MonoidalFunctor S.FreeRigid D) ⥤ Interpretation S D where
  obj F := { obj a := F.of.obj (of a)
             coupon g := (mapObjIso F.of.toFunctor (S.src g)).inv ≫
               F.of.map (FreeRigid.coupon g) ≫ (mapObjIso F.of.toFunctor (S.tgt g)).hom }
  map α := { iso a := (MonoidalFunctor.toFunctorIso α.iso).app (of a)
             comm g := by rw [evalIso_app, evalIso_app]; simp }
  map_id _ := hom_ext fun _ ↦ by simp
  map_comp _ _ := hom_ext fun _ ↦ by simp

variable {S D} in
/-- Restricting the extension of an interpretation gives back its coupons. -/
theorem restriction_obj_extension_obj_coupon (I : Interpretation S D) (g : S.Coupon) :
    ((restriction S D).obj ((extension S D).obj I)).coupon g = I.coupon g := by
  change (mapObjIso (lift I.obj I.coupon) (S.src g)).inv ≫ (lift I.obj I.coupon).map
    (FreeRigid.coupon g) ≫ (mapObjIso (lift I.obj I.coupon) (S.tgt g)).hom = I.coupon g
  rw [mapObjIso_lift, mapObjIso_lift, lift_map_coupon, Iso.refl_inv, Iso.refl_hom]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The unit of the equivalence: restricting the extension of an interpretation recovers it. -/
noncomputable def unitIso : 𝟭 (Interpretation S D) ≅ extension S D ⋙ restriction S D :=
  NatIso.ofComponents (fun I ↦ (Groupoid.isoEquivHom _ _).symm ⟨fun a ↦ Iso.refl (I.obj a),
    fun g ↦ by
      have h (X : RigidObject S.Obj) : (RigidObject.evalIso (g := ((restriction S D).obj
          ((extension S D).obj I)).obj) (fun a ↦ Iso.refl (I.obj a)) X).hom =
          𝟙 (RigidObject.eval I.obj X) := congrArg Iso.hom (RigidObject.evalIso_refl X)
      dsimp only [Functor.id_obj, Functor.comp_obj]
      rw [restriction_obj_extension_obj_coupon, h, h]
      exact (Category.comp_id _).trans (Category.id_comp _).symm⟩)
    fun φ ↦ hom_ext fun a ↦ by
      change (φ.iso a).hom ≫ 𝟙 _ = 𝟙 _ ≫ ((extension S D).map φ).iso.hom.hom.hom.app (of a)
      rw [Category.comp_id, Category.id_comp, extension_map_iso_hom_hom_hom_app_of]

variable {S D} in
@[simp] theorem unitIso_hom_app_iso (I : Interpretation S D) (a : S.Obj) :
    ((unitIso S D).hom.app I).iso a = Iso.refl (I.obj a) := (rfl)

variable {S D} in
private theorem lift_map_coupon_comp_objIso_refl_hom (F : S.FreeRigid ⥤ D) [F.Monoidal]
    (g : S.Coupon) :
    let F' := lift (fun a ↦ F.obj (of a)) fun g ↦
      (mapObjIso F (S.src g)).inv ≫ F.map (FreeRigid.coupon g) ≫ (mapObjIso F (S.tgt g)).hom
    F'.map (FreeRigid.coupon g) ≫ (objIso F' F (fun a ↦ Iso.refl (F.obj (of a))) (S.tgt g)).hom =
      (objIso F' F (fun a ↦ Iso.refl (F.obj (of a))) (S.src g)).hom ≫
        F.map (FreeRigid.coupon g) := by
  intro F'; rw [← Iso.eq_comp_inv, Category.assoc, objIso_lift_refl, objIso_lift_refl]
  exact lift_map_coupon _ _ g

variable {S D} in
private noncomputable def counitApp (F : Core (MonoidalFunctor S.FreeRigid D)) :
    (extension S D).obj ((restriction S D).obj F) ≅ F :=
  Core.isoMk <| @MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) F.of
    (monoidalNatIso (lift_map_coupon_comp_objIso_refl_hom F.of.toFunctor))
    (isMonoidal_monoidalNatIso_hom (lift_map_coupon_comp_objIso_refl_hom F.of.toFunctor))

/-- The counit of the equivalence: the extension of the restriction of a strong monoidal functor
is isomorphic to it via the identities at the generating objects. -/
noncomputable def counitIso :
    restriction S D ⋙ extension S D ≅ 𝟭 (Core (MonoidalFunctor S.FreeRigid D)) :=
  NatIso.ofComponents counitApp fun α ↦ Core.hom_ext <| MonoidalFunctor.hom_ext <|
    natTrans_ext fun a ↦ by
      have h (F : Core (MonoidalFunctor S.FreeRigid D)) : (counitApp F).hom.iso.hom.hom.hom.app
          (of a) = 𝟙 (F.of.obj (of a)) :=
        monoidalNatIso_hom_app_of (lift_map_coupon_comp_objIso_refl_hom F.of.toFunctor) a
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, coreCategory_comp_iso,
        Iso.trans_hom, MonoidalFunctor.comp_hom, LaxMonoidalFunctor.comp_hom, NatTrans.comp_app,
        extension_map_iso_hom_hom_hom_app_of, restriction_map_iso, Iso.app_hom,
        MonoidalFunctor.toFunctorIso_hom, Functor.id_map, h]
      exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {S D} in
@[simp] theorem counitIso_hom_app_iso_hom_hom_hom_app_of
    (F : Core (MonoidalFunctor S.FreeRigid D)) (a : S.Obj) :
    ((counitIso S D).hom.app F).iso.hom.hom.hom.app (of a) = 𝟙 (F.of.obj (of a)) :=
  monoidalNatIso_hom_app_of (lift_map_coupon_comp_objIso_refl_hom F.of.toFunctor) a

/-- **The universal property of the free rigid category on a duality signature**: groupoid
equivalence between `Interpretation S D` and strong monoidal functors `S.FreeRigid ⥤ D`. -/
@[expose, simps functor inverse unitIso counitIso]
noncomputable def equivCoreMonoidalFunctor :
    Interpretation S D ≌ Core (MonoidalFunctor S.FreeRigid D) where
  functor := extension S D; inverse := restriction S D
  unitIso := unitIso S D; counitIso := counitIso S D
  functor_unitIso_comp F := Core.hom_ext <| MonoidalFunctor.hom_ext <| natTrans_ext fun a ↦ by
    simp only [coreCategory_comp_iso, Iso.trans_hom, MonoidalFunctor.comp_hom,
      LaxMonoidalFunctor.comp_hom, NatTrans.comp_app, extension_map_iso_hom_hom_hom_app_of,
      unitIso_hom_app_iso, Iso.refl_hom, counitIso_hom_app_iso_hom_hom_hom_app_of,
      coreCategory_id_iso, MonoidalFunctor.id_hom, LaxMonoidalFunctor.id_hom, NatTrans.id_app]
    exact Category.id_comp _

end Interpretation

end Interpretation

end TauCeti.DualitySignature
