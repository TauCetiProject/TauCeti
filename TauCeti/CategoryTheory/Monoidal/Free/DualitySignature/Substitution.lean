/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Substitution
public import TauCeti.CategoryTheory.Monoidal.Free.DualitySignature.Universal

/-!
# Substitution of rigid expressions for coupons

A `DualitySignature.Substitution S T` replaces object generators of `S` by objects of
`T.FreeRigid` and coupons of `S` by raw morphisms `FreeRigid.Hom` in `T`:

* `FreeRigid.eval_eq_subst`, `FreeRigid.as_eval_eq_subst`,
  `Substitution.normalize_toFunctor_obj_as`: identify categorical object evaluation with
  `RigidObject.subst` and `WindingWord.subst`.
* `FreeRigid.Hom.subst` and `FreeRigid.HomEquiv.subst`: typed substitution on raw morphism
  expressions respecting the monoidal and zigzag axioms without coupon equations.
* `Substitution.toFunctor` and `Substitution.toFunctor_map_homMk`: induced strong monoidal functor
  `S.FreeRigid ⥤ T.FreeRigid` via `FreeRigid.lift`, agreeing with raw substitution.

Parallels `TauCeti.TensorSignature.Substitution`, extended to right and left duals.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, unpublished manuscript (1988), §2.
-/

public section

universe u v u' v' w

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti.DualitySignature

/-- A typed substitution between duality signatures. Object generators of `S` are replaced by
formal rigid object expressions in `T`, and coupons of `S` are replaced by raw morphism expressions
with the substituted source and target boundaries. The universes of the two signatures are
independent. -/
@[ext]
structure Substitution (S : DualitySignature.{u, v}) (T : DualitySignature.{u', v'}) where
  /-- The formal rigid object expression replacing each generating object of `S`. -/
  obj : S.Obj → T.FreeRigid
  /-- The raw formal morphism expression replacing each coupon of `S`. -/
  coupon : ∀ g : S.Coupon, FreeRigid.Hom
    (RigidObject.eval obj (S.src g)).as (RigidObject.eval obj (S.tgt g)).as

variable {S : DualitySignature.{u, v}} {T : DualitySignature.{u', v'}}

namespace FreeRigid

/-- Interpreting a formal rigid object expression via `f : α → T.FreeRigid` wraps the syntactic
substitution `RigidObject.subst` of the underlying object expressions `(f a).as`. -/
theorem eval_eq_subst {α : Type w} (f : α → T.FreeRigid) (X : RigidObject α) :
    RigidObject.eval f X = ⟨RigidObject.subst (fun a ↦ (f a).as) X⟩ := by
  induction X with
  | of _ => rw [RigidObject.eval_of, RigidObject.subst_of]
  | unit => rw [RigidObject.eval_unit, RigidObject.subst_unit]; rfl
  | tensor _ _ ihX ihY => rw [RigidObject.eval_tensor, RigidObject.subst_tensor, ihX, ihY]; rfl
  | rightDual _ ih => rw [RigidObject.eval_rightDual, RigidObject.subst_rightDual, ih]; rfl
  | leftDual _ ih => rw [RigidObject.eval_leftDual, RigidObject.subst_leftDual, ih]; rfl

/-- Underlying `RigidObject` form of `eval_eq_subst`: categorical interpretation into
`T.FreeRigid` agrees with syntactic substitution `RigidObject.subst`. -/
theorem as_eval_eq_subst {α : Type w} (f : α → T.FreeRigid) (X : RigidObject α) :
    (RigidObject.eval f X).as = RigidObject.subst (fun a ↦ (f a).as) X :=
  congrArg FreeRigid.as (eval_eq_subst f X)

/-- Substitute formal rigid object expressions for object generators and raw morphism expressions
for coupons. Endpoints are interpreted by `RigidObject.eval`. -/
noncomputable def Hom.subst (σ : Substitution S T) : ∀ {X Y}, Hom X Y →
    Hom (RigidObject.eval σ.obj X).as (RigidObject.eval σ.obj Y).as
  | _, _, .id X => .id (RigidObject.eval σ.obj X).as
  | _, _, .α_hom X Y Z => .α_hom (RigidObject.eval σ.obj X).as
      (RigidObject.eval σ.obj Y).as (RigidObject.eval σ.obj Z).as
  | _, _, .α_inv X Y Z => .α_inv (RigidObject.eval σ.obj X).as
      (RigidObject.eval σ.obj Y).as (RigidObject.eval σ.obj Z).as
  | _, _, .l_hom X => .l_hom (RigidObject.eval σ.obj X).as
  | _, _, .l_inv X => .l_inv (RigidObject.eval σ.obj X).as
  | _, _, .ρ_hom X => .ρ_hom (RigidObject.eval σ.obj X).as
  | _, _, .ρ_inv X => .ρ_inv (RigidObject.eval σ.obj X).as
  | _, _, .rightCoevaluation X => .rightCoevaluation (RigidObject.eval σ.obj X).as
  | _, _, .rightEvaluation X => .rightEvaluation (RigidObject.eval σ.obj X).as
  | _, _, .leftCoevaluation X => .leftCoevaluation (RigidObject.eval σ.obj X).as
  | _, _, .leftEvaluation X => .leftEvaluation (RigidObject.eval σ.obj X).as
  | _, _, .coupon g => σ.coupon g
  | _, _, .comp f g => (f.subst σ).comp (g.subst σ)
  | _, _, .whiskerLeft X f => (f.subst σ).whiskerLeft (RigidObject.eval σ.obj X).as
  | _, _, .whiskerRight f X => (f.subst σ).whiskerRight (RigidObject.eval σ.obj X).as
  | _, _, .tensor f g => (f.subst σ).tensor (g.subst σ)

@[simp] theorem Hom.subst_id (σ : Substitution S T) (X) :
    (Hom.id X).subst σ = .id (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_coupon (σ : Substitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := by rfl
@[simp] theorem Hom.subst_comp (σ : Substitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := by rfl
@[simp] theorem Hom.subst_tensor (σ : Substitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := by rfl
@[simp] theorem Hom.subst_whiskerLeft (σ : Substitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_whiskerRight (σ : Substitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_α_hom (σ : Substitution S T) (X Y Z) : (Hom.α_hom X Y Z).subst σ =
    .α_hom (RigidObject.eval σ.obj X).as (RigidObject.eval σ.obj Y).as
      (RigidObject.eval σ.obj Z).as := by rfl
@[simp] theorem Hom.subst_α_inv (σ : Substitution S T) (X Y Z) : (Hom.α_inv X Y Z).subst σ =
    .α_inv (RigidObject.eval σ.obj X).as (RigidObject.eval σ.obj Y).as
      (RigidObject.eval σ.obj Z).as := by rfl
@[simp] theorem Hom.subst_l_hom (σ : Substitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_l_inv (σ : Substitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_ρ_hom (σ : Substitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_ρ_inv (σ : Substitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_rightCoevaluation (σ : Substitution S T) (X) :
    (Hom.rightCoevaluation X).subst σ = .rightCoevaluation (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_rightEvaluation (σ : Substitution S T) (X) :
    (Hom.rightEvaluation X).subst σ = .rightEvaluation (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_leftCoevaluation (σ : Substitution S T) (X) :
    (Hom.leftCoevaluation X).subst σ = .leftCoevaluation (RigidObject.eval σ.obj X).as := by rfl
@[simp] theorem Hom.subst_leftEvaluation (σ : Substitution S T) (X) :
    (Hom.leftEvaluation X).subst σ = .leftEvaluation (RigidObject.eval σ.obj X).as := by rfl

end FreeRigid

namespace Substitution

open FreeRigid

variable (σ : Substitution S T)

/-- The strong monoidal functor `S.FreeRigid ⥤ T.FreeRigid` induced by a raw substitution, defined
as the universal lift of `σ.obj` and the quotient morphisms of `σ.coupon`. Exposed on objects so
that dependent morphism types over substituted endpoints reduce on constructors. -/
@[expose] noncomputable def toFunctor : S.FreeRigid ⥤ T.FreeRigid :=
  FreeRigid.lift σ.obj (fun g ↦ FreeRigid.homMk (σ.coupon g))

noncomputable instance : σ.toFunctor.Monoidal :=
  inferInstanceAs (FreeRigid.lift σ.obj (fun g ↦ FreeRigid.homMk (σ.coupon g))).Monoidal

@[simp] theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ := FreeRigid.lift_ε _ _
@[simp] theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ := FreeRigid.lift_η _ _
@[simp] theorem toFunctor_μ (X Y : S.FreeRigid) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ := FreeRigid.lift_μ _ _ X Y
@[simp] theorem toFunctor_δ (X Y : S.FreeRigid) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ := FreeRigid.lift_δ _ _ X Y
@[simp] theorem toFunctor_mapRightDualIso (X : S.FreeRigid) :
    σ.toFunctor.mapRightDualIso X (_hFX := RightRigidCategory.rightDual (σ.toFunctor.obj X)) =
      Iso.refl _ := FreeRigid.lift_mapRightDualIso _ _ X
@[simp] theorem toFunctor_mapLeftDualIso (X : S.FreeRigid) :
    σ.toFunctor.mapLeftDualIso X (_hFY := LeftRigidCategory.leftDual (σ.toFunctor.obj X)) =
      Iso.refl _ := FreeRigid.lift_mapLeftDualIso _ _ X
@[simp] theorem toFunctor_obj (X : S.FreeRigid) :
    σ.toFunctor.obj X = RigidObject.eval σ.obj X.as := by rfl

theorem toFunctor_obj_as (X : S.FreeRigid) :
    (σ.toFunctor.obj X).as = RigidObject.subst (fun a ↦ (σ.obj a).as) X.as :=
  FreeRigid.as_eval_eq_subst σ.obj X.as

/-- Normalization of a substituted `FreeRigid` object agrees with winding-word substitution on the
normalized boundaries. -/
theorem normalize_toFunctor_obj_as (X : S.FreeRigid) :
    RigidObject.normalize (σ.toFunctor.obj X).as =
      WindingWord.subst (fun a ↦ RigidObject.normalize (σ.obj a).as)
        (RigidObject.normalize X.as) := by rw [σ.toFunctor_obj_as, RigidObject.normalize_subst]

@[simp] theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeRigid.coupon g) = FreeRigid.homMk (σ.coupon g) :=
  FreeRigid.lift_map_coupon _ _ g

/-- Interpreting a raw formal morphism expression via `σ.toFunctor` yields the equivalence class of
its raw substitution `f.subst σ`. -/
@[simp] theorem toFunctor_map_homMk {X Y : RigidObject S.Obj} (f : FreeRigid.Hom X Y) :
    σ.toFunctor.map (FreeRigid.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) = FreeRigid.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | rightCoevaluation X => exact lift_map_rightCoevaluation _ _ ⟨X⟩
  | rightEvaluation X => exact lift_map_rightEvaluation _ _ ⟨X⟩
  | leftCoevaluation X => exact lift_map_leftCoevaluation _ _ ⟨X⟩
  | leftEvaluation X => exact lift_map_leftEvaluation _ _ ⟨X⟩
  | coupon g => exact lift_map_coupon _ _ g
  | comp _ _ hf hg => exact (liftMap_comp _ _ _ _).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X _ hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ _).trans (congrArg (RigidObject.eval σ.obj X ◁ ·) hf)
  | whiskerRight _ X hf =>
    exact (lift_map_whiskerRight _ _ _ ⟨X⟩).trans (congrArg (· ▷ RigidObject.eval σ.obj X) hf)
  | tensor _ _ hf hg => exact (lift_map_tensorHom _ _ _ _).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

end Substitution

namespace FreeRigid

/-- Raw substitution preserves the congruence generated by the monoidal and zigzag axioms. No
equation between the replacing coupons is required. -/
theorem HomEquiv.subst (σ : Substitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) :=
  Quotient.exact (s := setoidHom _ _) <| (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeRigid

end TauCeti.DualitySignature
