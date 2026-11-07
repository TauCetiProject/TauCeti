/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic

/-!
# Substitution of tensor expressions for coupons

A `TensorSignature.Substitution S T` replaces object generators of `S` by tensor expressions
in `T` and coupons of `S` by raw morphism expressions in `T` with the resulting boundaries.
In particular, an object generator can be replaced by the unit or by a multi-letter expression;
a coupon is not replaced by a new unary generator on its entire boundary.

`FreeMonoidal.Hom.subst` performs this replacement before quotienting by the monoidal axioms.
`FreeMonoidal.HomEquiv.subst` proves that it respects those axioms. The strong monoidal functor
`Substitution.toFunctor` is the existing universal lift, and `Substitution.toFunctor_map_homMk`
identifies its action with raw substitution. Thus substitution can be used either on raw terms
or on their equivalence classes, without choosing representatives.

The syntax and soundness argument use the constructors of `TensorSignature.FreeMonoidal`
and follow its interpretation construction. The mathematical setting is Joyal–Street,
*The geometry of tensor calculus I*, §1 (tensor schemes and their interpretations).
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

/-- A typed substitution between tensor signatures. Object generators are replaced by formal
tensor expressions, and coupons by raw expressions with the substituted source and target.
The object and coupon types of the two signatures need not have the same universes. -/
@[ext]
structure Substitution (S : TensorSignature.{u, v}) (T : TensorSignature.{u', v'}) where
  /-- The tensor expression replacing each object generator. -/
  obj : S.Obj → T.FreeMonoidal
  /-- The raw expression replacing each coupon. -/
  coupon : ∀ g : S.Coupon, FreeMonoidal.Hom
    (projectObj obj (S.src g)).as (projectObj obj (S.tgt g)).as

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}

namespace FreeMonoidal

/-- Substitute tensor expressions for object generators and raw expressions for coupons.
The endpoints are interpreted by the native tensor-word interpreter `projectObj`. -/
def Hom.subst (σ : Substitution S T) : ∀ {X Y}, Hom X Y →
    Hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .id X => .id (projectObj σ.obj X).as
  | _, _, .α_hom X Y Z => .α_hom (projectObj σ.obj X).as
      (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .α_inv X Y Z => .α_inv (projectObj σ.obj X).as
      (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .l_hom X => .l_hom (projectObj σ.obj X).as
  | _, _, .l_inv X => .l_inv (projectObj σ.obj X).as
  | _, _, .ρ_hom X => .ρ_hom (projectObj σ.obj X).as
  | _, _, .ρ_inv X => .ρ_inv (projectObj σ.obj X).as
  | _, _, .coupon g => σ.coupon g
  | _, _, .comp f g => (f.subst σ).comp (g.subst σ)
  | _, _, .whiskerLeft X f => (f.subst σ).whiskerLeft (projectObj σ.obj X).as
  | _, _, .whiskerRight f X => (f.subst σ).whiskerRight (projectObj σ.obj X).as
  | _, _, .tensor f g => (f.subst σ).tensor (g.subst σ)

@[simp]
theorem Hom.subst_id (σ : Substitution S T) (X) :
    (Hom.id X).subst σ = .id (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_coupon (σ : Substitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := by rfl

@[simp]
theorem Hom.subst_comp (σ : Substitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_tensor (σ : Substitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_whiskerLeft (σ : Substitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_whiskerRight (σ : Substitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_α_hom (σ : Substitution S T) (X Y Z) :
    (Hom.α_hom X Y Z).subst σ =
      .α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_α_inv (σ : Substitution S T) (X Y Z) :
    (Hom.α_inv X Y Z).subst σ =
      .α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_l_hom (σ : Substitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_l_inv (σ : Substitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_hom (σ : Substitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_inv (σ : Substitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (projectObj σ.obj X).as := by rfl

/-- Substitution preserves the relation generated by the monoidal-category axioms.
No equation between the replacing coupons is required. -/
theorem HomEquiv.subst (σ : Substitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) := by
  induction h with
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | whiskerLeft _ _ _ _ ih => exact .whiskerLeft _ _ _ ih
  | whiskerRight _ _ _ _ ih => exact .whiskerRight _ _ _ ih
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | tensorHom_def => exact .tensorHom_def _ _
  | comp_id => exact .comp_id _
  | id_comp => exact .id_comp _
  | assoc => exact .assoc _ _ _
  | id_tensorHom_id => exact .id_tensorHom_id
  | tensorHom_comp_tensorHom => exact .tensorHom_comp_tensorHom _ _ _ _
  | whiskerLeft_id => exact .whiskerLeft_id _ _
  | id_whiskerRight => exact .id_whiskerRight _ _
  | α_hom_inv => exact .α_hom_inv
  | α_inv_hom => exact .α_inv_hom
  | associator_naturality => exact .associator_naturality _ _ _
  | ρ_hom_inv => exact .ρ_hom_inv
  | ρ_inv_hom => exact .ρ_inv_hom
  | ρ_naturality => exact .ρ_naturality _
  | l_hom_inv => exact .l_hom_inv
  | l_inv_hom => exact .l_inv_hom
  | l_naturality => exact .l_naturality _
  | pentagon => exact .pentagon
  | triangle => exact .triangle

end FreeMonoidal

namespace Substitution

open FreeMonoidal

variable (σ : Substitution S T)

/-- The strong monoidal functor induced by a raw substitution. It is the universal lift
of the specified object expressions and the equivalence classes of the replacing coupons.
Its object action is exposed so that raw substituted expressions have the required endpoint
types in the representative computation rules. -/
@[expose] def toFunctor : S.FreeMonoidal ⥤ T.FreeMonoidal :=
  FreeMonoidal.lift σ.obj (fun g ↦ FreeMonoidal.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal := inferInstanceAs
  (FreeMonoidal.lift σ.obj (fun g ↦ FreeMonoidal.homMk (σ.coupon g))).Monoidal

@[simp]
theorem toFunctor_obj (X : S.FreeMonoidal) :
    σ.toFunctor.obj X = projectObj σ.obj X.as := by rfl

@[simp]
theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeMonoidal.coupon g) = FreeMonoidal.homMk (σ.coupon g) :=
  FreeMonoidal.lift_map_coupon _ _ g

/-- Interpreting a raw expression by the induced functor is the equivalence class of its
substitution. This is also the representative computation rule for the descended operation. -/
@[simp]
theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : FreeMonoidal.Hom X Y) :
    σ.toFunctor.map (FreeMonoidal.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeMonoidal.homMk (f.subst σ) := by
  -- The lift's interpreter is opaque in this module, so use its computation lemmas.
  -- The `homMk` structural generators and the wrapped interpreted endpoints are
  -- definitionally the corresponding native categorical objects and morphisms.
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | coupon g => exact lift_map_coupon _ _ g
  | comp f g hf hg =>
    exact (liftMap_comp _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X f hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ (homMk f)).trans
      (congrArg (projectObj σ.obj X ◁ ·) hf)
  | whiskerRight f X hf =>
    exact (lift_map_whiskerRight _ _ (homMk f) ⟨X⟩).trans
      (congrArg (· ▷ projectObj σ.obj X) hf)
  | tensor f g hf hg =>
    exact (lift_map_tensorHom _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

end Substitution

end TauCeti.TensorSignature
