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

Substitutions compose: `Substitution.comp σ τ` substitutes `τ` into the replacements chosen by
`σ`, and `Substitution.id S` replaces every generator by itself. On raw expressions,
`FreeMonoidal.Hom.subst_subst_heq` and `FreeMonoidal.Hom.subst_substitutionId_heq` show that
substituting `σ` and then `τ` is substituting `σ.comp τ`, and that the identity substitution
changes nothing. These are heterogeneous equalities, because the boundary words agree only up to
the propositional identifications `FreeMonoidal.projectObj_projectObj` and
`FreeMonoidal.projectObj_of` of their interpretations. Consequently composition of substitutions
is associative with the identity substitution as a two-sided unit (`Substitution.comp_assoc`,
`Substitution.id_comp`, `Substitution.comp_id`), and the induced functors satisfy
`Substitution.toFunctor_comp` and `Substitution.toFunctor_id`.

The syntax and soundness argument use the constructors of `TensorSignature.FreeMonoidal`
and follow its interpretation construction. The mathematical setting is Joyal–Street,
*The geometry of tensor calculus I*, §1 (tensor schemes and their interpretations).
-/

public section

universe u v u' v' u'' v'' u''' v'''

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
  | _, _, .comp f g => (Hom.subst σ f).comp (Hom.subst σ g)
  | _, _, .whiskerLeft X f => (Hom.subst σ f).whiskerLeft (projectObj σ.obj X).as
  | _, _, .whiskerRight f X => (Hom.subst σ f).whiskerRight (projectObj σ.obj X).as
  | _, _, .tensor f g => (Hom.subst σ f).tensor (Hom.subst σ g)

@[simp]
theorem Hom.subst_id (σ : Substitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.id X) = MonoidalCore.Hom.id (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_coupon (σ : Substitution S T) (g : S.Coupon) :
    Hom.subst σ (Hom.coupon g) = σ.coupon g := by rfl

@[simp]
theorem Hom.subst_comp (σ : Substitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    Hom.subst σ (f.comp g) = (Hom.subst σ f).comp (Hom.subst σ g) := by rfl

@[simp]
theorem Hom.subst_tensor (σ : Substitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    Hom.subst σ (f.tensor g) = (Hom.subst σ f).tensor (Hom.subst σ g) := by rfl

@[simp]
theorem Hom.subst_whiskerLeft (σ : Substitution S T) (X) {Y Z} (f : Hom Y Z) :
    Hom.subst σ (f.whiskerLeft X) = (Hom.subst σ f).whiskerLeft (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_whiskerRight (σ : Substitution S T) {Y Z} (f : Hom Y Z) (X) :
    Hom.subst σ (f.whiskerRight X) = (Hom.subst σ f).whiskerRight (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_α_hom (σ : Substitution S T) (X Y Z) :
    Hom.subst σ (MonoidalCore.Hom.α_hom X Y Z) =
      MonoidalCore.Hom.α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
        (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_α_inv (σ : Substitution S T) (X Y Z) :
    Hom.subst σ (MonoidalCore.Hom.α_inv X Y Z) =
      MonoidalCore.Hom.α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as
        (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_l_hom (σ : Substitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.l_hom X) =
      MonoidalCore.Hom.l_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_l_inv (σ : Substitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.l_inv X) =
      MonoidalCore.Hom.l_inv (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_hom (σ : Substitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.ρ_hom X) =
      MonoidalCore.Hom.ρ_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_inv (σ : Substitution S T) (X) :
    Hom.subst σ (MonoidalCore.Hom.ρ_inv X) =
      MonoidalCore.Hom.ρ_inv (projectObj σ.obj X).as := by rfl

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
theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ :=
  FreeMonoidal.lift_ε _ _

@[simp]
theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ :=
  FreeMonoidal.lift_η _ _

@[simp]
theorem toFunctor_μ (X Y : S.FreeMonoidal) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ :=
  FreeMonoidal.lift_μ _ _ X Y

@[simp]
theorem toFunctor_δ (X Y : S.FreeMonoidal) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ :=
  FreeMonoidal.lift_δ _ _ X Y

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
      FreeMonoidal.homMk (Hom.subst σ f) := by
  -- The lift's interpreter is opaque in this module, so use its computation lemmas.
  -- The `homMk` structural generators and the wrapped interpreted endpoints are
  -- definitionally the corresponding native categorical objects and morphisms.
  induction f with
  | id X => exact (lift σ.obj _).map_id ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | gen g => cases g with | coupon g => exact lift_map_coupon _ _ g
  | comp f g hf hg =>
    exact ((lift σ.obj _).map_comp (homMk f) (homMk g)).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X f hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ (homMk f)).trans
      (congrArg (projectObj σ.obj X ◁ ·) hf)
  | whiskerRight f X hf =>
    exact (lift_map_whiskerRight _ _ (homMk f) ⟨X⟩).trans
      (congrArg (· ▷ projectObj σ.obj X) hf)
  | tensor f g hf hg =>
    exact (lift_map_tensorHom _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

end Substitution

namespace FreeMonoidal

/-- Substitution preserves the relation generated by the monoidal-category axioms.
No equation between the replacing coupons is required. -/
theorem HomEquiv.subst (σ : Substitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (Hom.subst σ f) (Hom.subst σ g) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeMonoidal

namespace Substitution

open FreeMonoidal

/-- Two substitutions are equal if they replace each generating object by the same tensor
expression and each coupon by the same raw expression. The replacing expressions are compared
heterogeneously, coupon by coupon, since their types depend on the replacing object expressions;
this is a pointwise form of `Substitution.ext`. -/
theorem hext {σ σ' : Substitution S T} (hobj : σ.obj = σ'.obj)
    (hcoupon : ∀ g, σ.coupon g ≍ σ'.coupon g) : σ = σ' := by
  obtain ⟨obj, coupon⟩ := σ
  obtain ⟨obj', coupon'⟩ := σ'
  subst hobj
  congr
  funext g
  exact eq_of_heq (hcoupon g)

variable (S) in
/-- The identity substitution, replacing each generating object and each coupon of `S` by
itself. -/
def id : Substitution S S where
  obj := FreeMonoidal.of
  coupon g := cast (by rw [FreeMonoidal.projectObj_of, FreeMonoidal.projectObj_of])
    (Hom.coupon g)

@[simp]
theorem id_obj : (Substitution.id S).obj = FreeMonoidal.of := (rfl)

/-- The identity substitution replaces a coupon by the coupon itself, up to the identification
of each word with its interpretation by its own generating objects (`projectObj_of`). -/
theorem id_coupon_heq (g : S.Coupon) : (Substitution.id S).coupon g ≍ Hom.coupon g :=
  cast_heq _ _

variable {U : TensorSignature.{u'', v''}}

/-- The composite of the substitutions `σ` and `τ`: each generating object and each coupon of
`S` is replaced by its replacement under `σ`, into which `τ` is substituted. The order is
diagrammatic, as for `Functor.comp`: `σ` is applied first (`Substitution.toFunctor_comp`). -/
def comp (σ : Substitution S T) (τ : Substitution T U) : Substitution S U where
  obj a := projectObj τ.obj (σ.obj a).as
  coupon g :=
    cast (by rw [FreeMonoidal.projectObj_projectObj, FreeMonoidal.projectObj_projectObj])
      (Hom.subst τ (σ.coupon g))

@[simp]
theorem comp_obj (σ : Substitution S T) (τ : Substitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = projectObj τ.obj (σ.obj a).as :=
  (rfl)

/-- The composite substitution replaces a coupon by the substitution of `τ` into its replacement
under `σ`, up to the identification of the boundary words given by `projectObj_projectObj`. -/
theorem comp_coupon_heq (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g ≍ Hom.subst τ (σ.coupon g) :=
  cast_heq _ _

end Substitution

namespace FreeMonoidal

/-- Substituting into heterogeneously equal raw expressions gives heterogeneously equal
results. -/
theorem Hom.subst_congr_heq (σ : Substitution S T) {X X' Y Y' : FreeMonoidalCategory S.Obj}
    {f : Hom X Y} {f' : Hom X' Y'} (hX : X = X') (hY : Y = Y') (h : f ≍ f') :
    Hom.subst σ f ≍ Hom.subst σ f' := by
  subst hX hY
  rw [eq_of_heq h]

/-! The constructors of raw expressions respect heterogeneous equality, given equal words. -/

private theorem α_hom_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') :
    (MonoidalCore.Hom.α_hom X Y Z : Hom (S := S) _ _) ≍
      (MonoidalCore.Hom.α_hom X' Y' Z' : Hom (S := S) _ _) := by
  subst hX hY hZ
  rfl

private theorem α_inv_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') :
    (MonoidalCore.Hom.α_inv X Y Z : Hom (S := S) _ _) ≍
      (MonoidalCore.Hom.α_inv X' Y' Z' : Hom (S := S) _ _) := by
  subst hX hY hZ
  rfl

private theorem comp_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} {f : Hom X Y}
    {f' : Hom X' Y'} {g : Hom Y Z} {g' : Hom Y' Z'} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (hf : f ≍ f') (hg : g ≍ g') : f.comp g ≍ f'.comp g' := by
  subst hX hY hZ
  rw [eq_of_heq hf, eq_of_heq hg]

private theorem whiskerLeft_heq {X X' Y₁ Y₁' Y₂ Y₂' : FreeMonoidalCategory S.Obj}
    {f : Hom Y₁ Y₂} {f' : Hom Y₁' Y₂'} (hX : X = X') (h₁ : Y₁ = Y₁') (h₂ : Y₂ = Y₂')
    (hf : f ≍ f') : f.whiskerLeft X ≍ f'.whiskerLeft X' := by
  subst hX h₁ h₂
  rw [eq_of_heq hf]

private theorem whiskerRight_heq {X₁ X₁' X₂ X₂' Y Y' : FreeMonoidalCategory S.Obj}
    {f : Hom X₁ X₂} {f' : Hom X₁' X₂'} (h₁ : X₁ = X₁') (h₂ : X₂ = X₂') (hY : Y = Y')
    (hf : f ≍ f') : f.whiskerRight Y ≍ f'.whiskerRight Y' := by
  subst h₁ h₂ hY
  rw [eq_of_heq hf]

private theorem tensor_heq {W W' X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} {f : Hom W Y}
    {f' : Hom W' Y'} {g : Hom X Z} {g' : Hom X' Z'} (hW : W = W') (hX : X = X') (hY : Y = Y')
    (hZ : Z = Z') (hf : f ≍ f') (hg : g ≍ g') : f.tensor g ≍ f'.tensor g' := by
  subst hW hX hY hZ
  rw [eq_of_heq hf, eq_of_heq hg]

private theorem homMk_heq {X X' Y Y' : FreeMonoidalCategory S.Obj} {f : Hom X Y}
    {f' : Hom X' Y'} (hX : X = X') (hY : Y = Y') (hf : f ≍ f') :
    homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f ≍ homMk (X := ⟨X'⟩) (Y := ⟨Y'⟩) f' := by
  subst hX hY
  rw [eq_of_heq hf]

/-- Substituting the identity substitution into a raw expression gives the expression itself, up
to the identification of each word with its interpretation by its own generating objects. -/
theorem Hom.subst_substitutionId_heq {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    Hom.subst (Substitution.id S) f ≍ f := by
  have h (X : FreeMonoidalCategory S.Obj) : (projectObj (Substitution.id S).obj X).as = X :=
    congrArg FreeMonoidal.as (projectObj_of X)
  induction f with
  | id X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.id Z : Hom (S := S) _ _)) (h X)
  | α_hom X Y Z => exact α_hom_heq (h X) (h Y) (h Z)
  | α_inv X Y Z => exact α_inv_heq (h X) (h Y) (h Z)
  | l_hom X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.l_hom Z : Hom (S := S) _ _)) (h X)
  | l_inv X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.l_inv Z : Hom (S := S) _ _)) (h X)
  | ρ_hom X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.ρ_hom Z : Hom (S := S) _ _)) (h X)
  | ρ_inv X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.ρ_inv Z : Hom (S := S) _ _)) (h X)
  | gen g => cases g with | coupon g => exact Substitution.id_coupon_heq g
  | comp f g hf hg => exact comp_heq (h _) (h _) (h _) hf hg
  | whiskerLeft X f hf => exact whiskerLeft_heq (h X) (h _) (h _) hf
  | whiskerRight f X hf => exact whiskerRight_heq (h _) (h _) (h X) hf
  | tensor f g hf hg => exact tensor_heq (h _) (h _) (h _) (h _) hf hg

variable {U : TensorSignature.{u'', v''}}

/-- Substituting `σ` and then `τ` into a raw expression is substituting their composite, up to
the identification of the boundary words given by `projectObj_projectObj`. -/
theorem Hom.subst_subst_heq (σ : Substitution S T) (τ : Substitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    Hom.subst τ (Hom.subst σ f) ≍ Hom.subst (σ.comp τ) f := by
  have h (X : FreeMonoidalCategory S.Obj) :
      (projectObj τ.obj (projectObj σ.obj X).as).as = (projectObj (σ.comp τ).obj X).as :=
    congrArg FreeMonoidal.as (projectObj_projectObj τ.obj σ.obj X)
  induction f with
  | id X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.id Z : Hom (S := U) _ _)) (h X)
  | α_hom X Y Z => exact α_hom_heq (h X) (h Y) (h Z)
  | α_inv X Y Z => exact α_inv_heq (h X) (h Y) (h Z)
  | l_hom X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.l_hom Z : Hom (S := U) _ _)) (h X)
  | l_inv X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.l_inv Z : Hom (S := U) _ _)) (h X)
  | ρ_hom X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.ρ_hom Z : Hom (S := U) _ _)) (h X)
  | ρ_inv X => exact congr_arg_heq (fun Z ↦ (MonoidalCore.Hom.ρ_inv Z : Hom (S := U) _ _)) (h X)
  | gen g => cases g with | coupon g => exact (Substitution.comp_coupon_heq σ τ g).symm
  | comp f g hf hg => exact comp_heq (h _) (h _) (h _) hf hg
  | whiskerLeft X f hf => exact whiskerLeft_heq (h X) (h _) (h _) hf
  | whiskerRight f X hf => exact whiskerRight_heq (h _) (h _) (h X) hf
  | tensor f g hf hg => exact tensor_heq (h _) (h _) (h _) (h _) hf hg

end FreeMonoidal

namespace Substitution

open FreeMonoidal

variable {U : TensorSignature.{u'', v''}}

/-- The identity substitution is a left unit for composition. -/
@[simp]
theorem id_comp (σ : Substitution S T) : (Substitution.id S).comp σ = σ :=
  hext rfl fun g ↦ (comp_coupon_heq _ σ g).trans
    (Hom.subst_congr_heq σ (congrArg FreeMonoidal.as (projectObj_of _))
      (congrArg FreeMonoidal.as (projectObj_of _)) (id_coupon_heq g))

/-- The identity substitution is a right unit for composition. -/
@[simp]
theorem comp_id (σ : Substitution S T) : σ.comp (Substitution.id T) = σ :=
  hext (funext fun _ ↦ projectObj_of _) fun g ↦
    (comp_coupon_heq σ _ g).trans (Hom.subst_substitutionId_heq _)

/-- Composition of substitutions is associative. -/
theorem comp_assoc {W : TensorSignature.{u''', v'''}} (σ : Substitution S T)
    (τ : Substitution T U) (ρ : Substitution U W) : (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) :=
  hext (funext fun a ↦ projectObj_projectObj ρ.obj τ.obj (σ.obj a).as) fun g ↦
    ((comp_coupon_heq _ ρ g).trans
      (Hom.subst_congr_heq ρ
        (congrArg FreeMonoidal.as (FreeMonoidal.projectObj_projectObj _ _ _)).symm
        (congrArg FreeMonoidal.as (FreeMonoidal.projectObj_projectObj _ _ _)).symm
        (comp_coupon_heq σ τ g))).trans
      ((Hom.subst_subst_heq τ ρ _).trans (comp_coupon_heq σ _ g).symm)

/-- The functor induced by the identity substitution is the identity functor. -/
@[simp]
theorem toFunctor_id : (Substitution.id S).toFunctor = 𝟭 S.FreeMonoidal := by
  refine Functor.hext (fun X ↦ projectObj_of X.as) fun ⟨X⟩ ⟨Y⟩ f ↦ ?_
  induction f using Quotient.inductionOn with | _ f
  exact ((Substitution.id S).toFunctor_map_homMk f).heq.trans
    (homMk_heq (congrArg FreeMonoidal.as (projectObj_of X))
      (congrArg FreeMonoidal.as (projectObj_of Y)) (Hom.subst_substitutionId_heq f))

/-- The functor induced by a composite substitution is the composite of the induced
functors. -/
@[simp]
theorem toFunctor_comp (σ : Substitution S T) (τ : Substitution T U) :
    (σ.comp τ).toFunctor = σ.toFunctor ⋙ τ.toFunctor := by
  refine Functor.hext (fun X ↦ (projectObj_projectObj τ.obj σ.obj X.as).symm)
    fun ⟨X⟩ ⟨Y⟩ f ↦ ?_
  induction f using Quotient.inductionOn with | _ f
  refine ((σ.comp τ).toFunctor_map_homMk f).heq.trans (HEq.trans ?_
    ((congrArg τ.toFunctor.map (σ.toFunctor_map_homMk f)).trans
      (τ.toFunctor_map_homMk _)).symm.heq)
  exact homMk_heq (congrArg FreeMonoidal.as (projectObj_projectObj τ.obj σ.obj X)).symm
    (congrArg FreeMonoidal.as (projectObj_projectObj τ.obj σ.obj Y)).symm
    (Hom.subst_subst_heq σ τ f).symm

end Substitution

end TauCeti.TensorSignature
