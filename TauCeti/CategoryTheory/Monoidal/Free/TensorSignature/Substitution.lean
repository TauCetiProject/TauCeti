/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.EqToHom
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Coupons
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Hom
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Interpretation

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
`FreeMonoidal.Hom.subst_subst` (`subst_subst_heq`) and `FreeMonoidal.Hom.subst_substitutionId`
(`subst_substitutionId_heq`) show that substituting `σ` and then `τ` is substituting `σ.comp τ`,
and that the identity substitution changes nothing. Consequently composition of substitutions is
associative with the identity substitution as a two-sided unit (`Substitution.comp_assoc`,
`Substitution.id_comp`, `Substitution.comp_id`), and the induced functors satisfy
`Substitution.toFunctor_comp` and `Substitution.toFunctor_id`, as well as monoidal natural
isomorphisms `Substitution.toFunctorIdIso` and `Substitution.toFunctorCompIso` with unit and
associativity coherence laws.

Signature morphisms `TensorSignature.Hom` embed faithfully into substitutions via
`Hom.toSubstitution` compatibly with identities and composition. Composing a substitution with
a universal interpretation `FreeMonoidal.lift` in an arbitrary (not necessarily strict) monoidal
category is canonically monoidally isomorphic to the pulled-back lift
(`Substitution.toFunctorCompLiftIso`), and pullback acts functorially on the interpretation
groupoid (`Substitution.pullback`) naturally with respect to extension
(`Substitution.extensionPullbackIso`).

## Main definitions and results

* `TauCeti.TensorSignature.Substitution`: typed substitutions between tensor signatures across
  independent universes, with `Substitution.id`, `Substitution.comp`, `Substitution.id_comp`,
  `Substitution.comp_id`, and `Substitution.comp_assoc`.
* `TauCeti.TensorSignature.FreeMonoidal.Hom.subst`,
  `TauCeti.TensorSignature.FreeMonoidal.Hom.subst_substitutionId`, and
  `TauCeti.TensorSignature.FreeMonoidal.Hom.subst_subst`: raw expression substitution and its
  identity and composition laws.
* `TauCeti.TensorSignature.Hom.toSubstitution`, `TauCeti.TensorSignature.Hom.toFunctor`,
  `TauCeti.TensorSignature.Hom.toFunctor_injective`, `TauCeti.TensorSignature.Hom.toFunctorIdIso`,
  and `TauCeti.TensorSignature.Hom.toFunctorCompIso`: faithful functorial embedding of signature
  morphisms into substitutions and induced strong monoidal functors between free monoidal
  categories, with unit and associativity coherence laws.
* `TauCeti.TensorSignature.Substitution.toFunctor`,
  `TauCeti.TensorSignature.Substitution.toFunctor_id`,
  `TauCeti.TensorSignature.Substitution.toFunctor_comp`,
  `TauCeti.TensorSignature.Substitution.toFunctorIdIso`, and
  `TauCeti.TensorSignature.Substitution.toFunctorCompIso`: strong monoidal functoriality of
  substitution on free monoidal categories, with unit and associativity coherence laws.
* `TauCeti.TensorSignature.Substitution.pullbackObj`,
  `TauCeti.TensorSignature.Substitution.pullbackCoupon`,
  `TauCeti.TensorSignature.Substitution.pullback`,
  `TauCeti.TensorSignature.Substitution.toFunctorCompLiftIso`, and
  `TauCeti.TensorSignature.Substitution.extensionPullbackIso`: functorial change of signature on
  interpretations and naturality/coherence of the extension comparison.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1
  (tensor schemes and their interpretations).
-/

public section

universe u v u' v' u'' v'' u''' v''' u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

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

section RawSubst

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

@[simp] theorem Hom.subst_id (σ : Substitution S T) (X) :
    (Hom.id X).subst σ = .id (projectObj σ.obj X).as := by rfl

@[simp] theorem Hom.subst_coupon (σ : Substitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := by rfl

@[simp] theorem Hom.subst_comp (σ : Substitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := by rfl

@[simp] theorem Hom.subst_tensor (σ : Substitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := by rfl

@[simp] theorem Hom.subst_whiskerLeft (σ : Substitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (projectObj σ.obj X).as := by rfl

@[simp] theorem Hom.subst_whiskerRight (σ : Substitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (projectObj σ.obj X).as := by rfl

@[simp] theorem Hom.subst_α_hom (σ : Substitution S T) (X Y Z) :
    (Hom.α_hom X Y Z).subst σ =
      .α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp] theorem Hom.subst_α_inv (σ : Substitution S T) (X Y Z) :
    (Hom.α_inv X Y Z).subst σ =
      .α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp] theorem Hom.subst_l_hom (σ : Substitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (projectObj σ.obj X).as := by rfl

@[simp] theorem Hom.subst_l_inv (σ : Substitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (projectObj σ.obj X).as := by rfl

@[simp] theorem Hom.subst_ρ_hom (σ : Substitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (projectObj σ.obj X).as := by rfl

@[simp] theorem Hom.subst_ρ_inv (σ : Substitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (projectObj σ.obj X).as := by rfl

/-- Raw substitution commutes with endpoint casts. -/
@[simp]
theorem Hom.subst_cast (σ : Substitution S T) {X X' Y Y' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (f : Hom X Y) :
    (f.cast hX hY).subst σ =
      (f.subst σ).cast (congrArg (fun W ↦ (projectObj σ.obj W).as) hX)
        (congrArg (fun W ↦ (projectObj σ.obj W).as) hY) := by
  subst hX hY
  simp

private theorem Hom.eq_cast_of_heq {X X' Y Y' : FreeMonoidalCategory S.Obj}
    {f : Hom X Y} {f' : Hom X' Y'} (hX : X = X') (hY : Y = Y') (h : f' ≍ f) :
    f' = f.cast hX hY := by
  subst hX hY
  exact (eq_of_heq h).trans (Hom.cast_rfl f).symm

end FreeMonoidal

end RawSubst

namespace Substitution

open FreeMonoidal

section ToFunctor

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}} (σ : Substitution S T)

/-- The strong monoidal functor induced by a raw substitution. It is the universal lift
of the specified object expressions and the equivalence classes of the replacing coupons.
Its object action is exposed so that raw substituted expressions have the required endpoint
types in the representative computation rules. -/
@[expose] def toFunctor : S.FreeMonoidal ⥤ T.FreeMonoidal :=
  FreeMonoidal.lift σ.obj (fun g ↦ FreeMonoidal.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal := inferInstanceAs
  (FreeMonoidal.lift σ.obj (fun g ↦ FreeMonoidal.homMk (σ.coupon g))).Monoidal

@[simp]
theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ := FreeMonoidal.lift_ε _ _

@[simp]
theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ := FreeMonoidal.lift_η _ _

@[simp]
theorem toFunctor_μ (X Y : S.FreeMonoidal) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ := FreeMonoidal.lift_μ _ _ X Y

@[simp]
theorem toFunctor_δ (X Y : S.FreeMonoidal) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ := FreeMonoidal.lift_δ _ _ X Y

@[simp]
theorem toFunctor_obj (X : S.FreeMonoidal) :
    σ.toFunctor.obj X = projectObj σ.obj X.as := rfl

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

end ToFunctor

end Substitution

namespace FreeMonoidal

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}

/-- Substitution preserves the relation generated by the monoidal-category axioms.
No equation between the replacing coupons is required. -/
theorem HomEquiv.subst (σ : Substitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeMonoidal

namespace Substitution

open FreeMonoidal

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}

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
    (FreeMonoidal.Hom.coupon g)

@[simp]
theorem id_obj : (Substitution.id S).obj = FreeMonoidal.of := (rfl)

/-- The identity substitution replaces a coupon by the coupon itself, up to the identification
of each word with its interpretation by its own generating objects (`projectObj_of`). -/
theorem id_coupon_heq (g : S.Coupon) :
    (Substitution.id S).coupon g ≍ FreeMonoidal.Hom.coupon g :=
  cast_heq _ _

variable {U : TensorSignature.{u'', v''}}

/-- The composite of the substitutions `σ` and `τ`: each generating object and each coupon of
`S` is replaced by its replacement under `σ`, into which `τ` is substituted. The order is
diagrammatic, as for `Functor.comp`: `σ` is applied first (`Substitution.toFunctor_comp`). -/
def comp (σ : Substitution S T) (τ : Substitution T U) : Substitution S U where
  obj a := projectObj τ.obj (σ.obj a).as
  coupon g :=
    cast (by rw [FreeMonoidal.projectObj_projectObj, FreeMonoidal.projectObj_projectObj])
      ((σ.coupon g).subst τ)

@[simp]
theorem comp_obj (σ : Substitution S T) (τ : Substitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = projectObj τ.obj (σ.obj a).as :=
  (rfl)

/-- The composite substitution replaces a coupon by the substitution of `τ` into its replacement
under `σ`, up to the identification of the boundary words given by `projectObj_projectObj`. -/
theorem comp_coupon_heq (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g ≍ (σ.coupon g).subst τ :=
  cast_heq _ _

end Substitution

namespace FreeMonoidal

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}

/-- Substituting into heterogeneously equal raw expressions gives heterogeneously equal
results. -/
theorem Hom.subst_congr_heq (σ : Substitution S T) {X X' Y Y' : FreeMonoidalCategory S.Obj}
    {f : Hom X Y} {f' : Hom X' Y'} (hX : X = X') (hY : Y = Y') (h : f ≍ f') :
    f.subst σ ≍ f'.subst σ := by
  subst hX hY
  rw [eq_of_heq h]

/-! The constructors of raw expressions respect heterogeneous equality, given equal words. -/

private theorem α_hom_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') : Hom.α_hom X Y Z ≍ Hom.α_hom X' Y' Z' := by
  subst hX hY hZ; rfl

private theorem α_inv_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') : Hom.α_inv X Y Z ≍ Hom.α_inv X' Y' Z' := by
  subst hX hY hZ; rfl

private theorem comp_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} {f : Hom X Y}
    {f' : Hom X' Y'} {g : Hom Y Z} {g' : Hom Y' Z'} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (hf : f ≍ f') (hg : g ≍ g') : f.comp g ≍ f'.comp g' := by
  subst hX hY hZ; rw [eq_of_heq hf, eq_of_heq hg]

private theorem whiskerLeft_heq {X X' Y₁ Y₁' Y₂ Y₂' : FreeMonoidalCategory S.Obj}
    {f : Hom Y₁ Y₂} {f' : Hom Y₁' Y₂'} (hX : X = X') (h₁ : Y₁ = Y₁') (h₂ : Y₂ = Y₂')
    (hf : f ≍ f') : f.whiskerLeft X ≍ f'.whiskerLeft X' := by
  subst hX h₁ h₂; rw [eq_of_heq hf]

private theorem whiskerRight_heq {X₁ X₁' X₂ X₂' Y Y' : FreeMonoidalCategory S.Obj}
    {f : Hom X₁ X₂} {f' : Hom X₁' X₂'} (h₁ : X₁ = X₁') (h₂ : X₂ = X₂') (hY : Y = Y')
    (hf : f ≍ f') : f.whiskerRight Y ≍ f'.whiskerRight Y' := by
  subst h₁ h₂ hY; rw [eq_of_heq hf]

private theorem tensor_heq {W W' X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} {f : Hom W Y}
    {f' : Hom W' Y'} {g : Hom X Z} {g' : Hom X' Z'} (hW : W = W') (hX : X = X') (hY : Y = Y')
    (hZ : Z = Z') (hf : f ≍ f') (hg : g ≍ g') : f.tensor g ≍ f'.tensor g' := by
  subst hW hX hY hZ; rw [eq_of_heq hf, eq_of_heq hg]

private theorem homMk_heq {X X' Y Y' : FreeMonoidalCategory S.Obj} {f : Hom X Y}
    {f' : Hom X' Y'} (hX : X = X') (hY : Y = Y') (hf : f ≍ f') :
    homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f ≍ homMk (X := ⟨X'⟩) (Y := ⟨Y'⟩) f' := by
  subst hX hY; rw [eq_of_heq hf]

/-- Substituting the identity substitution into a raw expression gives the expression itself, up
to the identification of each word with its interpretation by its own generating objects. -/
theorem Hom.subst_substitutionId_heq {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    f.subst (Substitution.id S) ≍ f := by
  have h (X : FreeMonoidalCategory S.Obj) : (projectObj (Substitution.id S).obj X).as = X :=
    congrArg FreeMonoidal.as (projectObj_of X)
  induction f with
  | id X => exact congr_arg_heq Hom.id (h X)
  | α_hom X Y Z => exact α_hom_heq (h X) (h Y) (h Z)
  | α_inv X Y Z => exact α_inv_heq (h X) (h Y) (h Z)
  | l_hom X => exact congr_arg_heq Hom.l_hom (h X)
  | l_inv X => exact congr_arg_heq Hom.l_inv (h X)
  | ρ_hom X => exact congr_arg_heq Hom.ρ_hom (h X)
  | ρ_inv X => exact congr_arg_heq Hom.ρ_inv (h X)
  | coupon g => exact Substitution.id_coupon_heq g
  | comp f g hf hg => exact comp_heq (h _) (h _) (h _) hf hg
  | whiskerLeft X f hf => exact whiskerLeft_heq (h X) (h _) (h _) hf
  | whiskerRight f X hf => exact whiskerRight_heq (h _) (h _) (h X) hf
  | tensor f g hf hg => exact tensor_heq (h _) (h _) (h _) (h _) hf hg

/-- Substituting the identity substitution into a raw expression gives the expression itself, up
to endpoint casts identifying each word with its interpretation by its own generating objects. -/
@[simp]
theorem Hom.subst_substitutionId {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    f.subst (Substitution.id S) =
      f.cast
        ((congrArg FreeMonoidal.as (projectObj_of X)).symm.trans
          (congrArg (fun h ↦ (projectObj h X).as) (Substitution.id_obj (S := S)).symm))
        ((congrArg FreeMonoidal.as (projectObj_of Y)).symm.trans
          (congrArg (fun h ↦ (projectObj h Y).as) (Substitution.id_obj (S := S)).symm)) :=
  Hom.eq_cast_of_heq _ _ (Hom.subst_substitutionId_heq f)

variable {U : TensorSignature.{u'', v''}}

/-- Substituting `σ` and then `τ` into a raw expression is substituting their composite, up to
the identification of the boundary words given by `projectObj_projectObj`. -/
theorem Hom.subst_subst_heq (σ : Substitution S T) (τ : Substitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    (f.subst σ).subst τ ≍ f.subst (σ.comp τ) := by
  have h (X : FreeMonoidalCategory S.Obj) :
      (projectObj τ.obj (projectObj σ.obj X).as).as = (projectObj (σ.comp τ).obj X).as :=
    congrArg FreeMonoidal.as (projectObj_projectObj τ.obj σ.obj X)
  induction f with
  | id X => exact congr_arg_heq Hom.id (h X)
  | α_hom X Y Z => exact α_hom_heq (h X) (h Y) (h Z)
  | α_inv X Y Z => exact α_inv_heq (h X) (h Y) (h Z)
  | l_hom X => exact congr_arg_heq Hom.l_hom (h X)
  | l_inv X => exact congr_arg_heq Hom.l_inv (h X)
  | ρ_hom X => exact congr_arg_heq Hom.ρ_hom (h X)
  | ρ_inv X => exact congr_arg_heq Hom.ρ_inv (h X)
  | coupon g => exact (Substitution.comp_coupon_heq σ τ g).symm
  | comp f g hf hg => exact comp_heq (h _) (h _) (h _) hf hg
  | whiskerLeft X f hf => exact whiskerLeft_heq (h X) (h _) (h _) hf
  | whiskerRight f X hf => exact whiskerRight_heq (h _) (h _) (h X) hf
  | tensor f g hf hg => exact tensor_heq (h _) (h _) (h _) (h _) hf hg

/-- Substituting `σ` and then `τ` into a raw expression equals substituting their composite
`σ.comp τ`, up to the endpoint casts given by `projectObj_projectObj`. -/
@[simp]
theorem Hom.subst_subst (σ : Substitution S T) (τ : Substitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    (f.subst σ).subst τ =
      (f.subst (σ.comp τ)).cast
        ((congrArg (fun h ↦ (projectObj h X).as) (funext (Substitution.comp_obj σ τ))).trans
          (congrArg FreeMonoidal.as (projectObj_projectObj τ.obj σ.obj X)).symm)
        ((congrArg (fun h ↦ (projectObj h Y).as) (funext (Substitution.comp_obj σ τ))).trans
          (congrArg FreeMonoidal.as (projectObj_projectObj τ.obj σ.obj Y)).symm) :=
  Hom.eq_cast_of_heq _ _ (Hom.subst_subst_heq σ τ f)

end FreeMonoidal

namespace Substitution

open FreeMonoidal

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}}

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

/-! ### Embedding signature morphisms into substitutions -/

namespace Hom

open FreeMonoidal

/-- View a tensor-signature morphism as a substitution sending each generating object `a` to
`FreeMonoidal.of (φ.obj a)` and each coupon `g` to `Hom.coupon (φ.coupon g)`. -/
def toSubstitution {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) : Substitution S T where
  obj := FreeMonoidal.of ∘ φ.obj
  coupon g := (FreeMonoidal.Hom.coupon (φ.coupon g)).cast
    ((φ.src_coupon g).trans (as_projectObj (FreeMonoidal.of ∘ φ.obj) (S.src g)).symm)
    ((φ.tgt_coupon g).trans (as_projectObj (FreeMonoidal.of ∘ φ.obj) (S.tgt g)).symm)

@[simp]
theorem toSubstitution_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (a : S.Obj) :
    φ.toSubstitution.obj a = FreeMonoidal.of (φ.obj a) := by
  rfl

/-- Boundary compatibility for embedding a signature morphism `φ : Hom S T` as a substitution. -/
theorem src_coupon_projectObj_as {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    T.src (φ.coupon g) = (projectObj φ.toSubstitution.obj (S.src g)).as :=
  (φ.src_coupon g).trans (as_projectObj (FreeMonoidal.of ∘ φ.obj) (S.src g)).symm

/-- Target compatibility for embedding a signature morphism `φ : Hom S T` as a substitution. -/
theorem tgt_coupon_projectObj_as {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    T.tgt (φ.coupon g) = (projectObj φ.toSubstitution.obj (S.tgt g)).as :=
  (φ.tgt_coupon g).trans (as_projectObj (FreeMonoidal.of ∘ φ.obj) (S.tgt g)).symm

@[simp]
theorem toSubstitution_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    φ.toSubstitution.coupon g = (FreeMonoidal.Hom.coupon (φ.coupon g)).cast
      (φ.src_coupon_projectObj_as g) (φ.tgt_coupon_projectObj_as g) := by
  rfl

/-- The embedding of signature morphisms into substitutions is injective. -/
theorem toSubstitution_injective {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} :
    Function.Injective (toSubstitution (S := S) (T := T)) := by
  intro φ ψ h
  ext a
  · have ho := congrArg (fun σ : Substitution S T ↦ σ.obj a) h
    simp only [toSubstitution_obj] at ho
    exact FreeMonoidal.of_injective ho
  · have hc := congrArg (fun σ : Substitution S T ↦ (σ.coupon a).coupons) h
    simp only [toSubstitution_coupon, FreeMonoidal.Hom.coupons_cast,
      FreeMonoidal.Hom.coupons_coupon, List.cons.injEq, and_true] at hc
    exact hc

@[simp]
theorem toSubstitution_inj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {φ ψ : Hom S T} : φ.toSubstitution = ψ.toSubstitution ↔ φ = ψ :=
  toSubstitution_injective.eq_iff

@[simp]
theorem toSubstitution_id (S : TensorSignature.{u, v}) :
    (Hom.id S).toSubstitution = Substitution.id S := by
  refine Substitution.hext (funext fun a ↦ by simp) fun g ↦ ?_
  rw [toSubstitution_coupon]
  exact (Hom.cast_heq _ _ _).trans
    ((congr_arg_heq FreeMonoidal.Hom.coupon (Hom.id_coupon S g)).trans
      (Substitution.id_coupon_heq g).symm)

@[simp]
theorem toSubstitution_comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) :
    (φ.comp ψ).toSubstitution = φ.toSubstitution.comp ψ.toSubstitution := by
  refine Substitution.hext (funext fun a ↦ by simp) fun g ↦ ?_
  rw [toSubstitution_coupon]
  have hcoupon : (φ.toSubstitution.coupon g).subst ψ.toSubstitution ≍
      FreeMonoidal.Hom.coupon (ψ.coupon (φ.coupon g)) := by
    rw [toSubstitution_coupon, Hom.subst_cast, Hom.subst_coupon, toSubstitution_coupon]
    exact (Hom.cast_heq _ _ _).trans (Hom.cast_heq _ _ _)
  exact (Hom.cast_heq _ _ _).trans
    ((congr_arg_heq FreeMonoidal.Hom.coupon (Hom.comp_coupon φ ψ g)).trans
      (hcoupon.symm.trans
        (Substitution.comp_coupon_heq φ.toSubstitution ψ.toSubstitution g).symm))

/-- Precomposing a substitution `σ : Substitution T U` with a signature morphism `φ : Hom S T`
replaces each coupon `g` of `S` by `σ.coupon (φ.coupon g)` up to boundary transport. -/
theorem toSubstitution_comp_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (σ : Substitution T U) (g : S.Coupon) :
    (φ.toSubstitution.comp σ).coupon g = (σ.coupon (φ.coupon g)).cast
      ((congrArg (fun W ↦ (projectObj σ.obj W).as) (φ.src_coupon_projectObj_as g)).trans
        ((congrArg FreeMonoidal.as
          (FreeMonoidal.projectObj_projectObj σ.obj φ.toSubstitution.obj (S.src g))).trans
          (congrArg (fun h ↦ (projectObj h (S.src g)).as)
            (funext (Substitution.comp_obj φ.toSubstitution σ)).symm)))
      ((congrArg (fun W ↦ (projectObj σ.obj W).as) (φ.tgt_coupon_projectObj_as g)).trans
        ((congrArg FreeMonoidal.as
          (FreeMonoidal.projectObj_projectObj σ.obj φ.toSubstitution.obj (S.tgt g))).trans
          (congrArg (fun h ↦ (projectObj h (S.tgt g)).as)
            (funext (Substitution.comp_obj φ.toSubstitution σ)).symm))) := by
  have hsrc : (projectObj σ.obj (projectObj φ.toSubstitution.obj (S.src g)).as).as =
      (projectObj (φ.toSubstitution.comp σ).obj (S.src g)).as :=
    (congrArg FreeMonoidal.as
      (FreeMonoidal.projectObj_projectObj σ.obj φ.toSubstitution.obj (S.src g))).trans
      (congrArg (fun h ↦ (projectObj h (S.src g)).as)
        (funext (Substitution.comp_obj φ.toSubstitution σ)).symm)
  have htgt : (projectObj σ.obj (projectObj φ.toSubstitution.obj (S.tgt g)).as).as =
      (projectObj (φ.toSubstitution.comp σ).obj (S.tgt g)).as :=
    (congrArg FreeMonoidal.as
      (FreeMonoidal.projectObj_projectObj σ.obj φ.toSubstitution.obj (S.tgt g))).trans
      (congrArg (fun h ↦ (projectObj h (S.tgt g)).as)
        (funext (Substitution.comp_obj φ.toSubstitution σ)).symm)
  refine (Hom.eq_cast_of_heq hsrc htgt (Substitution.comp_coupon_heq φ.toSubstitution σ g)).trans ?_
  rw [toSubstitution_coupon, Hom.subst_cast, Hom.subst_coupon, Hom.cast_cast]

end Hom

/-! ### Monoidal natural isomorphisms and coherence for induced functors -/

namespace Substitution

open FreeMonoidal

section Functoriality

/-- The strong monoidal functor induced by `Substitution.id S` agrees on objects with the
identity functor. -/
theorem toFunctor_id_obj (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (Substitution.id S).toFunctor.obj X = X :=
  FreeMonoidal.projectObj_of X.as

private theorem toFunctor_map_id_coupon (S : TensorSignature.{u, v}) (g : S.Coupon) :
    (Substitution.id S).toFunctor.map (FreeMonoidal.coupon g) =
      eqToHom (toFunctor_id_obj S ⟨S.src g⟩) ≫ FreeMonoidal.coupon g ≫
        eqToHom (toFunctor_id_obj S ⟨S.tgt g⟩).symm :=
  (toFunctor_map_coupon (Substitution.id S) g).trans <|
    (congrArg FreeMonoidal.homMk (FreeMonoidal.Hom.eq_cast_of_heq
      (congrArg FreeMonoidal.as (toFunctor_id_obj S ⟨S.src g⟩)).symm
      (congrArg FreeMonoidal.as (toFunctor_id_obj S ⟨S.tgt g⟩)).symm
      (id_coupon_heq g))).trans ((homMk_cast _ _ _).trans (by rw [homMk_coupon]))

/-- The strong monoidal functor induced by `Substitution.id S` is monoidally naturally isomorphic
to the identity functor on `S.FreeMonoidal`. -/
def toFunctorIdIso (S : TensorSignature.{u, v}) :
    (Substitution.id S).toFunctor ≅ 𝟭 S.FreeMonoidal :=
  monoidalNatIsoOfEqObj (toFunctor_id_obj S)
    (by
      simp only [toFunctor_obj, tensorUnit_as, projectObj_tensorUnit, Functor.id_obj, toFunctor_η,
        Functor.LaxMonoidal.id_ε, Category.comp_id]
      exact (eqToHom_refl _ _).symm)
    (fun _ _ ↦ by
      simp only [toFunctor_obj, tensorObj_as, projectObj_tensorObj, Functor.id_obj, toFunctor_δ,
        Functor.LaxMonoidal.id_μ, Category.comp_id, Category.id_comp]
      exact TauCeti.eqToHom_tensorHom_eqToHom _ _)
    (fun g ↦ by
      rw [comp_eqToHom_iff, Category.assoc, toFunctor_map_id_coupon, Functor.id_map])

instance (S : TensorSignature.{u, v}) : NatTrans.IsMonoidal (toFunctorIdIso S).hom :=
  monoidalNatIsoOfEqObj_hom_isMonoidal _ _ _ _

@[simp]
theorem toFunctorIdIso_hom_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).hom.app X = eqToHom (toFunctor_id_obj S X) :=
  monoidalNatIsoOfEqObj_hom_app _ _ _ _ X

@[simp]
theorem toFunctorIdIso_inv_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).inv.app X = eqToHom (toFunctor_id_obj S X).symm :=
  monoidalNatIsoOfEqObj_inv_app _ _ _ _ X

/-- The strong monoidal functor induced by `σ.comp τ` agrees on objects with the composite functor
`σ.toFunctor ⋙ τ.toFunctor`. -/
theorem toFunctor_comp_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    (X : S.FreeMonoidal) :
    (σ.comp τ).toFunctor.obj X = (σ.toFunctor ⋙ τ.toFunctor).obj X :=
  congrArg FreeMonoidal.mk (congrArg FreeMonoidal.as
    (FreeMonoidal.projectObj_projectObj τ.obj σ.obj X.as)).symm

private theorem toFunctor_map_comp_coupon {U : TensorSignature.{u₃, v₃}}
    (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).toFunctor.map (FreeMonoidal.coupon g) =
      eqToHom (toFunctor_comp_obj σ τ ⟨S.src g⟩) ≫
        τ.toFunctor.map (σ.toFunctor.map (FreeMonoidal.coupon g)) ≫
        eqToHom (toFunctor_comp_obj σ τ ⟨S.tgt g⟩).symm := by
  have hsub : τ.toFunctor.map (σ.toFunctor.map (FreeMonoidal.coupon g)) =
      FreeMonoidal.homMk ((σ.coupon g).subst τ) :=
    (congrArg τ.toFunctor.map (toFunctor_map_coupon σ g)).trans (toFunctor_map_homMk τ (σ.coupon g))
  refine (toFunctor_map_coupon (σ.comp τ) g).trans <| (congrArg FreeMonoidal.homMk
    (FreeMonoidal.Hom.eq_cast_of_heq
      (congrArg FreeMonoidal.as (FreeMonoidal.projectObj_projectObj τ.obj σ.obj (S.src g)))
      (congrArg FreeMonoidal.as (FreeMonoidal.projectObj_projectObj τ.obj σ.obj (S.tgt g)))
      (comp_coupon_heq σ τ g))).trans <| (homMk_cast _ _ _).trans ?_
  exact congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _) hsub.symm

/-- The strong monoidal functor induced by a composite substitution `σ.comp τ` is monoidally
naturally isomorphic to the composite functor `σ.toFunctor ⋙ τ.toFunctor`. -/
def toFunctorCompIso {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    (σ.comp τ).toFunctor ≅ σ.toFunctor ⋙ τ.toFunctor :=
  monoidalNatIsoOfEqObj (toFunctor_comp_obj σ τ)
    (by
      simp only [toFunctor_obj, tensorUnit_as, projectObj_tensorUnit, Functor.comp_obj,
        toFunctor_η, Functor.LaxMonoidal.comp_ε, toFunctor_ε, Functor.map_id, Category.comp_id]
      exact (eqToHom_refl _ _).symm)
    (fun _ _ ↦ by
      simp only [toFunctor_obj, tensorObj_as, projectObj_tensorObj, Functor.comp_obj, toFunctor_δ,
        Functor.LaxMonoidal.comp_μ, toFunctor_μ, Functor.map_id, Category.comp_id,
        Category.id_comp]
      exact TauCeti.eqToHom_tensorHom_eqToHom _ _)
    (fun g ↦ by
      rw [comp_eqToHom_iff, Category.assoc, toFunctor_map_comp_coupon, Functor.comp_map])

instance {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    NatTrans.IsMonoidal (toFunctorCompIso σ τ).hom :=
  monoidalNatIsoOfEqObj_hom_isMonoidal _ _ _ _

@[simp]
theorem toFunctorCompIso_hom_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    (X : S.FreeMonoidal) :
    (toFunctorCompIso σ τ).hom.app X = eqToHom (toFunctor_comp_obj σ τ X) :=
  monoidalNatIsoOfEqObj_hom_app _ _ _ _ X

@[simp]
theorem toFunctorCompIso_inv_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    (X : S.FreeMonoidal) :
    (toFunctorCompIso σ τ).inv.app X = eqToHom (toFunctor_comp_obj σ τ X).symm :=
  monoidalNatIsoOfEqObj_inv_app _ _ _ _ X

/-- Left unit coherence for `Substitution.toFunctor`: composing `toFunctorCompIso (id S) σ` with
`toFunctorIdIso S` agrees with `Substitution.id_comp σ`. -/
theorem toFunctorCompIso_id_left {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) :
    toFunctorCompIso (id S) σ ≪≫ Functor.isoWhiskerRight (toFunctorIdIso S) σ.toFunctor ≪≫
        Functor.leftUnitor σ.toFunctor =
      eqToIso (congrArg toFunctor (id_comp σ)) := by
  ext X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    toFunctorCompIso_hom_app, toFunctorIdIso_hom_app, eqToIso.hom, eqToHom_app, eqToHom_map,
    eqToHom_trans, Category.comp_id]

/-- Right unit coherence for `Substitution.toFunctor`: composing `toFunctorCompIso σ (id T)` with
`toFunctorIdIso T` agrees with `Substitution.comp_id σ`. -/
theorem toFunctorCompIso_id_right {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) :
    toFunctorCompIso σ (id T) ≪≫ Functor.isoWhiskerLeft σ.toFunctor (toFunctorIdIso T) ≪≫
        Functor.rightUnitor σ.toFunctor =
      eqToIso (congrArg toFunctor (comp_id σ)) := by
  ext X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    toFunctorCompIso_hom_app, toFunctorIdIso_hom_app, eqToIso.hom, eqToHom_app, eqToHom_trans,
    Category.comp_id]

/-- Associativity coherence (pentagon) for `Substitution.toFunctorCompIso`. -/
theorem toFunctorCompIso_assoc {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} {V : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) (ρ : Substitution U V) :
    toFunctorCompIso (σ.comp τ) ρ ≪≫
        Functor.isoWhiskerRight (toFunctorCompIso σ τ) ρ.toFunctor ≪≫
        Functor.associator σ.toFunctor τ.toFunctor ρ.toFunctor =
      eqToIso (congrArg toFunctor (comp_assoc σ τ ρ)) ≪≫ toFunctorCompIso σ (τ.comp ρ) ≪≫
        Functor.isoWhiskerLeft σ.toFunctor (toFunctorCompIso τ ρ) := by
  ext X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.comp_obj, toFunctorCompIso_hom_app, eqToIso.hom,
    eqToHom_app, eqToHom_map, eqToHom_trans, Category.comp_id]

end Functoriality

/-! ### Change of signature for interpretations -/

section Pullback

variable {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
  {D : Type u₃} [Category.{v₃} D] [MonoidalCategory D]

/-- Pull back a generator-object assignment `fo : T.Obj → D` along a substitution
`σ : Substitution S T` by evaluating each replacing tensor word `σ.obj a` in `D`. -/
@[expose] def pullbackObj (σ : Substitution S T) (fo : T.Obj → D) : S.Obj → D :=
  fun a ↦ projectObj fo (σ.obj a).as

@[simp]
theorem pullbackObj_apply (σ : Substitution S T) (fo : T.Obj → D) (a : S.Obj) :
    σ.pullbackObj fo a = projectObj fo (σ.obj a).as :=
  (rfl)

/-- Evaluating a formal tensor word of `S` along `σ.pullbackObj fo` agrees with evaluating its
`σ`-substituted word along `fo`, in any (not necessarily strict) monoidal category `D`. -/
theorem projectObj_pullbackObj (σ : Substitution S T) (fo : T.Obj → D)
    (X : FreeMonoidalCategory S.Obj) :
    projectObj (σ.pullbackObj fo) X = projectObj fo (projectObj σ.obj X).as :=
  (FreeMonoidal.projectObj_projectObj fo σ.obj X).symm

/-- Pull back a coupon interpretation `(fo, fc)` of `T` in `D` along a substitution
`σ : Substitution S T` by interpreting each replacing expression `σ.coupon g` via
`FreeMonoidal.lift fo fc`. -/
def pullbackCoupon (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h))
    (g : S.Coupon) :
    projectObj (σ.pullbackObj fo) (S.src g) ⟶ projectObj (σ.pullbackObj fo) (S.tgt g) :=
  eqToHom (σ.projectObj_pullbackObj fo (S.src g)) ≫
    (FreeMonoidal.lift fo fc).map
      (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
        (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g)) ≫
      eqToHom (σ.projectObj_pullbackObj fo (S.tgt g)).symm

/-- Unfolding formula for `Substitution.pullbackCoupon` in terms of `FreeMonoidal.lift`,
`FreeMonoidal.homMk`, and `eqToHom`. -/
theorem pullbackCoupon_def (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h))
    (g : S.Coupon) :
    σ.pullbackCoupon fo fc g =
      eqToHom (σ.projectObj_pullbackObj fo (S.src g)) ≫
        (FreeMonoidal.lift fo fc).map
          (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
            (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g)) ≫
          eqToHom (σ.projectObj_pullbackObj fo (S.tgt g)).symm :=
  (rfl)

/-- Change-of-signature compatibility: precomposing `FreeMonoidal.lift fo fc` with `σ.toFunctor`
is monoidally naturally isomorphic to `FreeMonoidal.lift` of the pulled-back interpretation
`(σ.pullbackObj fo, σ.pullbackCoupon fo fc)` in any monoidal category `D`. -/
def toFunctorCompLiftIso (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h)) :
    σ.toFunctor ⋙ FreeMonoidal.lift fo fc ≅
      FreeMonoidal.lift (σ.pullbackObj fo) (σ.pullbackCoupon fo fc) :=
  have hobj : ∀ X, (σ.toFunctor ⋙ FreeMonoidal.lift fo fc).obj X =
      (FreeMonoidal.lift (σ.pullbackObj fo) (σ.pullbackCoupon fo fc)).obj X :=
    fun X ↦ (σ.projectObj_pullbackObj fo X.as).symm
  monoidalNatIsoOfEqObj hobj
    (by
      simp only [Functor.comp_obj, toFunctor_obj, tensorUnit_as, projectObj_tensorUnit,
        lift_obj_tensorUnit, Functor.OplaxMonoidal.comp_η, toFunctor_η, Functor.map_id, lift_η,
        Category.comp_id, lift_ε]
      exact (eqToHom_refl _ _).symm)
    (fun _ _ ↦ by
      simp only [Functor.comp_obj, toFunctor_obj, tensorObj_as, projectObj_tensorObj,
        lift_obj_tensor, Functor.OplaxMonoidal.comp_δ, toFunctor_δ, Functor.map_id, lift_δ,
        Category.comp_id, lift_μ, Category.id_comp]
      exact TauCeti.eqToHom_tensorHom_eqToHom _ _)
    (fun g ↦ by
      symm
      rw [eqToHom_comp_iff, lift_map_coupon, pullbackCoupon_def, Functor.comp_map,
        toFunctor_map_coupon]
      rfl)

instance (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h)) :
    NatTrans.IsMonoidal (σ.toFunctorCompLiftIso fo fc).hom :=
  monoidalNatIsoOfEqObj_hom_isMonoidal _ _ _ _

@[simp]
theorem toFunctorCompLiftIso_hom_app (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h))
    (X : S.FreeMonoidal) :
    (σ.toFunctorCompLiftIso fo fc).hom.app X =
      eqToHom (σ.projectObj_pullbackObj fo X.as).symm :=
  monoidalNatIsoOfEqObj_hom_app _ _ _ _ X

@[simp]
theorem toFunctorCompLiftIso_inv_app (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h))
    (X : S.FreeMonoidal) :
    (σ.toFunctorCompLiftIso fo fc).inv.app X =
      eqToHom (σ.projectObj_pullbackObj fo X.as) :=
  monoidalNatIsoOfEqObj_inv_app _ _ _ _ X

private theorem projectObjIso_pullbackObj (σ : Substitution S T) {I J : Interpretation T D}
    (α : I ⟶ J) (X : FreeMonoidalCategory S.Obj) :
    projectObjIso (f := σ.pullbackObj I.obj) (g := σ.pullbackObj J.obj)
        (fun a ↦ projectObjIso α.iso (σ.obj a).as) X =
      eqToIso (σ.projectObj_pullbackObj I.obj X) ≪≫
        projectObjIso α.iso (projectObj σ.obj X).as ≪≫
        eqToIso (σ.projectObj_pullbackObj J.obj X).symm := by
  -- Structural induction on the tensor word, collapsing `eqToHom` transports at each constructor.
  induction X with
  | of a =>
    refine Iso.ext ((congrArg Iso.hom (projectObjIso_of _ a)).trans (Eq.symm ?_))
    rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
    exact (congrArg₂ (· ≫ ·) (eqToHom_refl _ rfl)
        (congrArg₂ (· ≫ ·) rfl (eqToHom_refl _ rfl))).trans
      ((congrArg (𝟙 _ ≫ ·) (Category.comp_id _)).trans (Category.id_comp _))
  | unit =>
    refine Iso.ext ((congrArg Iso.hom (projectObjIso_tensorUnit _)).trans (Eq.symm ?_))
    rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
    exact (congrArg₂ (· ≫ ·) (eqToHom_refl _ rfl)
        (congrArg₂ (· ≫ ·) (congrArg Iso.hom (projectObjIso_tensorUnit α.iso))
          (eqToHom_refl _ rfl))).trans
      ((congrArg (𝟙 _ ≫ ·) (Category.comp_id _)).trans (Category.id_comp _))
  | tensor X Y ihX ihY =>
    refine Iso.ext ((congrArg Iso.hom (projectObjIso_tensor _ X Y)).trans ?_)
    refine (congrArg₂ (· ⊗ₘ ·) (congrArg Iso.hom ihX) (congrArg Iso.hom ihY)).trans ?_
    rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom,
      eqToIso.hom, eqToIso.hom, ← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom, TauCeti.eqToHom_tensorHom_eqToHom,
      TauCeti.eqToHom_tensorHom_eqToHom]
    refine Eq.symm ?_
    rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
    exact congrArg (fun f ↦ eqToHom _ ≫ f ≫ eqToHom _)
      (congrArg Iso.hom (projectObjIso_tensor α.iso _ _))

private theorem projectObjIso_congr_word {A : Type*} {f g : A → D} (e : ∀ a, f a ≅ g a)
    {w w' : FreeMonoidalCategory A} (hw : w = w') :
    (projectObjIso e w).hom =
      eqToHom (congrArg (projectObj f) hw) ≫ (projectObjIso e w').hom ≫
        eqToHom (congrArg (projectObj g) hw).symm := by
  subst hw; simp

/-- Pulling back a morphism of interpretations along a substitution `σ` commutes with the
pulled-back coupons. -/
theorem pullback_map_comm (σ : Substitution S T) {I J : Interpretation T D}
    (α : I ⟶ J) (g : S.Coupon) :
    σ.pullbackCoupon I.obj I.coupon g ≫
        (projectObjIso (f := σ.pullbackObj I.obj) (g := σ.pullbackObj J.obj)
          (fun a ↦ projectObjIso α.iso (σ.obj a).as) (S.tgt g)).hom =
      (projectObjIso (f := σ.pullbackObj I.obj) (g := σ.pullbackObj J.obj)
          (fun a ↦ projectObjIso α.iso (σ.obj a).as) (S.src g)).hom ≫
        σ.pullbackCoupon J.obj J.coupon g := by
  let mI : projectObj I.obj (projectObj σ.obj (S.src g)).as ⟶
      projectObj I.obj (projectObj σ.obj (S.tgt g)).as :=
    (FreeMonoidal.lift I.obj I.coupon).map
      (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
        (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g))
  let mJ : projectObj J.obj (projectObj σ.obj (S.src g)).as ⟶
      projectObj J.obj (projectObj σ.obj (S.tgt g)).as :=
    (FreeMonoidal.lift J.obj J.coupon).map
      (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
        (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g))
  have hnat : mI ≫ (projectObjIso α.iso (projectObj σ.obj (S.tgt g)).as).hom =
      (projectObjIso α.iso (projectObj σ.obj (S.src g)).as).hom ≫ mJ := by
    have h := ((Interpretation.extension T D).map α).iso.hom.hom.hom.naturality
      (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
        (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g))
    rw [Interpretation.extension_map_iso_hom_hom_hom_app,
      Interpretation.extension_map_iso_hom_hom_hom_app] at h
    exact h
  have hl : σ.pullbackCoupon I.obj I.coupon g =
      eqToHom (σ.projectObj_pullbackObj I.obj (S.src g)) ≫ mI ≫
        eqToHom (σ.projectObj_pullbackObj I.obj (S.tgt g)).symm :=
    σ.pullbackCoupon_def I.obj I.coupon g
  have hr : σ.pullbackCoupon J.obj J.coupon g =
      eqToHom (σ.projectObj_pullbackObj J.obj (S.src g)) ≫ mJ ≫
        eqToHom (σ.projectObj_pullbackObj J.obj (S.tgt g)).symm :=
    σ.pullbackCoupon_def J.obj J.coupon g
  refine (congrArg₂ (· ≫ ·) hl
    (congrArg Iso.hom (projectObjIso_pullbackObj σ α (S.tgt g)))).trans (Eq.trans ?_
      (congrArg₂ (· ≫ ·) (congrArg Iso.hom (projectObjIso_pullbackObj σ α (S.src g))) hr).symm)
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [reassoc_of% hnat]

variable (D) in
/-- Pull back interpretations of `T` in `D` and their isomorphisms along a substitution
`σ : Substitution S T`. -/
@[expose] def pullback (σ : Substitution S T) : Interpretation T D ⥤ Interpretation S D where
  obj I := ⟨σ.pullbackObj I.obj, σ.pullbackCoupon I.obj I.coupon⟩
  map α :=
    { iso a := projectObjIso α.iso (σ.obj a).as
      comm g := pullback_map_comm σ α g }
  map_id I := Interpretation.hom_ext fun a ↦
    (congrArg (fun e ↦ (projectObjIso e (σ.obj a).as).hom) (funext (Interpretation.id_iso I))).trans
      (congrArg Iso.hom (projectObjIso_refl (σ.obj a).as))
  map_comp α β := Interpretation.hom_ext fun a ↦
    (congrArg (fun e ↦ (projectObjIso e (σ.obj a).as).hom)
      (funext (Interpretation.comp_iso α β))).trans
      (congrArg Iso.hom (projectObjIso_trans _ _ (σ.obj a).as))

@[simp]
theorem pullback_obj_obj (σ : Substitution S T) (I : Interpretation T D) :
    ((σ.pullback D).obj I).obj = σ.pullbackObj I.obj := rfl

@[simp]
theorem pullback_obj_coupon (σ : Substitution S T) (I : Interpretation T D) :
    ((σ.pullback D).obj I).coupon = σ.pullbackCoupon I.obj I.coupon := rfl

@[simp]
theorem pullback_map_iso (σ : Substitution S T) {I J : Interpretation T D} (α : I ⟶ J)
    (a : S.Obj) :
    ((σ.pullback D).map α).iso a = projectObjIso α.iso (σ.obj a).as := rfl

/-- Naturality of `Substitution.toFunctorCompLiftIso` in `I : Interpretation T D`: whiskering the
extension of an interpretation isomorphism `α : I ⟶ J` with `σ.toFunctor` commutes with
`toFunctorCompLiftIso` and the extension of `(σ.pullback D).map α`. -/
theorem toFunctorCompLiftIso_natural (σ : Substitution S T) {I J : Interpretation T D}
    (α : I ⟶ J) :
    Functor.whiskerLeft σ.toFunctor ((Interpretation.extension T D).map α).iso.hom.hom.hom ≫
        (σ.toFunctorCompLiftIso J.obj J.coupon).hom =
      (σ.toFunctorCompLiftIso I.obj I.coupon).hom ≫
        ((Interpretation.extension S D).map ((σ.pullback D).map α)).iso.hom.hom.hom := by
  ext X
  have h1 := Interpretation.extension_map_iso_hom_hom_hom_app α (σ.toFunctor.obj X)
  have h2 := Interpretation.extension_map_iso_hom_hom_hom_app ((σ.pullback D).map α) X
  have hp := congrArg (eqToHom (σ.projectObj_pullbackObj I.obj X.as).symm ≫ ·)
    (congrArg Iso.hom (projectObjIso_pullbackObj σ α X.as))
  simp only [Iso.trans_hom, eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hp
  exact (congrArg₂ (· ≫ ·) h1 (toFunctorCompLiftIso_hom_app σ J.obj J.coupon X)).trans
    (hp.symm.trans (congrArg₂ (· ≫ ·) (toFunctorCompLiftIso_hom_app σ I.obj I.coupon X) h2).symm)

variable (D) in
/-- Precomposition of bundled strong monoidal functors and monoidal natural isomorphisms with
`σ.toFunctor`. -/
@[expose] def precomp (σ : Substitution S T) :
    Core (MonoidalFunctor T.FreeMonoidal D) ⥤ Core (MonoidalFunctor S.FreeMonoidal D) where
  obj F := ⟨MonoidalFunctor.of (σ.toFunctor ⋙ F.of.toFunctor)⟩
  map {F G} α := ⟨@MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) (.of _)
    (Functor.isoWhiskerLeft σ.toFunctor (MonoidalFunctor.toFunctorIso α.iso))
    (inferInstanceAs (NatTrans.IsMonoidal
      (σ.toFunctor.whiskerLeft (MonoidalFunctor.toFunctorIso α.iso).hom)))⟩
  map_id F := Core.hom_ext <| MonoidalFunctor.hom_ext <| by ext X; rfl
  map_comp α β := Core.hom_ext <| MonoidalFunctor.hom_ext <| by ext X; rfl

@[simp]
theorem precomp_obj_of (σ : Substitution S T) (F : Core (MonoidalFunctor T.FreeMonoidal D)) :
    ((σ.precomp D).obj F).of = MonoidalFunctor.of (σ.toFunctor ⋙ F.of.toFunctor) := rfl

@[simp]
theorem precomp_map_iso_hom_hom_hom (σ : Substitution S T)
    {F G : Core (MonoidalFunctor T.FreeMonoidal D)} (α : F ⟶ G) :
    ((σ.precomp D).map α).iso.hom.hom.hom =
      Functor.whiskerLeft σ.toFunctor α.iso.hom.hom.hom := rfl

variable (D) in
/-- Naturality of extension under pullback: precomposing `Interpretation.extension` with
`σ.toFunctor` is naturally isomorphic to pulling back interpretations along `σ` and extending. -/
def extensionPullbackIso (σ : Substitution S T) :
    Interpretation.extension T D ⋙ σ.precomp D ≅
      σ.pullback D ⋙ Interpretation.extension S D :=
  NatIso.ofComponents
    (fun I ↦ (Groupoid.isoEquivHom _ _).symm <|
      ⟨@MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) (.of _) (σ.toFunctorCompLiftIso I.obj I.coupon)
        (inferInstanceAs (NatTrans.IsMonoidal (σ.toFunctorCompLiftIso I.obj I.coupon).hom))⟩)
    (fun α ↦ Core.hom_ext <| MonoidalFunctor.hom_ext <| by
      -- Expose the underlying natural-transformation square for `toFunctorCompLiftIso_natural`.
      change Functor.whiskerLeft σ.toFunctor
          ((Interpretation.extension T D).map α).iso.hom.hom.hom ≫
          (σ.toFunctorCompLiftIso _ _).hom =
        (σ.toFunctorCompLiftIso _ _).hom ≫
          ((Interpretation.extension S D).map ((σ.pullback D).map α)).iso.hom.hom.hom
      exact toFunctorCompLiftIso_natural σ α)

@[simp]
theorem extensionPullbackIso_hom_app_iso_hom_hom_hom (σ : Substitution S T)
    (I : Interpretation T D) :
    ((σ.extensionPullbackIso D).hom.app I).iso.hom.hom.hom =
      (σ.toFunctorCompLiftIso I.obj I.coupon).hom := by
  rw [extensionPullbackIso]; simp only [NatIso.ofComponents_hom_app]; rfl

/-- Pulling back a generator-object assignment along `Substitution.id S` returns the same
assignment. -/
theorem pullback_id_obj (fo : S.Obj → D) : (id S).pullbackObj fo = fo :=
  funext fun a ↦ by simp [pullbackObj]

omit [MonoidalCategory D] in
private theorem eqToHom_conj_conj {a b c d e f : D}
    (h₁ : a = b) (h₂ : b = c) (m : c ⟶ d) (h₃ : d = e) (h₄ : e = f) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ m ≫ eqToHom h₃) ≫ eqToHom h₄ =
      eqToHom (h₁.trans h₂) ≫ m ≫ eqToHom (h₃.trans h₄) := by
  subst h₁ h₂ h₃ h₄; simp

private theorem pullbackCoupon_id (I : Interpretation S D) (g : S.Coupon) :
    (id S).pullbackCoupon I.obj I.coupon g =
      eqToHom (projectObj_congr (congrFun (pullback_id_obj I.obj)) (S.src g)) ≫
        I.coupon g ≫
        eqToHom (projectObj_congr (congrFun (pullback_id_obj I.obj)) (S.tgt g)).symm := by
  have hlift : (FreeMonoidal.lift I.obj I.coupon).map
        (FreeMonoidal.homMk (X := projectObj (id S).obj (S.src g))
          (Y := projectObj (id S).obj (S.tgt g)) ((id S).coupon g)) =
      eqToHom ((id S).projectObj_pullbackObj I.obj (S.src g) |>.symm.trans
          (projectObj_congr (congrFun (pullback_id_obj I.obj)) (S.src g))) ≫
        I.coupon g ≫
        eqToHom ((id S).projectObj_pullbackObj I.obj (S.tgt g) |>.symm.trans
          (projectObj_congr (congrFun (pullback_id_obj I.obj)) (S.tgt g))).symm :=
    (congrArg (FreeMonoidal.lift I.obj I.coupon).map
      ((Substitution.toFunctor_map_coupon (id S) g).symm.trans
        (toFunctor_map_id_coupon S g))).trans <|
      (Functor.map_comp _ _ _).trans <| congrArg₂ (· ≫ ·) (eqToHom_map _ _) <|
        (Functor.map_comp _ _ _).trans <|
          congrArg₂ (· ≫ ·) (FreeMonoidal.lift_map_coupon _ _ _) (eqToHom_map _ _)
  exact (pullbackCoupon_def (id S) I.obj I.coupon g).trans <|
    (congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _) hlift).trans (eqToHom_conj_conj _ _ _ _ _)

private theorem pullbackIdIso_comm (I : Interpretation S D) (g : S.Coupon) :
    (id S).pullbackCoupon I.obj I.coupon g ≫
        (projectObjIso (fun a ↦ eqToIso (congrFun (pullback_id_obj I.obj) a)) (S.tgt g)).hom =
      (projectObjIso (fun a ↦ eqToIso (congrFun (pullback_id_obj I.obj) a)) (S.src g)).hom ≫
        I.coupon g := by
  rw [pullbackCoupon_id, projectObjIso_eqToIso, projectObjIso_eqToIso, eqToIso.hom, eqToIso.hom]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem pullbackIdIso_naturality {I J : Interpretation S D} (α : I ⟶ J) (a : S.Obj) :
    (projectObjIso α.iso ((id S).obj a).as).hom ≫
        eqToHom (congrFun (pullback_id_obj J.obj) a) =
      eqToHom (congrFun (pullback_id_obj I.obj) a) ≫ (α.iso a).hom := by
  have h : ((id S).obj a).as = .of a := congrArg FreeMonoidal.as (congrFun id_obj a)
  have qJ : projectObj J.obj ((id S).obj a).as = J.obj a := congrFun (pullback_id_obj J.obj) a
  refine (congrArg (· ≫ eqToHom qJ) (projectObjIso_congr_word α.iso h)).trans ?_
  rw [projectObjIso_of]
  simp only [Category.assoc, eqToHom_trans]
  exact congrArg (_ ≫ ·)
    ((congrArg ((α.iso a).hom ≫ ·) (eqToHom_refl _ rfl)).trans (Category.comp_id _))

variable (D) in
/-- Pulling back interpretations along `Substitution.id S` is naturally isomorphic to the identity
functor on `Interpretation S D`. -/
def pullbackIdIso : (id S).pullback D ≅ 𝟭 (Interpretation S D) :=
  NatIso.ofComponents
    (fun I ↦ (Groupoid.isoEquivHom _ _).symm
      { iso a := eqToIso (congrFun (pullback_id_obj I.obj) a)
        comm g := pullbackIdIso_comm I g })
    (fun α ↦ Interpretation.hom_ext fun a ↦ pullbackIdIso_naturality α a)

@[simp]
theorem pullbackIdIso_hom_app_iso (I : Interpretation S D) (a : S.Obj) :
    ((pullbackIdIso D).hom.app I).iso a = eqToIso (congrFun (pullback_id_obj I.obj) a) := by
  rw [pullbackIdIso]; simp only [NatIso.ofComponents_hom_app]; rfl

/-- Pulling back a generator-object assignment along `σ.comp τ` agrees with pulling back along
`τ` and then along `σ`. -/
theorem comp_pullbackObj {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (fo : U.Obj → D) :
    (σ.comp τ).pullbackObj fo = σ.pullbackObj (τ.pullbackObj fo) :=
  funext fun a ↦ by
    rw [pullbackObj_apply, comp_obj, pullbackObj_apply, FreeMonoidal.projectObj_projectObj]
    exact projectObj_congr (fun b ↦ (pullbackObj_apply τ fo b).symm) (σ.obj a).as

private theorem pullbackCoupon_comp {U : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) (I : Interpretation U D) (g : S.Coupon) :
    (σ.comp τ).pullbackCoupon I.obj I.coupon g =
      eqToHom (projectObj_congr (congrFun (comp_pullbackObj σ τ I.obj)) (S.src g)) ≫
        σ.pullbackCoupon (τ.pullbackObj I.obj) (τ.pullbackCoupon I.obj I.coupon) g ≫
        eqToHom (projectObj_congr (congrFun (comp_pullbackObj σ τ I.obj)) (S.tgt g)).symm := by
  let mL := (FreeMonoidal.lift (τ.pullbackObj I.obj) (τ.pullbackCoupon I.obj I.coupon)).map
    (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
      (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g))
  have hnat := (τ.toFunctorCompLiftIso I.obj I.coupon).hom.naturality
    (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
      (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g))
  rw [Functor.comp_map, toFunctorCompLiftIso_hom_app, toFunctorCompLiftIso_hom_app,
    τ.toFunctor_map_homMk (σ.coupon g)] at hnat
  have hmid : (FreeMonoidal.lift I.obj I.coupon).map
        (FreeMonoidal.homMk (X := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.src g⟩)
          (Y := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.tgt g⟩) ((σ.coupon g).subst τ)) =
      eqToHom (τ.projectObj_pullbackObj I.obj (projectObj σ.obj (S.src g)).as).symm ≫
        mL ≫ eqToHom (τ.projectObj_pullbackObj I.obj (projectObj σ.obj (S.tgt g)).as) :=
    ((comp_eqToHom_iff _ _ _).mp hnat).trans (Category.assoc _ _ _)
  have hsub : τ.toFunctor.map (σ.toFunctor.map (FreeMonoidal.coupon g)) =
      FreeMonoidal.homMk (X := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.src g⟩)
        (Y := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.tgt g⟩) ((σ.coupon g).subst τ) :=
    (congrArg τ.toFunctor.map (toFunctor_map_coupon σ g)).trans (toFunctor_map_homMk τ (σ.coupon g))
  have hcomp : FreeMonoidal.homMk (X := projectObj (σ.comp τ).obj (S.src g))
        (Y := projectObj (σ.comp τ).obj (S.tgt g)) ((σ.comp τ).coupon g) =
      eqToHom (toFunctor_comp_obj σ τ ⟨S.src g⟩) ≫
        FreeMonoidal.homMk (X := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.src g⟩)
          (Y := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.tgt g⟩) ((σ.coupon g).subst τ) ≫
        eqToHom (toFunctor_comp_obj σ τ ⟨S.tgt g⟩).symm :=
    ((Substitution.toFunctor_map_coupon (σ.comp τ) g).symm.trans
      (toFunctor_map_comp_coupon σ τ g)).trans
      (congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _) hsub)
  have hlift : (FreeMonoidal.lift I.obj I.coupon).map
        (FreeMonoidal.homMk (X := projectObj (σ.comp τ).obj (S.src g))
          (Y := projectObj (σ.comp τ).obj (S.tgt g)) ((σ.comp τ).coupon g)) =
      eqToHom ((σ.comp τ).projectObj_pullbackObj I.obj (S.src g) |>.symm.trans
          ((projectObj_congr (congrFun (comp_pullbackObj σ τ I.obj)) (S.src g)).trans
            (σ.projectObj_pullbackObj (τ.pullbackObj I.obj) (S.src g)))) ≫
        mL ≫ eqToHom ((σ.comp τ).projectObj_pullbackObj I.obj (S.tgt g) |>.symm.trans
          ((projectObj_congr (congrFun (comp_pullbackObj σ τ I.obj)) (S.tgt g)).trans
            (σ.projectObj_pullbackObj (τ.pullbackObj I.obj) (S.tgt g)))).symm :=
    (congrArg (FreeMonoidal.lift I.obj I.coupon).map hcomp).trans <|
      (Functor.map_comp (FreeMonoidal.lift I.obj I.coupon)
        (eqToHom (toFunctor_comp_obj σ τ ⟨S.src g⟩))
        (FreeMonoidal.homMk (X := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.src g⟩)
          (Y := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.tgt g⟩) ((σ.coupon g).subst τ) ≫
          eqToHom (toFunctor_comp_obj σ τ ⟨S.tgt g⟩).symm)).trans <|
        (congrArg₂ (· ≫ ·) (eqToHom_map _ _) <|
          (Functor.map_comp (FreeMonoidal.lift I.obj I.coupon)
            (FreeMonoidal.homMk (X := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.src g⟩)
              (Y := (σ.toFunctor ⋙ τ.toFunctor).obj ⟨S.tgt g⟩) ((σ.coupon g).subst τ))
            (eqToHom (toFunctor_comp_obj σ τ ⟨S.tgt g⟩).symm)).trans
            (congrArg₂ (· ≫ ·) hmid (eqToHom_map _ _))).trans
          (eqToHom_conj_conj _ _ _ _ _)
  exact (pullbackCoupon_def (σ.comp τ) I.obj I.coupon g).trans <|
    (congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _) hlift).trans <|
      (eqToHom_conj_conj _ _ _ _ _).trans <| (eqToHom_conj_conj _ _ _ _ _).symm.trans <|
        congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _)
          (pullbackCoupon_def σ (τ.pullbackObj I.obj) (τ.pullbackCoupon I.obj I.coupon) g).symm

private theorem pullbackCompIso_comm {U : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) (I : Interpretation U D) (g : S.Coupon) :
    (σ.comp τ).pullbackCoupon I.obj I.coupon g ≫
        (projectObjIso (fun a ↦ eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a))
          (S.tgt g)).hom =
      (projectObjIso (fun a ↦ eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a))
          (S.src g)).hom ≫
        σ.pullbackCoupon (τ.pullbackObj I.obj) (τ.pullbackCoupon I.obj I.coupon) g := by
  rw [pullbackCoupon_comp, projectObjIso_eqToIso, projectObjIso_eqToIso, eqToIso.hom, eqToIso.hom]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem pullbackCompIso_naturality {U : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) {I J : Interpretation U D} (α : I ⟶ J)
    (a : S.Obj) :
    (projectObjIso α.iso ((σ.comp τ).obj a).as).hom ≫
        eqToHom (congrFun (comp_pullbackObj σ τ J.obj) a) =
      eqToHom (congrFun (comp_pullbackObj σ τ I.obj) a) ≫
        (projectObjIso ((τ.pullback D).map α).iso (σ.obj a).as).hom := by
  have h : ((σ.comp τ).obj a).as = (projectObj τ.obj (σ.obj a).as).as :=
    congrArg FreeMonoidal.as (comp_obj σ τ a)
  let m := (projectObjIso α.iso (projectObj τ.obj (σ.obj a).as).as).hom
  have qI : (σ.comp τ).pullbackObj I.obj a = projectObj (τ.pullbackObj I.obj) (σ.obj a).as :=
    congrFun (comp_pullbackObj σ τ I.obj) a
  have qJ : projectObj J.obj ((σ.comp τ).obj a).as = σ.pullbackObj (τ.pullbackObj J.obj) a :=
    congrFun (comp_pullbackObj σ τ J.obj) a
  have hp := congrArg Iso.hom (projectObjIso_pullbackObj τ α (σ.obj a).as)
  simp only [Iso.trans_hom, eqToIso.hom] at hp
  refine (congrArg (· ≫ eqToHom qJ) (projectObjIso_congr_word α.iso h)).trans ?_
  refine Eq.trans ?_ (congrArg (eqToHom qI ≫ ·) hp).symm
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (m ≫ ·) (eqToHom_trans _ _)))).trans
      ((congrArg (· ≫ m ≫ _) (eqToHom_trans _ _)).symm.trans (Category.assoc _ _ _))

variable (D) in
/-- Pulling back interpretations along `σ.comp τ` is naturally isomorphic to pulling back along
`τ` and then along `σ`. -/
def pullbackCompIso {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) :
    (σ.comp τ).pullback D ≅ τ.pullback D ⋙ σ.pullback D :=
  NatIso.ofComponents
    (fun I ↦ (Groupoid.isoEquivHom _ _).symm
      { iso a := eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a)
        comm g := pullbackCompIso_comm σ τ I g })
    (fun α ↦ Interpretation.hom_ext fun a ↦ pullbackCompIso_naturality σ τ α a)

@[simp]
theorem pullbackCompIso_hom_app_iso {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (I : Interpretation U D) (a : S.Obj) :
    ((pullbackCompIso D σ τ).hom.app I).iso a =
      eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a) := by
  rw [pullbackCompIso]; simp only [NatIso.ofComponents_hom_app]; rfl

/-- Compatibility of `Substitution.toFunctorCompLiftIso` with the identity substitution. -/
theorem toFunctorCompLiftIso_id (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g)) :
    (id S).toFunctorCompLiftIso fo fc ≪≫
        MonoidalFunctor.toFunctorIso
          ((Interpretation.extension S D).map ((pullbackIdIso D).hom.app ⟨fo, fc⟩)).iso =
      Functor.isoWhiskerRight (toFunctorIdIso S) (FreeMonoidal.lift fo fc) ≪≫
        Functor.leftUnitor (FreeMonoidal.lift fo fc) := by
  ext X
  have h1 := toFunctorCompLiftIso_hom_app (id S) fo fc X
  have h2 := (Interpretation.extension_map_iso_hom_hom_hom_app
      ((pullbackIdIso D).hom.app ⟨fo, fc⟩) X).trans
    ((congrArg Iso.hom (projectObjIso_eqToIso _ X.as)).trans (eqToIso.hom _))
  have hLHS := (congrArg₂ (· ≫ ·) h1 h2).trans (eqToHom_trans _ _)
  have hRHS : (Functor.isoWhiskerRight (toFunctorIdIso S) (FreeMonoidal.lift fo fc) ≪≫
        Functor.leftUnitor (FreeMonoidal.lift fo fc)).hom.app X =
      eqToHom (congrArg (FreeMonoidal.lift fo fc).obj (toFunctor_id_obj S X)) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.id_obj,
      toFunctorIdIso_hom_app, eqToHom_map]
    exact Category.comp_id _
  exact hLHS.trans hRHS.symm

/-- Compatibility of `Substitution.toFunctorCompLiftIso` with successive pullback along a composite
substitution `σ.comp τ`. -/
theorem toFunctorCompLiftIso_comp {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (fo : U.Obj → D)
    (fc : ∀ h : U.Coupon, projectObj fo (U.src h) ⟶ projectObj fo (U.tgt h)) :
    (σ.comp τ).toFunctorCompLiftIso fo fc ≪≫
        MonoidalFunctor.toFunctorIso
          ((Interpretation.extension S D).map ((pullbackCompIso D σ τ).hom.app ⟨fo, fc⟩)).iso =
      Functor.isoWhiskerRight (toFunctorCompIso σ τ) (FreeMonoidal.lift fo fc) ≪≫
        Functor.associator σ.toFunctor τ.toFunctor (FreeMonoidal.lift fo fc) ≪≫
        Functor.isoWhiskerLeft σ.toFunctor (τ.toFunctorCompLiftIso fo fc) ≪≫
        σ.toFunctorCompLiftIso (τ.pullbackObj fo) (τ.pullbackCoupon fo fc) := by
  ext X
  have h1 := toFunctorCompLiftIso_hom_app (σ.comp τ) fo fc X
  have h2 := (Interpretation.extension_map_iso_hom_hom_hom_app
      ((pullbackCompIso D σ τ).hom.app ⟨fo, fc⟩) X).trans
    ((congrArg Iso.hom (projectObjIso_eqToIso _ X.as)).trans (eqToIso.hom _))
  have hLHS := (congrArg₂ (· ≫ ·) h1 h2).trans (eqToHom_trans _ _)
  have hRHS : (Functor.isoWhiskerRight (toFunctorCompIso σ τ) (FreeMonoidal.lift fo fc) ≪≫
        Functor.associator σ.toFunctor τ.toFunctor (FreeMonoidal.lift fo fc) ≪≫
        Functor.isoWhiskerLeft σ.toFunctor (τ.toFunctorCompLiftIso fo fc) ≪≫
        σ.toFunctorCompLiftIso (τ.pullbackObj fo) (τ.pullbackCoupon fo fc)).hom.app X =
      eqToHom ((congrArg (FreeMonoidal.lift fo fc).obj (toFunctor_comp_obj σ τ X)).trans
        ((τ.projectObj_pullbackObj fo (projectObj σ.obj X.as).as).symm.trans
          (σ.projectObj_pullbackObj (τ.pullbackObj fo) X.as).symm)) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, toFunctorCompIso_hom_app, toFunctorCompLiftIso_hom_app,
      Functor.comp_obj, eqToHom_map, Category.id_comp]
    exact (congrArg (eqToHom _ ≫ ·) (eqToHom_trans _ _)).trans (eqToHom_trans _ _)
  exact hLHS.trans hRHS.symm

end Pullback

/-- Equal substitutions have a monoidal `eqToIso` between their induced functors. -/
theorem isMonoidal_eqToIso_toFunctor_hom {S : TensorSignature.{u₁, v₁}}
    {T : TensorSignature.{u₂, v₂}} {σ₁ σ₂ : Substitution S T} (h : σ₁ = σ₂) :
    NatTrans.IsMonoidal (eqToIso (congrArg toFunctor h)).hom := by
  subst h
  simpa only [eqToIso_refl, Iso.refl_hom] using
    inferInstanceAs (NatTrans.IsMonoidal (𝟙 σ₁.toFunctor))

end Substitution

namespace Hom

/-- The strong monoidal functor `S.FreeMonoidal ⥤ T.FreeMonoidal` induced by a morphism of tensor
signatures `φ : Hom S T`. -/
abbrev toFunctor {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) : S.FreeMonoidal ⥤ T.FreeMonoidal :=
  φ.toSubstitution.toFunctor

theorem toFunctor_map_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    φ.toFunctor.map (FreeMonoidal.coupon g) =
      eqToHom (congrArg FreeMonoidal.mk (φ.src_coupon_projectObj_as g).symm) ≫
        FreeMonoidal.coupon (φ.coupon g) ≫
          eqToHom (congrArg FreeMonoidal.mk (φ.tgt_coupon_projectObj_as g)) := by
  rw [Substitution.toFunctor_map_coupon, toSubstitution_coupon, FreeMonoidal.homMk_cast,
    FreeMonoidal.homMk_coupon]

/-- The assignment of free monoidal categories `φ ↦ φ.toFunctor` is injective on signature
morphisms: distinct morphisms of tensor signatures induce distinct functors
`S.FreeMonoidal ⥤ T.FreeMonoidal`. -/
theorem toFunctor_injective {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} :
    Function.Injective (toFunctor (S := S) (T := T)) := by
  rintro ⟨o₁, c₁, hs₁, ht₁⟩ ⟨o₂, c₂, hs₂, ht₂⟩ h
  obtain rfl : o₁ = o₂ := funext fun a ↦
    FreeMonoidal.of_injective
      (congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj (FreeMonoidal.of a)) h)
  congr
  funext a
  let φ : Hom S T := ⟨o₁, c₁, hs₁, ht₁⟩
  let ψ : Hom S T := ⟨o₁, c₂, hs₂, ht₂⟩
  have hsrc : T.src (c₁ a) = T.src (c₂ a) := (hs₁ a).trans (hs₂ a).symm
  have htgt : T.tgt (c₁ a) = T.tgt (c₂ a) := (ht₁ a).trans (ht₂ a).symm
  have h' : φ.toFunctor = ψ.toFunctor := h
  have hsrc_obj :
      (⟨(projectObj φ.toSubstitution.obj (S.src a)).as⟩ : T.FreeMonoidal) =
        ⟨(projectObj ψ.toSubstitution.obj (S.src a)).as⟩ :=
    congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj ⟨S.src a⟩) h'
  have htgt_obj :
      (⟨(projectObj φ.toSubstitution.obj (S.tgt a)).as⟩ : T.FreeMonoidal) =
        ⟨(projectObj ψ.toSubstitution.obj (S.tgt a)).as⟩ :=
    congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj ⟨S.tgt a⟩) h'
  have hcongr : eqToHom (congrArg FreeMonoidal.mk (φ.src_coupon_projectObj_as a).symm) ≫
        FreeMonoidal.coupon (c₁ a) ≫
        eqToHom (congrArg FreeMonoidal.mk (φ.tgt_coupon_projectObj_as a)) =
      eqToHom hsrc_obj ≫
        (eqToHom (congrArg FreeMonoidal.mk (ψ.src_coupon_projectObj_as a).symm) ≫
          FreeMonoidal.coupon (c₂ a) ≫
          eqToHom (congrArg FreeMonoidal.mk (ψ.tgt_coupon_projectObj_as a))) ≫
        eqToHom htgt_obj.symm :=
    (φ.toFunctor_map_coupon a).symm.trans ((Functor.congr_hom h' (FreeMonoidal.coupon a)).trans
      (congrArg (eqToHom hsrc_obj ≫ · ≫ eqToHom htgt_obj.symm) (ψ.toFunctor_map_coupon a)))
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at hcongr
  refine (FreeMonoidal.coupon_eq_iff hsrc htgt).mp ?_
  simpa [Category.assoc] using hcongr

@[simp]
theorem toFunctor_inj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {φ ψ : Hom S T} : φ.toFunctor = ψ.toFunctor ↔ φ = ψ :=
  toFunctor_injective.eq_iff

/-- The strong monoidal functor induced by `Hom.id S` agrees on objects with the identity
functor. -/
theorem toFunctor_id_obj (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (Hom.id S).toFunctor.obj X = X := by
  rw [toFunctor, toSubstitution_id]
  exact FreeMonoidal.projectObj_of X.as

/-- The strong monoidal functor induced by `φ.comp ψ` agrees on objects with the composite functor
`φ.toFunctor ⋙ ψ.toFunctor`. -/
theorem toFunctor_comp_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) (X : S.FreeMonoidal) :
    (φ.comp ψ).toFunctor.obj X = (φ.toFunctor ⋙ ψ.toFunctor).obj X := by
  rw [toFunctor, toSubstitution_comp]
  exact (congrArg FreeMonoidal.mk (congrArg FreeMonoidal.as
    (FreeMonoidal.projectObj_projectObj ψ.toSubstitution.obj φ.toSubstitution.obj X.as))).symm

/-- The strong monoidal functor induced by the identity signature morphism `Hom.id S` is monoidally
naturally isomorphic to `𝟭 S.FreeMonoidal`. -/
def toFunctorIdIso (S : TensorSignature.{u, v}) : (Hom.id S).toFunctor ≅ 𝟭 S.FreeMonoidal :=
  eqToIso (congrArg Substitution.toFunctor (toSubstitution_id S)) ≪≫ Substitution.toFunctorIdIso S

instance (S : TensorSignature.{u, v}) : NatTrans.IsMonoidal (toFunctorIdIso S).hom := by
  have := Substitution.isMonoidal_eqToIso_toFunctor_hom (toSubstitution_id S)
  exact inferInstanceAs (NatTrans.IsMonoidal (_ ≫ _))

@[simp]
theorem toFunctorIdIso_hom_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).hom.app X = eqToHom (toFunctor_id_obj S X) := by
  rw [toFunctorIdIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Substitution.toFunctorIdIso_hom_app, eqToHom_trans]

@[simp]
theorem toFunctorIdIso_inv_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).inv.app X = eqToHom (toFunctor_id_obj S X).symm := by
  rw [toFunctorIdIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app,
    Substitution.toFunctorIdIso_inv_app, eqToHom_trans]

/-- The strong monoidal functor induced by a composite signature morphism `φ.comp ψ` is monoidally
naturally isomorphic to `φ.toFunctor ⋙ ψ.toFunctor`. -/
def toFunctorCompIso {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) :
    (φ.comp ψ).toFunctor ≅ φ.toFunctor ⋙ ψ.toFunctor :=
  eqToIso (congrArg Substitution.toFunctor (toSubstitution_comp φ ψ)) ≪≫
    Substitution.toFunctorCompIso φ.toSubstitution ψ.toSubstitution

instance {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) :
    NatTrans.IsMonoidal (toFunctorCompIso φ ψ).hom := by
  have := Substitution.isMonoidal_eqToIso_toFunctor_hom (toSubstitution_comp φ ψ)
  exact inferInstanceAs (NatTrans.IsMonoidal (_ ≫ _))

@[simp]
theorem toFunctorCompIso_hom_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) (X : S.FreeMonoidal) :
    (toFunctorCompIso φ ψ).hom.app X = eqToHom (toFunctor_comp_obj φ ψ X) := by
  rw [toFunctorCompIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Substitution.toFunctorCompIso_hom_app, eqToHom_trans]

@[simp]
theorem toFunctorCompIso_inv_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) (X : S.FreeMonoidal) :
    (toFunctorCompIso φ ψ).inv.app X = eqToHom (toFunctor_comp_obj φ ψ X).symm := by
  rw [toFunctorCompIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app,
    Substitution.toFunctorCompIso_inv_app, eqToHom_trans]

/-- Left unit coherence for `Hom.toFunctor`: composing `toFunctorCompIso (Hom.id S) φ` with
`toFunctorIdIso S` agrees with `Hom.id_comp φ`. -/
theorem toFunctorCompIso_id_left {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) :
    toFunctorCompIso (Hom.id S) φ ≪≫ Functor.isoWhiskerRight (toFunctorIdIso S) φ.toFunctor ≪≫
        Functor.leftUnitor φ.toFunctor = eqToIso (congrArg toFunctor (Hom.id_comp φ)) := by
  ext X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    toFunctorCompIso_hom_app, toFunctorIdIso_hom_app, eqToIso.hom, eqToHom_app, eqToHom_map,
    eqToHom_trans, Category.comp_id]

/-- Right unit coherence for `Hom.toFunctor`: composing `toFunctorCompIso φ (Hom.id T)` with
`toFunctorIdIso T` agrees with `Hom.comp_id φ`. -/
theorem toFunctorCompIso_id_right {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) :
    toFunctorCompIso φ (Hom.id T) ≪≫ Functor.isoWhiskerLeft φ.toFunctor (toFunctorIdIso T) ≪≫
        Functor.rightUnitor φ.toFunctor = eqToIso (congrArg toFunctor (Hom.comp_id φ)) := by
  ext X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    toFunctorCompIso_hom_app, toFunctorIdIso_hom_app, eqToIso.hom, eqToHom_app, eqToHom_trans,
    Category.comp_id]

/-- Associativity coherence (pentagon) for `Hom.toFunctorCompIso`. -/
theorem toFunctorCompIso_assoc {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} {V : TensorSignature.{u₄, v₄}}
    (φ : Hom S T) (ψ : Hom T U) (θ : Hom U V) :
    toFunctorCompIso (φ.comp ψ) θ ≪≫
        Functor.isoWhiskerRight (toFunctorCompIso φ ψ) θ.toFunctor ≪≫
        Functor.associator φ.toFunctor ψ.toFunctor θ.toFunctor =
      eqToIso (congrArg toFunctor (Hom.comp_assoc φ ψ θ)) ≪≫ toFunctorCompIso φ (ψ.comp θ) ≪≫
        Functor.isoWhiskerLeft φ.toFunctor (toFunctorCompIso ψ θ) := by
  ext X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.comp_obj, toFunctorCompIso_hom_app, eqToIso.hom,
    eqToHom_app, eqToHom_map, eqToHom_trans, Category.comp_id]

end Hom

end TauCeti.TensorSignature
