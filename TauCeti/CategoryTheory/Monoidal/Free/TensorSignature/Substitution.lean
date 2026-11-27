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
import TauCeti.CategoryTheory.EqToHom
import TauCeti.CategoryTheory.NatIso

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
  `TauCeti.TensorSignature.Substitution.pullbackCoupon_id`,
  `TauCeti.TensorSignature.Substitution.pullbackCoupon_comp`,
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
@[simp] theorem Hom.subst_cast (σ : Substitution S T) {X X' Y Y' : FreeMonoidalCategory S.Obj}
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

@[simp] theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ := FreeMonoidal.lift_ε _ _
@[simp] theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ := FreeMonoidal.lift_η _ _
@[simp] theorem toFunctor_μ (X Y : S.FreeMonoidal) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ := FreeMonoidal.lift_μ _ _ X Y
@[simp] theorem toFunctor_δ (X Y : S.FreeMonoidal) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ := FreeMonoidal.lift_δ _ _ X Y
@[simp] theorem toFunctor_obj (X : S.FreeMonoidal) : σ.toFunctor.obj X = projectObj σ.obj X.as :=
  rfl
@[simp] theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeMonoidal.coupon g) = FreeMonoidal.homMk (σ.coupon g) :=
  FreeMonoidal.lift_map_coupon _ _ g

/-- Interpreting a raw expression by the induced functor is the equivalence class of its
substitution. This is also the representative computation rule for the descended operation. -/
@[simp] theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : FreeMonoidal.Hom X Y) :
    σ.toFunctor.map (FreeMonoidal.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeMonoidal.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | coupon g => exact lift_map_coupon _ _ g
  | comp _ _ hf hg =>
    exact (liftMap_comp _ _ (homMk _) (homMk _)).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X _ hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ (homMk _)).trans (congrArg (projectObj σ.obj X ◁ ·) hf)
  | whiskerRight _ X hf =>
    exact (lift_map_whiskerRight _ _ (homMk _) ⟨X⟩).trans (congrArg (· ▷ projectObj σ.obj X) hf)
  | tensor _ _ hf hg =>
    exact (lift_map_tensorHom _ _ (homMk _) (homMk _)).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

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
  obtain ⟨_, _⟩ := σ; obtain ⟨_, _⟩ := σ'; subst hobj; congr; funext g
  exact eq_of_heq (hcoupon g)

variable (S) in
/-- The identity substitution, replacing each generating object and each coupon of `S` by
itself. -/
def id : Substitution S S where
  obj := FreeMonoidal.of
  coupon g := cast (by rw [FreeMonoidal.projectObj_of, FreeMonoidal.projectObj_of])
    (FreeMonoidal.Hom.coupon g)

@[simp] theorem id_obj : (Substitution.id S).obj = FreeMonoidal.of := (rfl)

/-- Interpreting a tensor word under the identity substitution gives the same underlying word. -/
theorem as_projectObj_id (X : FreeMonoidalCategory S.Obj) :
    (projectObj (Substitution.id S).obj X).as = X := by
  rw [id_obj, FreeMonoidal.projectObj_of]

/-- The identity substitution replaces a coupon by the coupon itself, up to the identification
of each word with its interpretation by its own generating objects (`projectObj_of`). -/
theorem id_coupon_heq (g : S.Coupon) :
    (Substitution.id S).coupon g ≍ FreeMonoidal.Hom.coupon g :=
  cast_heq _ _

/-- The identity substitution replaces a coupon by the coupon itself, up to endpoint casts
identifying each boundary word with its interpretation under `id_obj`. -/
@[simp] theorem id_coupon (g : S.Coupon) :
    (Substitution.id S).coupon g =
      (FreeMonoidal.Hom.coupon g).cast
        (as_projectObj_id (S.src g)).symm (as_projectObj_id (S.tgt g)).symm :=
  FreeMonoidal.Hom.eq_cast_of_heq _ _ (id_coupon_heq g)

variable {U : TensorSignature.{u'', v''}}

/-- The composite of the substitutions `σ` and `τ`: each generating object and each coupon of
`S` is replaced by its replacement under `σ`, into which `τ` is substituted. The order is
diagrammatic, as for `Functor.comp`: `σ` is applied first (`Substitution.toFunctor_comp`). -/
def comp (σ : Substitution S T) (τ : Substitution T U) : Substitution S U where
  obj a := projectObj τ.obj (σ.obj a).as
  coupon g :=
    cast (by rw [FreeMonoidal.projectObj_projectObj, FreeMonoidal.projectObj_projectObj])
      ((σ.coupon g).subst τ)

@[simp] theorem comp_obj (σ : Substitution S T) (τ : Substitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = projectObj τ.obj (σ.obj a).as := (rfl)

/-- Interpreting a tensor word under `σ` and then `τ` gives the same underlying word as
interpreting directly under `σ.comp τ`. -/
theorem as_projectObj_comp (σ : Substitution S T) (τ : Substitution T U)
    (X : FreeMonoidalCategory S.Obj) :
    (projectObj τ.obj (projectObj σ.obj X).as).as = (projectObj (σ.comp τ).obj X).as := by
  rw [FreeMonoidal.projectObj_projectObj,
    show (fun a ↦ projectObj τ.obj (σ.obj a).as) = (σ.comp τ).obj from funext (comp_obj σ τ)]

/-- The composite substitution replaces a coupon by the substitution of `τ` into its replacement
under `σ`, up to the identification of the boundary words given by `projectObj_projectObj`. -/
theorem comp_coupon_heq (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g ≍ (σ.coupon g).subst τ :=
  cast_heq _ _

/-- The composite substitution replaces a coupon by the substitution of `τ` into its replacement
under `σ`, up to endpoint casts from `as_projectObj_comp`. -/
@[simp] theorem comp_coupon (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g =
      ((σ.coupon g).subst τ).cast
        (as_projectObj_comp σ τ (S.src g)) (as_projectObj_comp σ τ (S.tgt g)) :=
  FreeMonoidal.Hom.eq_cast_of_heq _ _ (comp_coupon_heq σ τ g)

end Substitution

namespace FreeMonoidal

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}

/-- Substituting into heterogeneously equal raw expressions gives heterogeneously equal
results. -/
theorem Hom.subst_congr_heq (σ : Substitution S T) {X X' Y Y' : FreeMonoidalCategory S.Obj}
    {f : Hom X Y} {f' : Hom X' Y'} (hX : X = X') (hY : Y = Y') (h : f ≍ f') :
    f.subst σ ≍ f'.subst σ := by
  subst hX hY; rw [eq_of_heq h]

/-! The constructors of raw expressions respect heterogeneous equality, given equal words. -/

private theorem α_hom_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') : Hom.α_hom X Y Z ≍ Hom.α_hom X' Y' Z' := by subst hX hY hZ; rfl
private theorem α_inv_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} (hX : X = X')
    (hY : Y = Y') (hZ : Z = Z') : Hom.α_inv X Y Z ≍ Hom.α_inv X' Y' Z' := by subst hX hY hZ; rfl
private theorem comp_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj} {f : Hom X Y}
    {f' : Hom X' Y'} {g : Hom Y Z} {g' : Hom Y' Z'} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (hf : f ≍ f') (hg : g ≍ g') : f.comp g ≍ f'.comp g' := by
  subst hX hY hZ; rw [eq_of_heq hf, eq_of_heq hg]
private theorem whiskerLeft_heq {X X' Y₁ Y₁' Y₂ Y₂' : FreeMonoidalCategory S.Obj}
    {f : Hom Y₁ Y₂} {f' : Hom Y₁' Y₂'} (hX : X = X') (h₁ : Y₁ = Y₁') (h₂ : Y₂ = Y₂')
    (hf : f ≍ f') : f.whiskerLeft X ≍ f'.whiskerLeft X' := by subst hX h₁ h₂; rw [eq_of_heq hf]
private theorem whiskerRight_heq {X₁ X₁' X₂ X₂' Y Y' : FreeMonoidalCategory S.Obj}
    {f : Hom X₁ X₂} {f' : Hom X₁' X₂'} (h₁ : X₁ = X₁') (h₂ : X₂ = X₂') (hY : Y = Y')
    (hf : f ≍ f') : f.whiskerRight Y ≍ f'.whiskerRight Y' := by subst h₁ h₂ hY; rw [eq_of_heq hf]
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
  have h := Substitution.as_projectObj_id (S := S)
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
@[simp] theorem Hom.subst_substitutionId {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    f.subst (Substitution.id S) =
      f.cast (Substitution.as_projectObj_id X).symm (Substitution.as_projectObj_id Y).symm :=
  Hom.eq_cast_of_heq _ _ (Hom.subst_substitutionId_heq f)

variable {U : TensorSignature.{u'', v''}}

/-- Substituting `σ` and then `τ` into a raw expression is substituting their composite, up to
the identification of the boundary words given by `projectObj_projectObj`. -/
theorem Hom.subst_subst_heq (σ : Substitution S T) (τ : Substitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    (f.subst σ).subst τ ≍ f.subst (σ.comp τ) := by
  have h := Substitution.as_projectObj_comp σ τ
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
`σ.comp τ`, up to the endpoint casts given by `as_projectObj_comp`. -/
@[simp] theorem Hom.subst_subst (σ : Substitution S T) (τ : Substitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    (f.subst σ).subst τ =
      (f.subst (σ.comp τ)).cast
        (Substitution.as_projectObj_comp σ τ X).symm
        (Substitution.as_projectObj_comp σ τ Y).symm :=
  Hom.eq_cast_of_heq _ _ (Hom.subst_subst_heq σ τ f)

end FreeMonoidal

namespace Substitution

open FreeMonoidal

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}}

/-- The identity substitution is a left unit for composition. -/
@[simp] theorem id_comp (σ : Substitution S T) : (Substitution.id S).comp σ = σ :=
  hext rfl fun g ↦ (comp_coupon_heq _ σ g).trans
    (Hom.subst_congr_heq σ (congrArg FreeMonoidal.as (projectObj_of _))
      (congrArg FreeMonoidal.as (projectObj_of _)) (id_coupon_heq g))

/-- The identity substitution is a right unit for composition. -/
@[simp] theorem comp_id (σ : Substitution S T) : σ.comp (Substitution.id T) = σ :=
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
@[simp] theorem toFunctor_id : (Substitution.id S).toFunctor = 𝟭 S.FreeMonoidal := by
  refine Functor.hext (fun X ↦ projectObj_of X.as) fun ⟨X⟩ ⟨Y⟩ f ↦ ?_
  induction f using Quotient.inductionOn with | _ f
  exact ((Substitution.id S).toFunctor_map_homMk f).heq.trans
    (homMk_heq (congrArg FreeMonoidal.as (projectObj_of X))
      (congrArg FreeMonoidal.as (projectObj_of Y)) (Hom.subst_substitutionId_heq f))

/-- The functor induced by a composite substitution is the composite of the induced
functors. -/
@[simp] theorem toFunctor_comp (σ : Substitution S T) (τ : Substitution T U) :
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

@[simp] theorem toSubstitution_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (a : S.Obj) :
    φ.toSubstitution.obj a = FreeMonoidal.of (φ.obj a) := (rfl)

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

@[simp] theorem toSubstitution_coupon {S : TensorSignature.{u₁, v₁}}
    {T : TensorSignature.{u₂, v₂}} (φ : Hom S T) (g : S.Coupon) :
    φ.toSubstitution.coupon g = (FreeMonoidal.Hom.coupon (φ.coupon g)).cast
      (φ.src_coupon_projectObj_as g) (φ.tgt_coupon_projectObj_as g) := (rfl)

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

@[simp] theorem toSubstitution_inj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {φ ψ : Hom S T} : φ.toSubstitution = ψ.toSubstitution ↔ φ = ψ :=
  toSubstitution_injective.eq_iff

@[simp] theorem toSubstitution_id (S : TensorSignature.{u, v}) :
    (Hom.id S).toSubstitution = Substitution.id S := by
  refine Substitution.hext (funext fun a ↦ by simp) fun g ↦ ?_
  rw [toSubstitution_coupon]
  exact (Hom.cast_heq _ _ _).trans
    ((congr_arg_heq FreeMonoidal.Hom.coupon (Hom.id_coupon S g)).trans
      (Substitution.id_coupon_heq g).symm)

@[simp] theorem toSubstitution_comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
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
        (Substitution.as_projectObj_comp φ.toSubstitution σ (S.src g)))
      ((congrArg (fun W ↦ (projectObj σ.obj W).as) (φ.tgt_coupon_projectObj_as g)).trans
        (Substitution.as_projectObj_comp φ.toSubstitution σ (S.tgt g))) := by
  refine (Hom.eq_cast_of_heq (Substitution.as_projectObj_comp φ.toSubstitution σ (S.src g))
    (Substitution.as_projectObj_comp φ.toSubstitution σ (S.tgt g))
    (Substitution.comp_coupon_heq φ.toSubstitution σ g)).trans ?_
  rw [toSubstitution_coupon, Hom.subst_cast, Hom.subst_coupon, Hom.cast_cast]

end Hom

/-! ### Monoidal natural isomorphisms and coherence for induced functors -/

namespace Substitution

open FreeMonoidal

section Functoriality

/-- The strong monoidal functor induced by `Substitution.id S` agrees on objects with the
identity functor. -/
theorem toFunctor_id_obj (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (Substitution.id S).toFunctor.obj X = X := FreeMonoidal.projectObj_of X.as

private lemma isMonoidal_eqToIso_of_toFunctor
    {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) (G : S.FreeMonoidal ⥤ T.FreeMonoidal) [G.LaxMonoidal]
    (h : σ.toFunctor = G)
    (hε : Functor.LaxMonoidal.ε G =
      eqToHom (congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj (𝟙_ S.FreeMonoidal)) h))
    (hμ : ∀ X Y, Functor.LaxMonoidal.μ G X Y =
      eqToHom (by simp only [← h, toFunctor_obj, tensorObj_as, projectObj_tensorObj])) :
    NatTrans.IsMonoidal (eqToIso h).hom where
  unit := by
    simp only [eqToIso.hom, eqToHom_app, toFunctor_ε, hε]
    exact Category.id_comp _
  tensor X Y := by
    simp only [eqToIso.hom, eqToHom_app, toFunctor_μ, hμ, TauCeti.eqToHom_tensorHom_eqToHom]
    exact (Category.id_comp _).trans (eqToHom_trans _ _).symm

/-- The strong monoidal functor induced by `Substitution.id S` is monoidally naturally isomorphic
to the identity functor on `S.FreeMonoidal`. -/
def toFunctorIdIso (S : TensorSignature.{u, v}) :
    (Substitution.id S).toFunctor ≅ 𝟭 S.FreeMonoidal :=
  eqToIso toFunctor_id

instance (S : TensorSignature.{u, v}) : NatTrans.IsMonoidal (toFunctorIdIso S).hom :=
  isMonoidal_eqToIso_of_toFunctor (Substitution.id S) (𝟭 S.FreeMonoidal) toFunctor_id
    (by simp only [Functor.LaxMonoidal.id_ε]; exact (eqToHom_refl _ _).symm)
    (fun X Y ↦ by simp only [Functor.LaxMonoidal.id_μ]; exact (eqToHom_refl _ _).symm)

@[simp] theorem toFunctorIdIso_hom_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).hom.app X = eqToHom (toFunctor_id_obj S X) := by
  rw [toFunctorIdIso, eqToIso.hom, eqToHom_app]

@[simp] theorem toFunctorIdIso_inv_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).inv.app X = eqToHom (toFunctor_id_obj S X).symm := by
  rw [toFunctorIdIso, eqToIso.inv, eqToHom_app]

/-- The strong monoidal functor induced by `σ.comp τ` agrees on objects with the composite functor
`σ.toFunctor ⋙ τ.toFunctor`. -/
theorem toFunctor_comp_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    (X : S.FreeMonoidal) :
    (σ.comp τ).toFunctor.obj X = (σ.toFunctor ⋙ τ.toFunctor).obj X :=
  congrArg FreeMonoidal.mk (congrArg FreeMonoidal.as
    (FreeMonoidal.projectObj_projectObj τ.obj σ.obj X.as)).symm

/-- The strong monoidal functor induced by a composite substitution `σ.comp τ` is monoidally
naturally isomorphic to the composite functor `σ.toFunctor ⋙ τ.toFunctor`. -/
def toFunctorCompIso {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    (σ.comp τ).toFunctor ≅ σ.toFunctor ⋙ τ.toFunctor :=
  eqToIso (toFunctor_comp σ τ)

instance {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    NatTrans.IsMonoidal (toFunctorCompIso σ τ).hom :=
  isMonoidal_eqToIso_of_toFunctor (σ.comp τ) (σ.toFunctor ⋙ τ.toFunctor) (toFunctor_comp σ τ)
    (by
      simp only [Functor.LaxMonoidal.comp_ε, toFunctor_obj, tensorUnit_as, projectObj_tensorUnit,
        toFunctor_ε, CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).trans (eqToHom_refl _ _).symm)
    (fun X Y ↦ by
      simp only [Functor.LaxMonoidal.comp_μ, toFunctor_obj, tensorObj_as, projectObj_tensorObj,
        toFunctor_μ, CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).trans (eqToHom_refl _ _).symm)

@[simp] theorem toFunctorCompIso_hom_app {S : TensorSignature.{u₁, v₁}}
    {T : TensorSignature.{u₂, v₂}} {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T)
    (τ : Substitution T U) (X : S.FreeMonoidal) :
    (toFunctorCompIso σ τ).hom.app X = eqToHom (toFunctor_comp_obj σ τ X) := by
  rw [toFunctorCompIso, eqToIso.hom, eqToHom_app]

@[simp] theorem toFunctorCompIso_inv_app {S : TensorSignature.{u₁, v₁}}
    {T : TensorSignature.{u₂, v₂}} {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T)
    (τ : Substitution T U) (X : S.FreeMonoidal) :
    (toFunctorCompIso σ τ).inv.app X = eqToHom (toFunctor_comp_obj σ τ X).symm := by
  rw [toFunctorCompIso, eqToIso.inv, eqToHom_app]

/-- Left unit coherence for `Substitution.toFunctor`: composing `toFunctorCompIso (id S) σ` with
`toFunctorIdIso S` agrees with `Substitution.id_comp σ`. -/
theorem toFunctorCompIso_id_left {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) :
    toFunctorCompIso (id S) σ ≪≫ Functor.isoWhiskerRight (toFunctorIdIso S) σ.toFunctor ≪≫
        Functor.leftUnitor σ.toFunctor = eqToIso (congrArg toFunctor (id_comp σ)) :=
  NatIso.eq_eqToIso_of_hom_app_eqToHom _ _ fun X ↦ ⟨_, by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      toFunctorCompIso_hom_app, toFunctorIdIso_hom_app, eqToHom_map, Category.comp_id]
    rw [eqToHom_trans]⟩

/-- Right unit coherence for `Substitution.toFunctor`: composing `toFunctorCompIso σ (id T)` with
`toFunctorIdIso T` agrees with `Substitution.comp_id σ`. -/
theorem toFunctorCompIso_id_right {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) :
    toFunctorCompIso σ (id T) ≪≫ Functor.isoWhiskerLeft σ.toFunctor (toFunctorIdIso T) ≪≫
        Functor.rightUnitor σ.toFunctor = eqToIso (congrArg toFunctor (comp_id σ)) :=
  NatIso.eq_eqToIso_of_hom_app_eqToHom _ _ fun X ↦ ⟨_, by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      toFunctorCompIso_hom_app, toFunctorIdIso_hom_app, Category.comp_id]
    rw [eqToHom_trans]⟩

/-- Associativity coherence (pentagon) for `Substitution.toFunctorCompIso`. -/
theorem toFunctorCompIso_assoc {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} {V : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) (ρ : Substitution U V) :
    toFunctorCompIso (σ.comp τ) ρ ≪≫ Functor.isoWhiskerRight (toFunctorCompIso σ τ) ρ.toFunctor ≪≫
        Functor.associator σ.toFunctor τ.toFunctor ρ.toFunctor =
      eqToIso (congrArg toFunctor (comp_assoc σ τ ρ)) ≪≫ toFunctorCompIso σ (τ.comp ρ) ≪≫
        Functor.isoWhiskerLeft σ.toFunctor (toFunctorCompIso τ ρ) :=
  NatIso.eq_of_hom_app_eqToHom
    (fun X ↦ ⟨_, by
      simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Functor.associator_hom_app, Functor.comp_obj,
        toFunctorCompIso_hom_app, eqToHom_map, Category.comp_id]
      rw [eqToHom_trans]⟩)
    (fun X ↦ ⟨_, by
      simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.comp_obj, toFunctorCompIso_hom_app, eqToIso.hom,
        eqToHom_app]
      rw [eqToHom_trans, eqToHom_trans]⟩)

end Functoriality

/-! ### Change of signature for interpretations -/

section Pullback

variable {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
  {D : Type u₃} [Category.{v₃} D] [MonoidalCategory D]

/-- Pull back a generator-object assignment `fo : T.Obj → D` along a substitution
`σ : Substitution S T` by evaluating each replacing tensor word `σ.obj a` in `D`. -/
@[expose] def pullbackObj (σ : Substitution S T) (fo : T.Obj → D) : S.Obj → D :=
  fun a ↦ projectObj fo (σ.obj a).as

@[simp] theorem pullbackObj_apply (σ : Substitution S T) (fo : T.Obj → D) (a : S.Obj) :
    σ.pullbackObj fo a = projectObj fo (σ.obj a).as := (rfl)

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
          eqToHom (σ.projectObj_pullbackObj fo (S.tgt g)).symm := (rfl)

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
    (by simp only [Functor.comp_obj, toFunctor_obj, tensorUnit_as, projectObj_tensorUnit,
          lift_obj_tensorUnit, Functor.OplaxMonoidal.comp_η, toFunctor_η,
          CategoryTheory.Functor.map_id, lift_η, Category.comp_id, lift_ε]
        exact (eqToHom_refl _ _).symm)
    (fun _ _ ↦ by
        simp only [Functor.comp_obj, toFunctor_obj, tensorObj_as, projectObj_tensorObj,
          lift_obj_tensor, Functor.OplaxMonoidal.comp_δ, toFunctor_δ,
          CategoryTheory.Functor.map_id, lift_δ, Category.comp_id, lift_μ, Category.id_comp]
        exact TauCeti.eqToHom_tensorHom_eqToHom _ _)
    (fun g ↦ by
        symm
        rw [eqToHom_comp_iff, lift_map_coupon, pullbackCoupon_def, Functor.comp_map,
          toFunctor_map_coupon]
        -- `⟨S.src g⟩.as` is `S.src g` and `σ.toFunctor.obj ⟨X⟩` is `projectObj σ.obj X`
        -- definitionally, so both sides match up to proof irrelevance of `eqToHom`.
        rfl)

instance (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h)) :
    NatTrans.IsMonoidal (σ.toFunctorCompLiftIso fo fc).hom :=
  monoidalNatIsoOfEqObj_hom_isMonoidal _ _ _ _

@[simp] theorem toFunctorCompLiftIso_hom_app (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h))
    (X : S.FreeMonoidal) :
    (σ.toFunctorCompLiftIso fo fc).hom.app X =
      eqToHom (σ.projectObj_pullbackObj fo X.as).symm := monoidalNatIsoOfEqObj_hom_app _ _ _ _ X

@[simp] theorem toFunctorCompLiftIso_inv_app (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h))
    (X : S.FreeMonoidal) :
    (σ.toFunctorCompLiftIso fo fc).inv.app X =
      eqToHom (σ.projectObj_pullbackObj fo X.as) := monoidalNatIsoOfEqObj_inv_app _ _ _ _ X

private theorem projectObjIso_pullbackObj (σ : Substitution S T) {I J : Interpretation T D}
    (α : I ⟶ J) (X : FreeMonoidalCategory S.Obj) :
    projectObjIso (f := σ.pullbackObj I.obj) (g := σ.pullbackObj J.obj)
        (fun a ↦ projectObjIso α.iso (σ.obj a).as) X =
      eqToIso (σ.projectObj_pullbackObj I.obj X) ≪≫
        projectObjIso α.iso (projectObj σ.obj X).as ≪≫
        eqToIso (σ.projectObj_pullbackObj J.obj X).symm := by
  ext
  refine (congrArg Iso.hom
    (FreeMonoidalCategory.projectObjIso_projectObj α.iso (fun a ↦ (σ.obj a).as) X)).trans ?_
  simp only [Iso.trans_hom, eqToIso.hom]
  rw [FreeMonoidalCategory.projectObjIso_congr_word α.iso (FreeMonoidal.as_projectObj σ.obj X).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  -- The `eqToHom` endpoints match by proof irrelevance and `σ.projectObj_pullbackObj` defeq.
  rfl

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
    (FreeMonoidal.lift I.obj I.coupon).map (FreeMonoidal.homMk (σ.coupon g))
  let mJ : projectObj J.obj (projectObj σ.obj (S.src g)).as ⟶
      projectObj J.obj (projectObj σ.obj (S.tgt g)).as :=
    (FreeMonoidal.lift J.obj J.coupon).map (FreeMonoidal.homMk (σ.coupon g))
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
  refine (congrArg₂ (· ≫ ·) hl (congrArg Iso.hom (projectObjIso_pullbackObj σ α (S.tgt g)))).trans
    (Eq.trans ?_
      (congrArg₂ (· ≫ ·) (congrArg Iso.hom (projectObjIso_pullbackObj σ α (S.src g))) hr).symm)
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [reassoc_of% hnat]

variable (D) in
/-- Pull back interpretations of `T` in `D` and their isomorphisms along a substitution
`σ : Substitution S T`. -/
@[expose] def pullback (σ : Substitution S T) : Interpretation T D ⥤ Interpretation S D where
  obj I := ⟨σ.pullbackObj I.obj, σ.pullbackCoupon I.obj I.coupon⟩
  map α := { iso a := projectObjIso α.iso (σ.obj a).as, comm g := pullback_map_comm σ α g }
  map_id I := Interpretation.hom_ext fun a ↦
    (congrArg (fun e ↦ (projectObjIso e (σ.obj a).as).hom) (funext (Interpretation.id_iso I))).trans
      (congrArg Iso.hom (projectObjIso_refl (σ.obj a).as))
  map_comp α β := Interpretation.hom_ext fun a ↦
    (congrArg (fun e ↦ (projectObjIso e (σ.obj a).as).hom)
      (funext (Interpretation.comp_iso α β))).trans
      (congrArg Iso.hom (projectObjIso_trans _ _ (σ.obj a).as))

@[simp] theorem pullback_obj_obj (σ : Substitution S T) (I : Interpretation T D) :
    ((σ.pullback D).obj I).obj = σ.pullbackObj I.obj := (rfl)
@[simp] theorem pullback_obj_coupon (σ : Substitution S T) (I : Interpretation T D) :
    ((σ.pullback D).obj I).coupon = σ.pullbackCoupon I.obj I.coupon := (rfl)
@[simp] theorem pullback_map_iso (σ : Substitution S T) {I J : Interpretation T D} (α : I ⟶ J)
    (a : S.Obj) : ((σ.pullback D).map α).iso a = projectObjIso α.iso (σ.obj a).as := (rfl)

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
  have hp := congrArg Iso.hom (projectObjIso_pullbackObj σ α X.as)
  simp only [Iso.trans_hom, eqToIso.hom] at hp
  have h1 := (Interpretation.extension_map_iso_hom_hom_hom_app α (σ.toFunctor.obj X)).trans
    (FreeMonoidalCategory.projectObjIso_congr_word α.iso
      (congrArg FreeMonoidal.as (σ.toFunctor_obj X)))
  have h2 := toFunctorCompLiftIso_hom_app σ J.obj J.coupon X
  have h3 := toFunctorCompLiftIso_hom_app σ I.obj I.coupon X
  have h4 := ((Interpretation.extension_map_iso_hom_hom_hom_app ((σ.pullback D).map α) X).trans
    (congrArg (fun e ↦ (projectObjIso e X.as).hom)
      (funext (pullback_map_iso σ α)))).trans hp
  exact TauCeti.eq_of_heq_conj
    (m := (projectObjIso α.iso (projectObj σ.obj X.as).as).hom)
    ((heq_of_eq (congrArg₂ (· ≫ ·) h1 h2)).trans
      ((comp_eqToHom_heq _ _).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))))
    ((heq_of_eq (congrArg₂ (· ≫ ·) h3 h4)).trans
      ((eqToHom_comp_heq _ _).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))))
    HEq.rfl

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

@[simp] theorem precomp_obj_of (σ : Substitution S T)
    (F : Core (MonoidalFunctor T.FreeMonoidal D)) :
    ((σ.precomp D).obj F).of = MonoidalFunctor.of (σ.toFunctor ⋙ F.of.toFunctor) := (rfl)

@[simp] theorem precomp_map_iso_hom_hom_hom (σ : Substitution S T)
    {F G : Core (MonoidalFunctor T.FreeMonoidal D)} (α : F ⟶ G) :
    ((σ.precomp D).map α).iso.hom.hom.hom =
      Functor.whiskerLeft σ.toFunctor α.iso.hom.hom.hom := (rfl)

private def extensionPullbackApp (σ : Substitution S T) (I : Interpretation T D) :
    (Interpretation.extension T D ⋙ σ.precomp D).obj I ≅
      (σ.pullback D ⋙ Interpretation.extension S D).obj I :=
  (Groupoid.isoEquivHom _ _).symm <|
    ⟨@MonoidalFunctor.isoMk _ _ _ _ _ _ (.of _) (.of _) (σ.toFunctorCompLiftIso I.obj I.coupon)
      (inferInstanceAs (NatTrans.IsMonoidal (σ.toFunctorCompLiftIso I.obj I.coupon).hom))⟩

private lemma extensionPullbackApp_hom_iso_hom_hom_hom (σ : Substitution S T)
    (I : Interpretation T D) :
    (extensionPullbackApp (D := D) σ I).hom.iso.hom.hom.hom =
      (σ.toFunctorCompLiftIso I.obj I.coupon).hom := (rfl)

variable (D) in
/-- Naturality of extension under pullback: precomposing `Interpretation.extension` with
`σ.toFunctor` is naturally isomorphic to pulling back interpretations along `σ` and extending. -/
def extensionPullbackIso (σ : Substitution S T) :
    Interpretation.extension T D ⋙ σ.precomp D ≅
      σ.pullback D ⋙ Interpretation.extension S D :=
  NatIso.ofComponents (extensionPullbackApp σ) fun α ↦ by
    refine Core.hom_ext <| MonoidalFunctor.hom_ext <| ?_
    simp only [coreCategory_comp_iso, Iso.trans_hom, MonoidalFunctor.comp_hom,
      LaxMonoidalFunctor.comp_hom, Functor.comp_map, precomp_map_iso_hom_hom_hom,
      extensionPullbackApp_hom_iso_hom_hom_hom]
    exact toFunctorCompLiftIso_natural σ α

@[simp] theorem extensionPullbackIso_hom_app_iso_hom_hom_hom (σ : Substitution S T)
    (I : Interpretation T D) :
    ((σ.extensionPullbackIso D).hom.app I).iso.hom.hom.hom =
      (σ.toFunctorCompLiftIso I.obj I.coupon).hom :=
  extensionPullbackApp_hom_iso_hom_hom_hom σ I

/-- Pulling back a generator-object assignment along `Substitution.id S` returns the same
assignment. -/
theorem pullback_id_obj (fo : S.Obj → D) : (id S).pullbackObj fo = fo :=
  funext fun a ↦ by simp [pullbackObj]

private lemma lift_coupon_eq_of_eqToHom {fo fo' : S.Obj → D}
    {fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g)}
    {fc' : ∀ g : S.Coupon, projectObj fo' (S.src g) ⟶ projectObj fo' (S.tgt g)}
    (e : FreeMonoidal.lift fo' fc' ≅ FreeMonoidal.lift fo fc)
    {h : ∀ a, fo' a = fo a}
    (he : ∀ X : S.FreeMonoidal, e.hom.app X = eqToHom (projectObj_congr h X.as))
    (g : S.Coupon) :
    fc' g = eqToHom (projectObj_congr h (S.src g)) ≫ fc g ≫
      eqToHom (projectObj_congr h (S.tgt g)).symm := by
  have hnat := e.hom.naturality (FreeMonoidal.coupon g)
  simp only [he, FreeMonoidal.lift_map_coupon] at hnat
  exact ((comp_eqToHom_iff _ _ _).mp hnat).trans (Category.assoc _ _ _)

private lemma pullback_comm_of_eq {fo fo' : S.Obj → D}
    {fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g)}
    {fc' : ∀ g : S.Coupon, projectObj fo' (S.src g) ⟶ projectObj fo' (S.tgt g)}
    (h : fo' = fo)
    (hfc : ∀ g, fc' g = eqToHom (projectObj_congr (congrFun h) (S.src g)) ≫ fc g ≫
      eqToHom (projectObj_congr (congrFun h) (S.tgt g)).symm)
    (g : S.Coupon) :
    fc' g ≫ (projectObjIso (fun a ↦ eqToIso (congrFun h a)) (S.tgt g)).hom =
      (projectObjIso (fun a ↦ eqToIso (congrFun h a)) (S.src g)).hom ≫ fc g := by
  rw [hfc, projectObjIso_eqToIso, projectObjIso_eqToIso, eqToIso.hom, eqToIso.hom]
  simp

private lemma toFunctorCompLiftIso_id_rhs_hom_app (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))
    (X : S.FreeMonoidal) :
    (Functor.isoWhiskerRight (toFunctorIdIso S) (FreeMonoidal.lift fo fc) ≪≫
        Functor.leftUnitor (FreeMonoidal.lift fo fc)).hom.app X =
      eqToHom (congrArg (FreeMonoidal.lift fo fc).obj (toFunctor_id_obj S X)) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.id_obj,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, toFunctorIdIso_hom_app, eqToHom_map]
  exact Category.comp_id _

/-- Pulling back a coupon interpretation `(fo, fc)` along `Substitution.id S` recovers `fc`, up to
`eqToHom` transports along `pullback_id_obj`. -/
@[simp] theorem pullbackCoupon_id (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))
    (g : S.Coupon) :
    (id S).pullbackCoupon fo fc g =
      eqToHom (projectObj_congr (congrFun (pullback_id_obj fo)) (S.src g)) ≫
        fc g ≫
        eqToHom (projectObj_congr (congrFun (pullback_id_obj fo)) (S.tgt g)).symm :=
  lift_coupon_eq_of_eqToHom (h := congrFun (pullback_id_obj fo))
    (((id S).toFunctorCompLiftIso fo fc).symm ≪≫
      Functor.isoWhiskerRight (toFunctorIdIso S) (FreeMonoidal.lift fo fc) ≪≫
      Functor.leftUnitor (FreeMonoidal.lift fo fc))
    (fun X ↦ by
      rw [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, toFunctorCompLiftIso_inv_app,
        toFunctorCompLiftIso_id_rhs_hom_app]
      exact TauCeti.eq_of_heq_id ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _))
        (eqToHom_heq_id_cod _ _ _) (FreeMonoidal.lift_obj _ _ _))
    g

private theorem pullbackIdIso_naturality {I J : Interpretation S D} (α : I ⟶ J) (a : S.Obj) :
    (projectObjIso α.iso ((id S).obj a).as).hom ≫
        eqToHom (congrFun (pullback_id_obj J.obj) a) =
      eqToHom (congrFun (pullback_id_obj I.obj) a) ≫ (α.iso a).hom := by
  have hword := projectObjIso_congr_word α.iso
    ((congrArg FreeMonoidal.as (congrFun id_obj a)).trans (FreeMonoidal.of_as a))
  rw [projectObjIso_of] at hword; rw [hword]
  exact TauCeti.eq_of_heq_conj (m := (α.iso a).hom)
    ((comp_eqToHom_heq _ _).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)))
    (eqToHom_comp_heq _ _) HEq.rfl

private def pullbackIdIsoApp (I : Interpretation S D) :
    ((id S).pullback D).obj I ≅ (𝟭 (Interpretation S D)).obj I :=
  (Groupoid.isoEquivHom _ _).symm
    { iso a := eqToIso (congrFun (pullback_id_obj I.obj) a)
      comm g := pullback_comm_of_eq (pullback_id_obj I.obj) (pullbackCoupon_id I.obj I.coupon) g }

private lemma pullbackIdIsoApp_hom_iso (I : Interpretation S D) (a : S.Obj) :
    (pullbackIdIsoApp (D := D) I).hom.iso a = eqToIso (congrFun (pullback_id_obj I.obj) a) :=
  congrArg (fun k : ((id S).pullback D).obj I ⟶ (𝟭 (Interpretation S D)).obj I ↦ k.iso a)
    (Groupoid.isoEquivHom_symm_apply_hom _ _ _)

variable (D) in
/-- Pulling back interpretations along `Substitution.id S` is naturally isomorphic to the identity
functor on `Interpretation S D`. -/
def pullbackIdIso : (id S).pullback D ≅ 𝟭 (Interpretation S D) :=
  NatIso.ofComponents pullbackIdIsoApp
    fun α ↦ Interpretation.hom_ext fun a ↦ pullbackIdIso_naturality α a

@[simp] theorem pullbackIdIso_hom_app_iso (I : Interpretation S D) (a : S.Obj) :
    ((pullbackIdIso D).hom.app I).iso a = eqToIso (congrFun (pullback_id_obj I.obj) a) :=
  pullbackIdIsoApp_hom_iso I a

/-- Pulling back a generator-object assignment along `σ.comp τ` agrees with pulling back along
`τ` and then along `σ`. -/
theorem comp_pullbackObj {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (fo : U.Obj → D) :
    (σ.comp τ).pullbackObj fo = σ.pullbackObj (τ.pullbackObj fo) :=
  funext fun a ↦ by
    rw [pullbackObj_apply, comp_obj, pullbackObj_apply, FreeMonoidal.projectObj_projectObj]
    exact projectObj_congr (fun b ↦ (pullbackObj_apply τ fo b).symm) (σ.obj a).as

private lemma toFunctorCompLiftIso_comp_rhs_hom_app {U : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) (fo : U.Obj → D)
    (fc : ∀ h : U.Coupon, projectObj fo (U.src h) ⟶ projectObj fo (U.tgt h))
    (X : S.FreeMonoidal) :
    (Functor.isoWhiskerRight (toFunctorCompIso σ τ) (FreeMonoidal.lift fo fc) ≪≫
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
  exact TauCeti.eq_of_heq_id
    ((eqToHom_comp_heq _ _).trans ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _)))
    (eqToHom_heq_id_cod _ _ _)
    (FreeMonoidal.lift_obj _ (σ.pullbackCoupon _ (τ.pullbackCoupon fo fc)) X)

/-- Pulling back a coupon interpretation `(fo, fc)` along a composite substitution `σ.comp τ`
agrees with pulling back along `τ` and then along `σ`, up to `eqToHom` transports along
`comp_pullbackObj`. -/
@[simp] theorem pullbackCoupon_comp {U : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) (fo : U.Obj → D)
    (fc : ∀ h : U.Coupon, projectObj fo (U.src h) ⟶ projectObj fo (U.tgt h))
    (g : S.Coupon) :
    (σ.comp τ).pullbackCoupon fo fc g =
      eqToHom (projectObj_congr (congrFun (comp_pullbackObj σ τ fo)) (S.src g)) ≫
        σ.pullbackCoupon (τ.pullbackObj fo) (τ.pullbackCoupon fo fc) g ≫
        eqToHom (projectObj_congr (congrFun (comp_pullbackObj σ τ fo)) (S.tgt g)).symm :=
  lift_coupon_eq_of_eqToHom (h := congrFun (comp_pullbackObj σ τ fo))
    (((σ.comp τ).toFunctorCompLiftIso fo fc).symm ≪≫
      Functor.isoWhiskerRight (toFunctorCompIso σ τ) (FreeMonoidal.lift fo fc) ≪≫
      Functor.associator σ.toFunctor τ.toFunctor (FreeMonoidal.lift fo fc) ≪≫
      Functor.isoWhiskerLeft σ.toFunctor (τ.toFunctorCompLiftIso fo fc) ≪≫
      σ.toFunctorCompLiftIso (τ.pullbackObj fo) (τ.pullbackCoupon fo fc))
    (fun X ↦ by
      rw [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, toFunctorCompLiftIso_inv_app,
        toFunctorCompLiftIso_comp_rhs_hom_app]
      exact TauCeti.eq_of_heq_id ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _))
        (eqToHom_heq_id_cod _ _ _) rfl)
    g

private theorem pullbackCompIso_naturality {U : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) {I J : Interpretation U D} (α : I ⟶ J)
    (a : S.Obj) :
    (projectObjIso α.iso ((σ.comp τ).obj a).as).hom ≫
        eqToHom (congrFun (comp_pullbackObj σ τ J.obj) a) =
      eqToHom (congrFun (comp_pullbackObj σ τ I.obj) a) ≫
        (projectObjIso ((τ.pullback D).map α).iso (σ.obj a).as).hom := by
  have hp := congrArg Iso.hom (projectObjIso_pullbackObj τ α (σ.obj a).as)
  simp only [Iso.trans_hom, eqToIso.hom] at hp
  have hword := projectObjIso_congr_word α.iso (congrArg FreeMonoidal.as (comp_obj σ τ a))
  exact TauCeti.eq_of_heq_conj (m := (projectObjIso α.iso (projectObj τ.obj (σ.obj a).as).as).hom)
    ((heq_of_eq (congrArg (· ≫ _) hword)).trans
      ((comp_eqToHom_heq _ _).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))))
    ((heq_of_eq (congrArg (_ ≫ ·) hp)).trans
      ((eqToHom_comp_heq _ _).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))))
    HEq.rfl

private def pullbackCompIsoApp {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (I : Interpretation U D) :
    ((σ.comp τ).pullback D).obj I ≅ (τ.pullback D ⋙ σ.pullback D).obj I :=
  (Groupoid.isoEquivHom _ _).symm
    { iso a := eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a)
      comm g := pullback_comm_of_eq (comp_pullbackObj σ τ I.obj)
        (pullbackCoupon_comp σ τ I.obj I.coupon) g }

private lemma pullbackCompIsoApp_hom_iso {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (I : Interpretation U D) (a : S.Obj) :
    (pullbackCompIsoApp (D := D) σ τ I).hom.iso a =
      eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a) :=
  congrArg (fun k : ((σ.comp τ).pullback D).obj I ⟶ (τ.pullback D ⋙ σ.pullback D).obj I ↦
    k.iso a) (Groupoid.isoEquivHom_symm_apply_hom _ _ _)

variable (D) in
/-- Pulling back interpretations along `σ.comp τ` is naturally isomorphic to pulling back along
`τ` and then along `σ`. -/
def pullbackCompIso {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) :
    (σ.comp τ).pullback D ≅ τ.pullback D ⋙ σ.pullback D :=
  NatIso.ofComponents (pullbackCompIsoApp σ τ)
    fun α ↦ Interpretation.hom_ext fun a ↦ pullbackCompIso_naturality σ τ α a

@[simp] theorem pullbackCompIso_hom_app_iso {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (I : Interpretation U D) (a : S.Obj) :
    ((pullbackCompIso D σ τ).hom.app I).iso a =
      eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a) :=
  pullbackCompIsoApp_hom_iso σ τ I a

private theorem pullback_eqToIso_hom_app_iso {σ₁ σ₂ : Substitution S T} (h : σ₁ = σ₂)
    (I : Interpretation T D) (a : S.Obj) :
    (((eqToIso (congrArg (pullback D) h)).hom.app I).iso a).hom =
      eqToHom (congrArg (fun K : Interpretation S D ↦ K.obj a)
        (Functor.congr_obj (congrArg (pullback D) h) I)) := by
  subst h; simp

private theorem pullback_map_eqToIso_hom (σ : Substitution S T) {I J : Interpretation T D}
    {α : I ⟶ J} {h : ∀ b, I.obj b = J.obj b} (hα : ∀ b, α.iso b = eqToIso (h b)) (a : S.Obj) :
    (((σ.pullback D).map α).iso a).hom = eqToHom (projectObj_congr h (σ.obj a).as) := by
  rw [pullback_map_iso, funext hα, projectObjIso_eqToIso, eqToIso.hom]

variable (D) in
/-- Left unit coherence for `Substitution.pullback`: composing `pullbackCompIso D (id S) σ` with
`pullbackIdIso D` (in contravariant order) agrees with `Substitution.id_comp σ`. -/
theorem pullbackCompIso_id_left (σ : Substitution S T) :
    pullbackCompIso D (id S) σ ≪≫ Functor.isoWhiskerLeft (σ.pullback D) (pullbackIdIso D) ≪≫
        Functor.rightUnitor (σ.pullback D) = eqToIso (congrArg (pullback D) (id_comp σ)) := by
  ext I a
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Interpretation.comp_iso, Category.comp_id]
  have hL := congrArg₂ (· ≫ ·)
    (congrArg Iso.hom (pullbackCompIso_hom_app_iso (id S) σ I a))
    (congrArg Iso.hom (pullbackIdIso_hom_app_iso ((σ.pullback D).obj I) a))
  simp only [eqToIso.hom] at hL
  exact TauCeti.eq_of_heq_id
    ((heq_of_eq hL).trans ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _)))
    ((heq_of_eq (pullback_eqToIso_hom_app_iso (id_comp σ) I a)).trans (eqToHom_heq_id_cod _ _ _))
    (congrFun (pullback_obj_obj σ I) a).symm

variable (D) in
/-- Right unit coherence for `Substitution.pullback`: composing `pullbackCompIso D σ (id T)` with
`pullbackIdIso D` (in contravariant order) agrees with `Substitution.comp_id σ`. -/
theorem pullbackCompIso_id_right (σ : Substitution S T) :
    pullbackCompIso D σ (id T) ≪≫ Functor.isoWhiskerRight (pullbackIdIso D) (σ.pullback D) ≪≫
        Functor.leftUnitor (σ.pullback D) = eqToIso (congrArg (pullback D) (comp_id σ)) := by
  ext I a
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Interpretation.comp_iso, Category.comp_id]
  have h1 := congrArg Iso.hom (pullbackCompIso_hom_app_iso σ (id T) I a)
  simp only [eqToIso.hom] at h1
  exact TauCeti.eq_of_heq_id
    ((heq_of_eq (congrArg₂ (· ≫ ·) h1
      (pullback_map_eqToIso_hom σ (pullbackIdIso_hom_app_iso I) a))).trans
      ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _)))
    ((heq_of_eq (pullback_eqToIso_hom_app_iso (comp_id σ) I a)).trans (eqToHom_heq_id_cod _ _ _))
    (by rw [Functor.id_obj, pullback_obj_obj, pullbackObj_apply])

variable (D) in
/-- Associativity coherence (pentagon) for `Substitution.pullbackCompIso` in contravariant
composition order. -/
theorem pullbackCompIso_assoc {U : TensorSignature.{u₄, v₄}} {V : TensorSignature.{u', v'}}
    (σ : Substitution S T) (τ : Substitution T U) (ρ : Substitution U V) :
    pullbackCompIso D (σ.comp τ) ρ ≪≫
        Functor.isoWhiskerLeft (ρ.pullback D) (pullbackCompIso D σ τ) =
      eqToIso (congrArg (pullback D) (comp_assoc σ τ ρ)) ≪≫ pullbackCompIso D σ (τ.comp ρ) ≪≫
        Functor.isoWhiskerRight (pullbackCompIso D τ ρ) (σ.pullback D) ≪≫
        Functor.associator (ρ.pullback D) (τ.pullback D) (σ.pullback D) := by
  ext I a
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.comp_obj, Interpretation.comp_iso, Category.comp_id]
  have hL := congrArg₂ (· ≫ ·)
    (congrArg Iso.hom (pullbackCompIso_hom_app_iso (σ.comp τ) ρ I a))
    (congrArg Iso.hom (pullbackCompIso_hom_app_iso σ τ ((ρ.pullback D).obj I) a))
  have hR2 := congrArg Iso.hom (pullbackCompIso_hom_app_iso σ (τ.comp ρ) I a)
  simp only [eqToIso.hom] at hL hR2
  have hR := congrArg₂ (· ≫ ·) (pullback_eqToIso_hom_app_iso (comp_assoc σ τ ρ) I a)
    (congrArg₂ (· ≫ ·) hR2 (pullback_map_eqToIso_hom σ (pullbackCompIso_hom_app_iso τ ρ I) a))
  exact TauCeti.eq_of_heq_id
    ((heq_of_eq hL).trans ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _)))
    ((heq_of_eq hR).trans
      ((eqToHom_comp_heq _ _).trans ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _))))
    (by rw [Functor.comp_obj, pullback_obj_obj, pullback_obj_obj, pullback_obj_obj,
      pullbackObj_apply])

private theorem extension_map_eqToIso_hom {I J : Interpretation S D}
    {α : I ⟶ J} {h : ∀ a, I.obj a = J.obj a} (hα : ∀ a, α.iso a = eqToIso (h a))
    (X : S.FreeMonoidal) :
    ((Interpretation.extension S D).map α).iso.hom.hom.hom.app X =
      eqToHom (projectObj_congr h X.as) := by
  rw [Interpretation.extension_map_iso_hom_hom_hom_app, funext hα, projectObjIso_eqToIso,
    eqToIso.hom]

/-- Compatibility of `Substitution.toFunctorCompLiftIso` with the identity substitution. -/
theorem toFunctorCompLiftIso_id (fo : S.Obj → D)
    (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g)) :
    (id S).toFunctorCompLiftIso fo fc ≪≫
        MonoidalFunctor.toFunctorIso
          ((Interpretation.extension S D).map ((pullbackIdIso D).hom.app ⟨fo, fc⟩)).iso =
      Functor.isoWhiskerRight (toFunctorIdIso S) (FreeMonoidal.lift fo fc) ≪≫
        Functor.leftUnitor (FreeMonoidal.lift fo fc) := by
  ext X
  refine (congrArg₂ (· ≫ ·) (toFunctorCompLiftIso_hom_app (id S) fo fc X)
    (extension_map_eqToIso_hom (pullbackIdIso_hom_app_iso ⟨fo, fc⟩) X)).trans ?_
  rw [toFunctorCompLiftIso_id_rhs_hom_app]
  exact TauCeti.eq_of_heq_id ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _))
    (eqToHom_heq_id_cod _ _ _) (by rw [Functor.id_obj, FreeMonoidal.lift_obj])

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
  refine (congrArg₂ (· ≫ ·) (toFunctorCompLiftIso_hom_app (σ.comp τ) fo fc X)
    (extension_map_eqToIso_hom (pullbackCompIso_hom_app_iso σ τ ⟨fo, fc⟩) X)).trans ?_
  rw [toFunctorCompLiftIso_comp_rhs_hom_app]
  exact TauCeti.eq_of_heq_id ((eqToHom_comp_heq _ _).trans (eqToHom_heq_id_cod _ _ _))
    (eqToHom_heq_id_cod _ _ _) (by rw [Functor.comp_obj, pullback_obj_obj, pullback_obj_obj])

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
    (φ : Hom S T) : S.FreeMonoidal ⥤ T.FreeMonoidal := φ.toSubstitution.toFunctor

theorem toFunctor_map_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    φ.toFunctor.map (FreeMonoidal.coupon g) =
      eqToHom (congrArg FreeMonoidal.mk (φ.src_coupon_projectObj_as g).symm) ≫
        FreeMonoidal.coupon (φ.coupon g) ≫
          eqToHom (congrArg FreeMonoidal.mk (φ.tgt_coupon_projectObj_as g)) := by
  rw [Substitution.toFunctor_map_coupon, toSubstitution_coupon, FreeMonoidal.homMk_cast,
    FreeMonoidal.homMk_coupon]

private lemma coupon_eq_of_toFunctor_eq {S : TensorSignature.{u₁, v₁}}
    {T : TensorSignature.{u₂, v₂}} {φ ψ : Hom S T}
    (h : φ.toFunctor = ψ.toFunctor) (hobj : φ.obj = ψ.obj) (g : S.Coupon) :
    φ.coupon g = ψ.coupon g := by
  have hsrc : T.src (φ.coupon g) = T.src (ψ.coupon g) := by rw [φ.src_coupon, ψ.src_coupon, hobj]
  have htgt : T.tgt (φ.coupon g) = T.tgt (ψ.coupon g) := by rw [φ.tgt_coupon, ψ.tgt_coupon, hobj]
  refine (FreeMonoidal.coupon_eq_iff hsrc htgt).mp ?_
  have hsrc_obj : (⟨(projectObj φ.toSubstitution.obj (S.src g)).as⟩ : T.FreeMonoidal) =
      ⟨(projectObj ψ.toSubstitution.obj (S.src g)).as⟩ :=
    congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj ⟨S.src g⟩) h
  have htgt_obj : (⟨(projectObj φ.toSubstitution.obj (S.tgt g)).as⟩ : T.FreeMonoidal) =
      ⟨(projectObj ψ.toSubstitution.obj (S.tgt g)).as⟩ :=
    congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj ⟨S.tgt g⟩) h
  have hcongr : _ = eqToHom hsrc_obj ≫
      (eqToHom (congrArg FreeMonoidal.mk (ψ.src_coupon_projectObj_as g).symm) ≫
        FreeMonoidal.coupon (ψ.coupon g) ≫
        eqToHom (congrArg FreeMonoidal.mk (ψ.tgt_coupon_projectObj_as g))) ≫
      eqToHom htgt_obj.symm :=
    (φ.toFunctor_map_coupon g).symm.trans <| (Functor.congr_hom h (FreeMonoidal.coupon g)).trans <|
      congrArg (eqToHom hsrc_obj ≫ · ≫ eqToHom htgt_obj.symm) (ψ.toFunctor_map_coupon g)
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at hcongr
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans] at hcongr
  exact hcongr

/-- The assignment of free monoidal categories `φ ↦ φ.toFunctor` is injective on signature
morphisms: distinct morphisms of tensor signatures induce distinct functors
`S.FreeMonoidal ⥤ T.FreeMonoidal`. -/
theorem toFunctor_injective {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} :
    Function.Injective (toFunctor (S := S) (T := T)) := by
  intro φ ψ h
  have hobj : φ.obj = ψ.obj := funext fun a ↦ FreeMonoidal.of_injective
    (congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj (FreeMonoidal.of a)) h)
  exact Hom.ext hobj (funext (coupon_eq_of_toFunctor_eq h hobj))

@[simp] theorem toFunctor_inj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {φ ψ : Hom S T} : φ.toFunctor = ψ.toFunctor ↔ φ = ψ := toFunctor_injective.eq_iff

/-- The strong monoidal functor induced by `Hom.id S` agrees on objects with the identity
functor. -/
theorem toFunctor_id_obj (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (Hom.id S).toFunctor.obj X = X := by
  rw [toFunctor, toSubstitution_id]; exact FreeMonoidal.projectObj_of X.as

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

instance (S : TensorSignature.{u, v}) : NatTrans.IsMonoidal (toFunctorIdIso S).hom :=
  have := Substitution.isMonoidal_eqToIso_toFunctor_hom (toSubstitution_id S)
  inferInstanceAs (NatTrans.IsMonoidal (_ ≫ _))

@[simp] theorem toFunctorIdIso_hom_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).hom.app X = eqToHom (toFunctor_id_obj S X) := by
  rw [toFunctorIdIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Substitution.toFunctorIdIso_hom_app, eqToHom_trans]

@[simp] theorem toFunctorIdIso_inv_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
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
    NatTrans.IsMonoidal (toFunctorCompIso φ ψ).hom :=
  have := Substitution.isMonoidal_eqToIso_toFunctor_hom (toSubstitution_comp φ ψ)
  inferInstanceAs (NatTrans.IsMonoidal (_ ≫ _))

@[simp] theorem toFunctorCompIso_hom_app {S : TensorSignature.{u₁, v₁}}
    {T : TensorSignature.{u₂, v₂}} {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U)
    (X : S.FreeMonoidal) :
    (toFunctorCompIso φ ψ).hom.app X = eqToHom (toFunctor_comp_obj φ ψ X) := by
  rw [toFunctorCompIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Substitution.toFunctorCompIso_hom_app, eqToHom_trans]

@[simp] theorem toFunctorCompIso_inv_app {S : TensorSignature.{u₁, v₁}}
    {T : TensorSignature.{u₂, v₂}} {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U)
    (X : S.FreeMonoidal) :
    (toFunctorCompIso φ ψ).inv.app X = eqToHom (toFunctor_comp_obj φ ψ X).symm := by
  rw [toFunctorCompIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app,
    Substitution.toFunctorCompIso_inv_app, eqToHom_trans]

/-- Left unit coherence for `Hom.toFunctor`: composing `toFunctorCompIso (Hom.id S) φ` with
`toFunctorIdIso S` agrees with `Hom.id_comp φ`. -/
theorem toFunctorCompIso_id_left {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) :
    toFunctorCompIso (Hom.id S) φ ≪≫ Functor.isoWhiskerRight (toFunctorIdIso S) φ.toFunctor ≪≫
        Functor.leftUnitor φ.toFunctor = eqToIso (congrArg toFunctor (Hom.id_comp φ)) :=
  have key : ∀ {σ₀ σc} (h₀ : σ₀ = Substitution.id S) (hc : σc = σ₀.comp φ.toSubstitution)
      (hc' : σc.toFunctor = φ.toFunctor),
      (eqToIso (congrArg Substitution.toFunctor hc) ≪≫
        Substitution.toFunctorCompIso σ₀ φ.toSubstitution) ≪≫ Functor.isoWhiskerRight
        (eqToIso (congrArg Substitution.toFunctor h₀) ≪≫ Substitution.toFunctorIdIso S)
        φ.toFunctor ≪≫ Functor.leftUnitor φ.toFunctor = eqToIso hc' := by
    rintro _ _ rfl rfl _; simpa using Substitution.toFunctorCompIso_id_left φ.toSubstitution
  key (toSubstitution_id S) (toSubstitution_comp (Hom.id S) φ) _

/-- Right unit coherence for `Hom.toFunctor`: composing `toFunctorCompIso φ (Hom.id T)` with
`toFunctorIdIso T` agrees with `Hom.comp_id φ`. -/
theorem toFunctorCompIso_id_right {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) :
    toFunctorCompIso φ (Hom.id T) ≪≫ Functor.isoWhiskerLeft φ.toFunctor (toFunctorIdIso T) ≪≫
        Functor.rightUnitor φ.toFunctor = eqToIso (congrArg toFunctor (Hom.comp_id φ)) :=
  have key : ∀ {σ₀ σc} (h₀ : σ₀ = Substitution.id T) (hc : σc = φ.toSubstitution.comp σ₀)
      (hc' : σc.toFunctor = φ.toFunctor),
      (eqToIso (congrArg Substitution.toFunctor hc) ≪≫
        Substitution.toFunctorCompIso φ.toSubstitution σ₀) ≪≫ Functor.isoWhiskerLeft φ.toFunctor
        (eqToIso (congrArg Substitution.toFunctor h₀) ≪≫ Substitution.toFunctorIdIso T) ≪≫
        Functor.rightUnitor φ.toFunctor = eqToIso hc' := by
    rintro _ _ rfl rfl _; simpa using Substitution.toFunctorCompIso_id_right φ.toSubstitution
  key (toSubstitution_id T) (toSubstitution_comp φ (Hom.id T)) _

/-- Associativity coherence (pentagon) for `Hom.toFunctorCompIso`. -/
theorem toFunctorCompIso_assoc {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} {V : TensorSignature.{u₄, v₄}}
    (φ : Hom S T) (ψ : Hom T U) (θ : Hom U V) :
    toFunctorCompIso (φ.comp ψ) θ ≪≫
        Functor.isoWhiskerRight (toFunctorCompIso φ ψ) θ.toFunctor ≪≫
        Functor.associator φ.toFunctor ψ.toFunctor θ.toFunctor =
      eqToIso (congrArg toFunctor (Hom.comp_assoc φ ψ θ)) ≪≫ toFunctorCompIso φ (ψ.comp θ) ≪≫
        Functor.isoWhiskerLeft φ.toFunctor (toFunctorCompIso ψ θ) :=
  have key : ∀ {σ₁₂ : Substitution S U} {σ₂₃ : Substitution T V} {σL σR : Substitution S V}
      (h₁₂ : σ₁₂ = φ.toSubstitution.comp ψ.toSubstitution)
      (h₂₃ : σ₂₃ = ψ.toSubstitution.comp θ.toSubstitution)
      (hL : σL = σ₁₂.comp θ.toSubstitution) (hR : σR = φ.toSubstitution.comp σ₂₃)
      (hLR : σL.toFunctor = σR.toFunctor),
      (eqToIso (congrArg Substitution.toFunctor hL) ≪≫
        Substitution.toFunctorCompIso σ₁₂ θ.toSubstitution) ≪≫ Functor.isoWhiskerRight
        (eqToIso (congrArg Substitution.toFunctor h₁₂) ≪≫
          Substitution.toFunctorCompIso φ.toSubstitution ψ.toSubstitution) θ.toFunctor ≪≫
        Functor.associator φ.toFunctor ψ.toFunctor θ.toFunctor = eqToIso hLR ≪≫
        (eqToIso (congrArg Substitution.toFunctor hR) ≪≫
          Substitution.toFunctorCompIso φ.toSubstitution σ₂₃) ≪≫ Functor.isoWhiskerLeft φ.toFunctor
        (eqToIso (congrArg Substitution.toFunctor h₂₃) ≪≫
          Substitution.toFunctorCompIso ψ.toSubstitution θ.toSubstitution) := by
    rintro _ _ _ _ rfl rfl rfl rfl _
    simpa using
      Substitution.toFunctorCompIso_assoc φ.toSubstitution ψ.toSubstitution θ.toSubstitution
  key (toSubstitution_comp φ ψ) (toSubstitution_comp ψ θ)
    (toSubstitution_comp (φ.comp ψ) θ) (toSubstitution_comp φ (ψ.comp θ)) _

end Hom

end TauCeti.TensorSignature
