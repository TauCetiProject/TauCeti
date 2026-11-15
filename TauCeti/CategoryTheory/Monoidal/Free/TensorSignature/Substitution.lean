/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.EqToHom
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Hom

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

Substitutions have an identity `Substitution.id` and associative composition `Substitution.comp`
across arbitrary signature universes, satisfying strict two-sided unit and associativity laws.
Signature morphisms `TensorSignature.Hom` embed faithfully into substitutions via
`Hom.toSubstitution` compatibly with identities and composition. On free monoidal categories,
identity and composite substitutions induce canonical monoidal natural isomorphisms
`Substitution.toFunctorIdIso` and `Substitution.toFunctorCompIso`, and composing a substitution
with a universal interpretation `FreeMonoidal.lift` in an arbitrary (not necessarily strict)
monoidal category is canonically monoidally isomorphic to the pulled-back lift
(`Substitution.toFunctorCompLiftIso`).

## Main definitions and results

* `TauCeti.TensorSignature.Substitution`: typed substitutions between tensor signatures across
  independent universes, with `Substitution.id`, `Substitution.comp`, `Substitution.id_comp`,
  `Substitution.comp_id`, and `Substitution.comp_assoc`.
* `TauCeti.TensorSignature.FreeMonoidal.Hom.subst`,
  `TauCeti.TensorSignature.FreeMonoidal.Hom.id_subst`, and
  `TauCeti.TensorSignature.FreeMonoidal.Hom.subst_subst`: raw expression substitution and its
  identity and composition laws.
* `TauCeti.TensorSignature.Hom.toSubstitution`, `TauCeti.TensorSignature.Hom.toFunctor`,
  `TauCeti.TensorSignature.Hom.toFunctor_injective`, `TauCeti.TensorSignature.Hom.toFunctorIdIso`,
  and `TauCeti.TensorSignature.Hom.toFunctorCompIso`: faithful functorial embedding of signature
  morphisms into substitutions and induced strong monoidal functors between free monoidal
  categories.
* `TauCeti.TensorSignature.Substitution.toFunctor`,
  `TauCeti.TensorSignature.Substitution.toFunctorIdIso`, and
  `TauCeti.TensorSignature.Substitution.toFunctorCompIso`: strong monoidal functoriality of
  substitution on free monoidal categories.
* `TauCeti.TensorSignature.Substitution.pullbackObj`,
  `TauCeti.TensorSignature.Substitution.pullbackCoupon`, and
  `TauCeti.TensorSignature.Substitution.toFunctorCompLiftIso`: change-of-signature monoidal
  natural isomorphism for `FreeMonoidal.lift` into any monoidal category.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1
  (tensor schemes and their interpretations).
-/

public section

universe u v u' v' u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

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

/-- Raw substitution commutes with endpoint casts. -/
theorem Hom.subst_cast (σ : Substitution S T) {X X' Y Y' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (f : Hom X Y) :
    (f.cast hX hY).subst σ =
      (f.subst σ).cast (congrArg (fun W ↦ (projectObj σ.obj W).as) hX)
        (congrArg (fun W ↦ (projectObj σ.obj W).as) hY) := by
  subst hX hY
  rfl

end FreeMonoidal

end RawSubst

/-! ### Identity, composition, and associativity of substitutions -/

namespace Substitution

open FreeMonoidal

/-- Extensionality for substitutions whose object maps agree pointwise, transporting the coupon
replacements along the resulting boundary equalities via `FreeMonoidal.Hom.cast`. -/
theorem ext_cast {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {σ₁ σ₂ : Substitution S T} (hobj : ∀ a, σ₁.obj a = σ₂.obj a)
    (hcoupon : ∀ g, (σ₁.coupon g).cast
      (congrArg FreeMonoidal.as (projectObj_congr hobj (S.src g)))
      (congrArg FreeMonoidal.as (projectObj_congr hobj (S.tgt g))) = σ₂.coupon g) :
    σ₁ = σ₂ := by
  obtain ⟨o₁, c₁⟩ := σ₁
  obtain ⟨o₂, c₂⟩ := σ₂
  obtain rfl : o₁ = o₂ := funext hobj
  congr
  funext g
  exact (Hom.cast_rfl _).symm.trans (hcoupon g)

/-- The identity substitution on a tensor signature `S`, sending each generating object to itself
and each coupon to itself. -/
@[expose] def id (S : TensorSignature.{u, v}) : Substitution S S where
  obj := FreeMonoidal.of
  coupon g := (FreeMonoidal.Hom.coupon g).cast
    (projectObj_of_as (S.src g)).symm (projectObj_of_as (S.tgt g)).symm

@[simp]
theorem id_obj (S : TensorSignature.{u, v}) (a : S.Obj) :
    (id S).obj a = FreeMonoidal.of a :=
  rfl

@[simp]
theorem id_coupon (S : TensorSignature.{u, v}) (g : S.Coupon) :
    (id S).coupon g =
      (FreeMonoidal.Hom.coupon g).cast
        (projectObj_of_as (S.src g)).symm (projectObj_of_as (S.tgt g)).symm :=
  rfl

/-- Evaluating a formal tensor word along `σ` and then `τ` unwraps to the same tensor word as
evaluating along the composite object assignment `fun a ↦ projectObj τ.obj (σ.obj a).as`. -/
theorem comp_projectObj_as {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    (W : FreeMonoidalCategory S.Obj) :
    (projectObj τ.obj (projectObj σ.obj W).as).as =
      (projectObj (fun a ↦ projectObj τ.obj (σ.obj a).as) W).as :=
  congrArg FreeMonoidal.as (projectObj_projectObj_as τ.obj σ.obj W)

/-- Diagrammatic composition of substitutions across independent signature universes: first apply
`σ : Substitution S T`, then apply `τ : Substitution T U` to the resulting expressions. -/
@[expose] def comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    Substitution S U where
  obj a := projectObj τ.obj (σ.obj a).as
  coupon g := ((σ.coupon g).subst τ).cast
    (comp_projectObj_as σ τ (S.src g)) (comp_projectObj_as σ τ (S.tgt g))

@[simp]
theorem comp_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = projectObj τ.obj (σ.obj a).as :=
  rfl

@[simp]
theorem comp_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g = ((σ.coupon g).subst τ).cast
      (comp_projectObj_as σ τ (S.src g)) (comp_projectObj_as σ τ (S.tgt g)) :=
  rfl

end Substitution

namespace FreeMonoidal

/-- Substituting the identity substitution into any raw formal morphism returns that morphism,
transported along `projectObj_of_as`. -/
theorem Hom.id_subst {S : TensorSignature.{u, v}} {X Y : FreeMonoidalCategory S.Obj}
    (f : Hom X Y) :
    f.subst (Substitution.id S) =
      f.cast (projectObj_of_as X).symm (projectObj_of_as Y).symm := by
  induction f with
  | id X => exact (Hom.cast_id (projectObj_of_as X).symm _ _).symm
  | α_hom X Y Z =>
    exact (Hom.cast_α_hom (projectObj_of_as X).symm (projectObj_of_as Y).symm
      (projectObj_of_as Z).symm _ _).symm
  | α_inv X Y Z =>
    exact (Hom.cast_α_inv (projectObj_of_as X).symm (projectObj_of_as Y).symm
      (projectObj_of_as Z).symm _ _).symm
  | l_hom X => exact (Hom.cast_l_hom (projectObj_of_as X).symm _ _).symm
  | l_inv X => exact (Hom.cast_l_inv (projectObj_of_as X).symm _ _).symm
  | ρ_hom X => exact (Hom.cast_ρ_hom (projectObj_of_as X).symm _ _).symm
  | ρ_inv X => exact (Hom.cast_ρ_inv (projectObj_of_as X).symm _ _).symm
  | coupon g => rfl
  | comp f g ihf ihg =>
    rw [Hom.subst_comp, ihf, ihg]
    exact Hom.cast_comp _ _ _ f g
  | whiskerLeft X f ih =>
    rw [Hom.subst_whiskerLeft, ih]
    exact Hom.cast_whiskerLeft (projectObj_of_as X).symm _ _ f _ _
  | whiskerRight f X ih =>
    rw [Hom.subst_whiskerRight, ih]
    exact Hom.cast_whiskerRight _ _ (projectObj_of_as X).symm f _ _
  | tensor f g ihf ihg =>
    rw [Hom.subst_tensor, ihf, ihg]
    exact Hom.cast_tensor _ _ _ _ f g _ _

/-- Applying two raw substitutions successively agrees with applying their composite
`σ.comp τ`. -/
theorem Hom.subst_subst {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    (f.subst σ).subst τ =
      (f.subst (σ.comp τ)).cast (Substitution.comp_projectObj_as σ τ X).symm
        (Substitution.comp_projectObj_as σ τ Y).symm := by
  induction f with
  | id X => exact (Hom.cast_id (Substitution.comp_projectObj_as σ τ X).symm _ _).symm
  | α_hom X Y Z =>
    exact (Hom.cast_α_hom (Substitution.comp_projectObj_as σ τ X).symm
      (Substitution.comp_projectObj_as σ τ Y).symm
      (Substitution.comp_projectObj_as σ τ Z).symm _ _).symm
  | α_inv X Y Z =>
    exact (Hom.cast_α_inv (Substitution.comp_projectObj_as σ τ X).symm
      (Substitution.comp_projectObj_as σ τ Y).symm
      (Substitution.comp_projectObj_as σ τ Z).symm _ _).symm
  | l_hom X => exact (Hom.cast_l_hom (Substitution.comp_projectObj_as σ τ X).symm _ _).symm
  | l_inv X => exact (Hom.cast_l_inv (Substitution.comp_projectObj_as σ τ X).symm _ _).symm
  | ρ_hom X => exact (Hom.cast_ρ_hom (Substitution.comp_projectObj_as σ τ X).symm _ _).symm
  | ρ_inv X => exact (Hom.cast_ρ_inv (Substitution.comp_projectObj_as σ τ X).symm _ _).symm
  | coupon g =>
    dsimp only [Hom.subst, Substitution.comp]
    simp
  | comp f g ihf ihg =>
    dsimp only [Hom.subst]
    rw [ihf, ihg]
    exact Hom.cast_comp _ _ _ _ _
  | whiskerLeft X f ih =>
    dsimp only [Hom.subst]
    rw [ih]
    exact Hom.cast_whiskerLeft (Substitution.comp_projectObj_as σ τ X).symm _ _ _ _ _
  | whiskerRight f X ih =>
    dsimp only [Hom.subst]
    rw [ih]
    exact Hom.cast_whiskerRight _ _ (Substitution.comp_projectObj_as σ τ X).symm _ _ _
  | tensor f g ihf ihg =>
    dsimp only [Hom.subst]
    rw [ihf, ihg]
    exact Hom.cast_tensor _ _ _ _ _ _ _ _

end FreeMonoidal

namespace Substitution

open FreeMonoidal

@[simp]
theorem id_comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) : (id S).comp σ = σ := by
  refine ext_cast (fun _ ↦ rfl) fun g ↦ eq_of_heq ?_
  dsimp only [id, comp]
  rw [Hom.subst_cast, Hom.subst_coupon]
  exact (Hom.cast_heq _ _ _).trans ((Hom.cast_heq _ _ _).trans (Hom.cast_heq _ _ _))

@[simp]
theorem comp_id {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) : σ.comp (id T) = σ := by
  refine ext_cast (fun a ↦ projectObj_of_self (σ.obj a)) fun g ↦ eq_of_heq ?_
  dsimp only [comp]
  rw [Hom.id_subst]
  exact (Hom.cast_heq _ _ _).trans ((Hom.cast_heq _ _ _).trans (Hom.cast_heq _ _ _))

theorem comp_assoc {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} {V : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) (ρ : Substitution U V) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  refine ext_cast (fun a ↦ projectObj_projectObj_as ρ.obj τ.obj (σ.obj a).as) fun g ↦ eq_of_heq ?_
  dsimp only [comp]
  rw [Hom.subst_cast, Hom.subst_subst]
  exact ((Hom.cast_heq _ _ _).trans
    ((Hom.cast_heq _ _ _).trans ((Hom.cast_heq _ _ _).trans (Hom.cast_heq _ _ _)))).trans
    (Hom.cast_heq _ _ _).symm

end Substitution

/-! ### Embedding signature morphisms into substitutions -/

namespace Hom

open FreeMonoidal

/-- Boundary compatibility for embedding a signature morphism `φ : Hom S T` as a substitution. -/
theorem src_coupon_projectObj_as {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    T.src (φ.coupon g) = (projectObj (FreeMonoidal.of ∘ φ.obj) (S.src g)).as :=
  (φ.src_coupon g).trans (projectObj_as (FreeMonoidal.of ∘ φ.obj) (S.src g)).symm

/-- Target compatibility for embedding a signature morphism `φ : Hom S T` as a substitution. -/
theorem tgt_coupon_projectObj_as {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    T.tgt (φ.coupon g) = (projectObj (FreeMonoidal.of ∘ φ.obj) (S.tgt g)).as :=
  (φ.tgt_coupon g).trans (projectObj_as (FreeMonoidal.of ∘ φ.obj) (S.tgt g)).symm

/-- View a tensor-signature morphism as a substitution sending each generating object `a` to
`FreeMonoidal.of (φ.obj a)` and each coupon `g` to `Hom.coupon (φ.coupon g)`. -/
@[expose] def toSubstitution {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) : Substitution S T where
  obj := FreeMonoidal.of ∘ φ.obj
  coupon g := (FreeMonoidal.Hom.coupon (φ.coupon g)).cast
    (φ.src_coupon_projectObj_as g) (φ.tgt_coupon_projectObj_as g)

@[simp]
theorem toSubstitution_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (a : S.Obj) :
    φ.toSubstitution.obj a = FreeMonoidal.of (φ.obj a) :=
  rfl

@[simp]
theorem toSubstitution_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    φ.toSubstitution.coupon g = (FreeMonoidal.Hom.coupon (φ.coupon g)).cast
      (φ.src_coupon_projectObj_as g) (φ.tgt_coupon_projectObj_as g) :=
  rfl

/-- The embedding of signature morphisms into substitutions is injective. -/
theorem toSubstitution_injective {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}} :
    Function.Injective (toSubstitution (S := S) (T := T)) := by
  intro φ ψ h
  ext a
  · exact FreeMonoidal.of_injective (congrArg (fun σ ↦ σ.obj a) h)
  · have hc := congrArg (fun σ : Substitution S T ↦ (σ.coupon a).coupons) h
    dsimp only [toSubstitution] at hc
    simpa using hc

@[simp]
theorem toSubstitution_inj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {φ ψ : Hom S T} : φ.toSubstitution = ψ.toSubstitution ↔ φ = ψ :=
  toSubstitution_injective.eq_iff

@[simp]
theorem toSubstitution_id (S : TensorSignature.{u, v}) :
    (Hom.id S).toSubstitution = Substitution.id S := by
  refine Substitution.ext_cast (fun _ ↦ rfl) fun g ↦ eq_of_heq ?_
  dsimp only [toSubstitution, Substitution.id, Hom.id]
  exact ((Hom.cast_heq _ _ _).trans (Hom.cast_heq _ _ _)).trans (Hom.cast_heq _ _ _).symm

@[simp]
theorem toSubstitution_comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) :
    (φ.comp ψ).toSubstitution = φ.toSubstitution.comp ψ.toSubstitution := by
  refine Substitution.ext_cast (fun _ ↦ rfl) fun g ↦ eq_of_heq ?_
  dsimp only [toSubstitution, Substitution.comp, Hom.comp]
  rw [FreeMonoidal.Hom.subst_cast, FreeMonoidal.Hom.subst_coupon]
  exact ((Hom.cast_heq _ _ _).trans (Hom.cast_heq _ _ _)).trans
    ((Hom.cast_heq _ _ _).trans ((Hom.cast_heq _ _ _).trans (Hom.cast_heq _ _ _))).symm

/-- Precomposing a substitution `σ : Substitution T U` with a signature morphism `φ : Hom S T`
evaluates `σ` on the renamed generators and coupons. -/
theorem toSubstitution_comp_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (σ : Substitution T U) (a : S.Obj) :
    (φ.toSubstitution.comp σ).obj a = σ.obj (φ.obj a) :=
  rfl

/-- Precomposing a substitution `σ : Substitution T U` with a signature morphism `φ : Hom S T`
replaces each coupon `g` of `S` by `σ.coupon (φ.coupon g)` up to boundary transport. -/
theorem toSubstitution_comp_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (σ : Substitution T U) (g : S.Coupon) :
    (φ.toSubstitution.comp σ).coupon g = (σ.coupon (φ.coupon g)).cast
      ((congrArg (fun W ↦ (projectObj σ.obj W).as) (φ.src_coupon_projectObj_as g)).trans
        (Substitution.comp_projectObj_as φ.toSubstitution σ (S.src g)))
      ((congrArg (fun W ↦ (projectObj σ.obj W).as) (φ.tgt_coupon_projectObj_as g)).trans
        (Substitution.comp_projectObj_as φ.toSubstitution σ (S.tgt g))) := by
  apply eq_of_heq
  dsimp only [Substitution.comp, toSubstitution]
  rw [FreeMonoidal.Hom.subst_cast, FreeMonoidal.Hom.subst_coupon]
  exact ((Hom.cast_heq _ _ _).trans (Hom.cast_heq _ _ _)).trans (Hom.cast_heq _ _ _).symm

end Hom

/-! ### Induced strong monoidal functors and monoidal natural isomorphisms -/

namespace FreeMonoidal

section MonoidalNatIsoOfEqObj

variable {S : TensorSignature.{u, v}} {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {F G : S.FreeMonoidal ⥤ D} [F.Monoidal] [G.Monoidal]

/-- When two strong monoidal functors out of `S.FreeMonoidal` have pointwise equal object maps
compatibly with their unit and tensor comparison morphisms, the canonical word isomorphism built
from `eqToIso` at the generators reduces to `eqToHom` on every formal tensor word. -/
theorem wordIso_eqToIso_hom (hobj : ∀ X, F.obj X = G.obj X)
    (hunit : Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε G = eqToHom (hobj (𝟙_ _)))
    (htensor : ∀ X Y, Functor.OplaxMonoidal.δ F X Y ≫
      (eqToHom (hobj X) ⊗ₘ eqToHom (hobj Y)) ≫ Functor.LaxMonoidal.μ G X Y =
        eqToHom (hobj (X ⊗ Y)))
    (X : FreeMonoidalCategory S.Obj) :
    (wordIso F G (fun a ↦ eqToIso (hobj (of a))) X).hom = eqToHom (hobj ⟨X⟩) := by
  induction X with
  | of a =>
    rw [← of_as, wordIso_of, eqToIso.hom]
  | unit => exact (wordIso_tensorUnit_hom F G _).trans hunit
  | tensor X Y ihX ihY =>
    refine (wordIso_tensor_hom F G _ ⟨X⟩ ⟨Y⟩).trans ?_
    rw [ihX, ihY]
    exact htensor ⟨X⟩ ⟨Y⟩

/-- Construct a monoidal natural isomorphism `F ≅ G` between strong monoidal functors out of
`S.FreeMonoidal` whose object maps agree propositionally, whose monoidal structure morphisms
conjugate `eqToHom`, and whose actions on coupons agree up to `eqToHom`. -/
def monoidalNatIsoOfEqObj (hobj : ∀ X, F.obj X = G.obj X)
    (hunit : Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε G = eqToHom (hobj (𝟙_ _)))
    (htensor : ∀ X Y, Functor.OplaxMonoidal.δ F X Y ≫
      (eqToHom (hobj X) ⊗ₘ eqToHom (hobj Y)) ≫ Functor.LaxMonoidal.μ G X Y =
        eqToHom (hobj (X ⊗ Y)))
    (hcoupon : ∀ g, F.map (coupon g) ≫ eqToHom (hobj ⟨S.tgt g⟩) =
      eqToHom (hobj ⟨S.src g⟩) ≫ G.map (coupon g)) :
    F ≅ G :=
  monoidalNatIso (e := fun a ↦ eqToIso (hobj (of a))) fun g ↦ by
    rw [wordIso_eqToIso_hom hobj hunit htensor, wordIso_eqToIso_hom hobj hunit htensor]
    exact hcoupon g

@[simp]
theorem monoidalNatIsoOfEqObj_hom_app (hobj : ∀ X, F.obj X = G.obj X)
    (hunit : Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε G = eqToHom (hobj (𝟙_ _)))
    (htensor : ∀ X Y, Functor.OplaxMonoidal.δ F X Y ≫
      (eqToHom (hobj X) ⊗ₘ eqToHom (hobj Y)) ≫ Functor.LaxMonoidal.μ G X Y =
        eqToHom (hobj (X ⊗ Y)))
    (hcoupon : ∀ g, F.map (coupon g) ≫ eqToHom (hobj ⟨S.tgt g⟩) =
      eqToHom (hobj ⟨S.src g⟩) ≫ G.map (coupon g))
    (X : S.FreeMonoidal) :
    (monoidalNatIsoOfEqObj hobj hunit htensor hcoupon).hom.app X = eqToHom (hobj X) :=
  (monoidalNatIso_hom_app _ X).trans (wordIso_eqToIso_hom hobj hunit htensor X.as)

@[simp]
theorem monoidalNatIsoOfEqObj_inv_app (hobj : ∀ X, F.obj X = G.obj X)
    (hunit : Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε G = eqToHom (hobj (𝟙_ _)))
    (htensor : ∀ X Y, Functor.OplaxMonoidal.δ F X Y ≫
      (eqToHom (hobj X) ⊗ₘ eqToHom (hobj Y)) ≫ Functor.LaxMonoidal.μ G X Y =
        eqToHom (hobj (X ⊗ Y)))
    (hcoupon : ∀ g, F.map (coupon g) ≫ eqToHom (hobj ⟨S.tgt g⟩) =
      eqToHom (hobj ⟨S.src g⟩) ≫ G.map (coupon g))
    (X : S.FreeMonoidal) :
    (monoidalNatIsoOfEqObj hobj hunit htensor hcoupon).inv.app X = eqToHom (hobj X).symm := by
  rw [← cancel_epi ((monoidalNatIsoOfEqObj hobj hunit htensor hcoupon).hom.app X),
    Iso.hom_inv_id_app, monoidalNatIsoOfEqObj_hom_app, eqToHom_trans, eqToHom_refl]

instance monoidalNatIsoOfEqObj_hom_isMonoidal (hobj : ∀ X, F.obj X = G.obj X)
    (hunit : Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε G = eqToHom (hobj (𝟙_ _)))
    (htensor : ∀ X Y, Functor.OplaxMonoidal.δ F X Y ≫
      (eqToHom (hobj X) ⊗ₘ eqToHom (hobj Y)) ≫ Functor.LaxMonoidal.μ G X Y =
        eqToHom (hobj (X ⊗ Y)))
    (hcoupon : ∀ g, F.map (coupon g) ≫ eqToHom (hobj ⟨S.tgt g⟩) =
      eqToHom (hobj ⟨S.src g⟩) ≫ G.map (coupon g)) :
    NatTrans.IsMonoidal (monoidalNatIsoOfEqObj hobj hunit htensor hcoupon).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (monoidalNatIso _).hom)

end MonoidalNatIsoOfEqObj

end FreeMonoidal

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
    σ.toFunctor.obj X = projectObj σ.obj X.as := rfl

@[simp]
theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeMonoidal.coupon g) = FreeMonoidal.homMk (σ.coupon g) :=
  FreeMonoidal.lift_map_coupon _ _ g

/-- Interpreting a raw expression by the induced functor is the equivalence class of its
substitution. This is also the representative computation rule for the descended operation. -/
@[simp]
theorem toFunctor_map_homMk {X Y : S.FreeMonoidal} (f : FreeMonoidal.Hom X.as Y.as) :
    σ.toFunctor.map (FreeMonoidal.homMk f) =
      FreeMonoidal.homMk (X := projectObj σ.obj X.as) (Y := projectObj σ.obj Y.as) (f.subst σ) := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  dsimp only at f ⊢
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

section Functoriality

private theorem comp_eqToHom_of_eq {C : Type*} [Category* C] {X X' Y Y' : C}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : f = eqToHom hX ≫ g ≫ eqToHom hY.symm) :
    f ≫ eqToHom hY = eqToHom hX ≫ g := by
  subst hX hY
  simpa using h

private theorem comp_eqToHom_of_symm_eq {C : Type*} [Category* C] {X X' Y Y' : C}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : g = eqToHom hX.symm ≫ f ≫ eqToHom hY) :
    f ≫ eqToHom hY = eqToHom hX ≫ g := by
  subst hX hY
  simpa using h.symm

/-- The strong monoidal functor induced by the identity substitution is monoidally naturally
isomorphic to the identity functor on `S.FreeMonoidal`. -/
def toFunctorIdIso (S : TensorSignature.{u, v}) :
    (Substitution.id S).toFunctor ≅ 𝟭 S.FreeMonoidal :=
  monoidalNatIsoOfEqObj
    (fun X ↦ projectObj_of_self X)
    (by
      simp only [toFunctor_obj, tensorUnit_as, projectObj_tensorUnit, Functor.id_obj, toFunctor_η,
        Functor.LaxMonoidal.id_ε, Category.comp_id]
      exact (eqToHom_refl _ _).symm)
    (fun _ _ ↦ by
      simp only [toFunctor_obj, tensorObj_as, projectObj_tensorObj, Functor.id_obj, toFunctor_δ,
        Functor.LaxMonoidal.id_μ, Category.comp_id, Category.id_comp]
      exact TauCeti.eqToHom_tensorHom_eqToHom _ _)
    (fun g ↦ comp_eqToHom_of_eq _ _ ((toFunctor_map_coupon _ g).trans (homMk_cast _ _ _)))

instance (S : TensorSignature.{u, v}) : NatTrans.IsMonoidal (toFunctorIdIso S).hom :=
  monoidalNatIsoOfEqObj_hom_isMonoidal _ _ _ _

@[simp]
theorem toFunctorIdIso_hom_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).hom.app X = eqToHom (projectObj_of_self X) :=
  monoidalNatIsoOfEqObj_hom_app _ _ _ _ X

@[simp]
theorem toFunctorIdIso_inv_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).inv.app X = eqToHom (projectObj_of_self X).symm :=
  monoidalNatIsoOfEqObj_inv_app _ _ _ _ X

/-- The strong monoidal functor induced by a composite substitution `σ.comp τ` is monoidally
naturally isomorphic to the composite functor `σ.toFunctor ⋙ τ.toFunctor`. -/
def toFunctorCompIso {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    (σ.comp τ).toFunctor ≅ σ.toFunctor ⋙ τ.toFunctor :=
  monoidalNatIsoOfEqObj
    (fun X ↦ (projectObj_projectObj_as τ.obj σ.obj X.as).symm)
    (by
      simp only [toFunctor_obj, tensorUnit_as, projectObj_tensorUnit, Functor.comp_obj, toFunctor_η,
        Functor.LaxMonoidal.comp_ε, toFunctor_ε, Functor.map_id, Category.comp_id]
      exact (eqToHom_refl _ _).symm)
    (fun _ _ ↦ by
      simp only [toFunctor_obj, tensorObj_as, projectObj_tensorObj, Functor.comp_obj, toFunctor_δ,
        Functor.LaxMonoidal.comp_μ, toFunctor_μ, Functor.map_id, Category.comp_id, Category.id_comp]
      exact TauCeti.eqToHom_tensorHom_eqToHom _ _)
    (fun g ↦
      have hmap : homMk (X := projectObj τ.obj (projectObj σ.obj (S.src g)).as)
          (Y := projectObj τ.obj (projectObj σ.obj (S.tgt g)).as) ((σ.coupon g).subst τ) =
          (σ.toFunctor ⋙ τ.toFunctor).map (FreeMonoidal.coupon g) :=
        (toFunctor_map_homMk τ (σ.coupon g)).symm.trans
          (congrArg τ.toFunctor.map (toFunctor_map_coupon σ g)).symm
      comp_eqToHom_of_eq _ _ ((toFunctor_map_coupon (σ.comp τ) g).trans
        ((homMk_cast _ _ _).trans (congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _) hmap))))

instance {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    NatTrans.IsMonoidal (toFunctorCompIso σ τ).hom :=
  monoidalNatIsoOfEqObj_hom_isMonoidal _ _ _ _

@[simp]
theorem toFunctorCompIso_hom_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    (X : S.FreeMonoidal) :
    (toFunctorCompIso σ τ).hom.app X =
      eqToHom (projectObj_projectObj_as τ.obj σ.obj X.as).symm :=
  monoidalNatIsoOfEqObj_hom_app _ _ _ _ X

@[simp]
theorem toFunctorCompIso_inv_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    (X : S.FreeMonoidal) :
    (toFunctorCompIso σ τ).inv.app X =
      eqToHom (projectObj_projectObj_as τ.obj σ.obj X.as) :=
  monoidalNatIsoOfEqObj_inv_app _ _ _ _ X

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
  rfl

/-- Evaluating a formal tensor word of `S` along `σ.pullbackObj fo` agrees with evaluating its
`σ`-substituted word along `fo`, in any (not necessarily strict) monoidal category `D`. -/
theorem projectObj_pullbackObj (σ : Substitution S T) (fo : T.Obj → D)
    (X : FreeMonoidalCategory S.Obj) :
    projectObj (σ.pullbackObj fo) X = projectObj fo (projectObj σ.obj X).as :=
  (projectObj_projectObj_as fo σ.obj X).symm

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

/-- Change-of-signature compatibility: precomposing `FreeMonoidal.lift fo fc` with `σ.toFunctor`
is monoidally naturally isomorphic to `FreeMonoidal.lift` of the pulled-back interpretation
`(σ.pullbackObj fo, σ.pullbackCoupon fo fc)` in any monoidal category `D`. -/
def toFunctorCompLiftIso (σ : Substitution S T) (fo : T.Obj → D)
    (fc : ∀ h : T.Coupon, projectObj fo (T.src h) ⟶ projectObj fo (T.tgt h)) :
    σ.toFunctor ⋙ FreeMonoidal.lift fo fc ≅
      FreeMonoidal.lift (σ.pullbackObj fo) (σ.pullbackCoupon fo fc) :=
  monoidalNatIsoOfEqObj
    (fun X ↦ (σ.projectObj_pullbackObj fo X.as).symm)
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
    (fun g ↦ comp_eqToHom_of_symm_eq _ _
      ((lift_map_coupon _ _ g).trans
        (congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _)
          (congrArg (FreeMonoidal.lift fo fc).map (toFunctor_map_coupon σ g)).symm)))

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

end Pullback

/-- Equal substitutions induce monoidally naturally isomorphic functors via `eqToIso`. -/
def toFunctorEqIso {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {σ₁ σ₂ : Substitution S T} (h : σ₁ = σ₂) : σ₁.toFunctor ≅ σ₂.toFunctor :=
  eqToIso (congrArg toFunctor h)

instance {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {σ₁ σ₂ : Substitution S T} (h : σ₁ = σ₂) :
    NatTrans.IsMonoidal (toFunctorEqIso h).hom := by
  subst h
  simpa only [toFunctorEqIso, eqToIso_refl, Iso.refl_hom] using
    inferInstanceAs (NatTrans.IsMonoidal (𝟙 σ₁.toFunctor))

@[simp]
theorem toFunctorEqIso_hom_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {σ₁ σ₂ : Substitution S T} (h : σ₁ = σ₂) (X : S.FreeMonoidal) :
    (toFunctorEqIso h).hom.app X =
      eqToHom (congrArg (fun σ : Substitution S T ↦ σ.toFunctor.obj X) h) := by
  subst h
  rfl

@[simp]
theorem toFunctorEqIso_inv_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {σ₁ σ₂ : Substitution S T} (h : σ₁ = σ₂) (X : S.FreeMonoidal) :
    (toFunctorEqIso h).inv.app X =
      eqToHom (congrArg (fun σ : Substitution S T ↦ σ.toFunctor.obj X) h).symm := by
  subst h
  rfl

end Substitution

namespace Hom

/-- The strong monoidal functor `S.FreeMonoidal ⥤ T.FreeMonoidal` induced by a morphism of tensor
signatures `φ : Hom S T`. -/
abbrev toFunctor {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) : S.FreeMonoidal ⥤ T.FreeMonoidal :=
  φ.toSubstitution.toFunctor

theorem toFunctor_obj_of {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (a : S.Obj) :
    φ.toFunctor.obj (FreeMonoidal.of a) = FreeMonoidal.of (φ.obj a) :=
  (rfl)

theorem toFunctor_map_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    φ.toFunctor.map (FreeMonoidal.coupon g) =
      eqToHom (congrArg FreeMonoidal.mk (φ.src_coupon_projectObj_as g).symm) ≫
        FreeMonoidal.coupon (φ.coupon g) ≫
          eqToHom (congrArg FreeMonoidal.mk (φ.tgt_coupon_projectObj_as g)) := by
  rw [Substitution.toFunctor_map_coupon]
  dsimp only [toFunctor, toSubstitution, Substitution.toFunctor, FreeMonoidal.lift]
  simp

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
  have hmap : φ.toFunctor.map (FreeMonoidal.coupon a) =
      ψ.toFunctor.map (FreeMonoidal.coupon a) :=
    (Functor.congr_hom h (FreeMonoidal.coupon a)).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans
        ((Category.id_comp _).trans
          ((congrArg (_ ≫ ·) (eqToHom_refl _ _)).trans (Category.comp_id _))))
  have heq := (φ.toFunctor_map_coupon a).symm.trans (hmap.trans (ψ.toFunctor_map_coupon a))
  refine (FreeMonoidal.coupon_eq_iff hsrc htgt).mp ?_
  have hcancel := congrArg
    (fun k ↦ eqToHom (congrArg FreeMonoidal.mk (φ.src_coupon_projectObj_as a)) ≫ k ≫
      eqToHom (congrArg FreeMonoidal.mk (φ.tgt_coupon_projectObj_as a)).symm) heq
  simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id] using hcancel

@[simp]
theorem toFunctor_inj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {φ ψ : Hom S T} : φ.toFunctor = ψ.toFunctor ↔ φ = ψ :=
  toFunctor_injective.eq_iff

/-- The strong monoidal functor induced by the identity signature morphism `Hom.id S` is monoidally
naturally isomorphic to `𝟭 S.FreeMonoidal`. -/
def toFunctorIdIso (S : TensorSignature.{u, v}) : (Hom.id S).toFunctor ≅ 𝟭 S.FreeMonoidal :=
  Substitution.toFunctorEqIso (toSubstitution_id S) ≪≫ Substitution.toFunctorIdIso S

instance (S : TensorSignature.{u, v}) : NatTrans.IsMonoidal (toFunctorIdIso S).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (_ ≫ _))

@[simp]
theorem toFunctorIdIso_hom_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).hom.app X = eqToHom (FreeMonoidal.projectObj_of_self X) :=
  (congrArg (· ≫ (Substitution.toFunctorIdIso S).hom.app X)
    ((Substitution.toFunctorEqIso_hom_app (toSubstitution_id S) X).trans
      (eqToHom_refl _ _))).trans
    ((Category.id_comp _).trans (Substitution.toFunctorIdIso_hom_app S X))

@[simp]
theorem toFunctorIdIso_inv_app (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (toFunctorIdIso S).inv.app X = eqToHom (FreeMonoidal.projectObj_of_self X).symm :=
  (congrArg ((Substitution.toFunctorIdIso S).inv.app X ≫ ·)
    ((Substitution.toFunctorEqIso_inv_app (toSubstitution_id S) X).trans
      (eqToHom_refl _ _))).trans
    ((Category.comp_id _).trans (Substitution.toFunctorIdIso_inv_app S X))

/-- The strong monoidal functor induced by a composite signature morphism `φ.comp ψ` is monoidally
naturally isomorphic to `φ.toFunctor ⋙ ψ.toFunctor`. -/
def toFunctorCompIso {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) :
    (φ.comp ψ).toFunctor ≅ φ.toFunctor ⋙ ψ.toFunctor :=
  Substitution.toFunctorEqIso (toSubstitution_comp φ ψ) ≪≫
    Substitution.toFunctorCompIso φ.toSubstitution ψ.toSubstitution

instance {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) :
    NatTrans.IsMonoidal (toFunctorCompIso φ ψ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (_ ≫ _))

@[simp]
theorem toFunctorCompIso_hom_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) (X : S.FreeMonoidal) :
    (toFunctorCompIso φ ψ).hom.app X =
      eqToHom (FreeMonoidal.projectObj_projectObj_as
        (FreeMonoidal.of ∘ ψ.obj) (FreeMonoidal.of ∘ φ.obj) X.as).symm :=
  (congrArg (· ≫ (Substitution.toFunctorCompIso φ.toSubstitution ψ.toSubstitution).hom.app X)
    ((Substitution.toFunctorEqIso_hom_app (toSubstitution_comp φ ψ) X).trans
      (eqToHom_refl _ _))).trans
    ((Category.id_comp _).trans
      (Substitution.toFunctorCompIso_hom_app φ.toSubstitution ψ.toSubstitution X))

@[simp]
theorem toFunctorCompIso_inv_app {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) (X : S.FreeMonoidal) :
    (toFunctorCompIso φ ψ).inv.app X =
      eqToHom (FreeMonoidal.projectObj_projectObj_as
        (FreeMonoidal.of ∘ ψ.obj) (FreeMonoidal.of ∘ φ.obj) X.as) :=
  (congrArg ((Substitution.toFunctorCompIso φ.toSubstitution ψ.toSubstitution).inv.app X ≫ ·)
    ((Substitution.toFunctorEqIso_inv_app (toSubstitution_comp φ ψ) X).trans
      (eqToHom_refl _ _))).trans
    ((Category.comp_id _).trans
      (Substitution.toFunctorCompIso_inv_app φ.toSubstitution ψ.toSubstitution X))

end Hom

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

end TauCeti.TensorSignature
