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

Substitutions have an identity `Substitution.id` and associative composition `Substitution.comp`
across arbitrary signature universes, satisfying strict two-sided unit and associativity laws.
Signature morphisms `TensorSignature.Hom` embed faithfully into substitutions via
`Hom.toSubstitution` compatibly with identities and composition. On free monoidal categories,
identity and composite substitutions induce canonical monoidal natural isomorphisms
`Substitution.toFunctorIdIso` and `Substitution.toFunctorCompIso` satisfying the two-sided unit
and associativity coherence laws, and composing a substitution with a universal interpretation
`FreeMonoidal.lift` in an arbitrary (not necessarily strict) monoidal category is canonically
monoidally isomorphic to the pulled-back lift (`Substitution.toFunctorCompLiftIso`).
Pullback acts functorially on the interpretation groupoid (`Substitution.pullback`) naturally
with respect to extension (`Substitution.extensionPullbackIso`).

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
  categories, with unit and associativity coherence laws.
* `TauCeti.TensorSignature.Substitution.toFunctor`,
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
@[simp]
theorem Hom.subst_cast (σ : Substitution S T) {X X' Y Y' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (f : Hom X Y) :
    (f.cast hX hY).subst σ =
      (f.subst σ).cast (congrArg (fun W ↦ (projectObj σ.obj W).as) hX)
        (congrArg (fun W ↦ (projectObj σ.obj W).as) hY) := by
  subst hX hY
  simp

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
def id (S : TensorSignature.{u, v}) : Substitution S S where
  obj := FreeMonoidal.of
  coupon g := (FreeMonoidal.Hom.coupon g).cast
    (projectObj_of_as (S.src g)).symm (projectObj_of_as (S.tgt g)).symm

@[simp]
theorem id_obj (S : TensorSignature.{u, v}) (a : S.Obj) :
    (id S).obj a = FreeMonoidal.of a := by
  rfl

/-- Evaluating a formal tensor word along the identity substitution returns the same word. -/
@[simp]
theorem id_projectObj_as (S : TensorSignature.{u, v}) (X : FreeMonoidalCategory S.Obj) :
    (projectObj (id S).obj X).as = X :=
  projectObj_of_as X

@[simp]
theorem id_coupon (S : TensorSignature.{u, v}) (g : S.Coupon) :
    (id S).coupon g =
      (FreeMonoidal.Hom.coupon g).cast
        (id_projectObj_as S (S.src g)).symm (id_projectObj_as S (S.tgt g)).symm := by
  rfl

/-- Diagrammatic composition of substitutions across independent signature universes: first apply
`σ : Substitution S T`, then apply `τ : Substitution T U` to the resulting expressions. -/
def comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    Substitution S U where
  obj a := projectObj τ.obj (σ.obj a).as
  coupon g := ((σ.coupon g).subst τ).cast
    (congrArg FreeMonoidal.as (projectObj_projectObj_as τ.obj σ.obj (S.src g)))
    (congrArg FreeMonoidal.as (projectObj_projectObj_as τ.obj σ.obj (S.tgt g)))

@[simp]
theorem comp_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) (a : S.Obj) :
    (σ.comp τ).obj a = projectObj τ.obj (σ.obj a).as := by
  rfl

/-- Evaluating a formal tensor word along `σ` and then `τ` unwraps to the same tensor word as
evaluating along the composite substitution `σ.comp τ`. -/
theorem comp_projectObj_as {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    (W : FreeMonoidalCategory S.Obj) :
    (projectObj τ.obj (projectObj σ.obj W).as).as =
      (projectObj (σ.comp τ).obj W).as :=
  congrArg FreeMonoidal.as (projectObj_projectObj_as τ.obj σ.obj W)

@[simp]
theorem comp_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) (g : S.Coupon) :
    (σ.comp τ).coupon g = ((σ.coupon g).subst τ).cast
      (comp_projectObj_as σ τ (S.src g)) (comp_projectObj_as σ τ (S.tgt g)) := by
  rfl

end Substitution

namespace FreeMonoidal

/-- Substituting the identity substitution into any raw formal morphism returns that morphism,
transported along `Substitution.id_projectObj_as`. -/
@[simp 1100]
theorem Hom.id_subst {S : TensorSignature.{u, v}} {X Y : FreeMonoidalCategory S.Obj}
    (f : Hom X Y) :
    f.subst (Substitution.id S) =
      f.cast (Substitution.id_projectObj_as S X).symm
        (Substitution.id_projectObj_as S Y).symm := by
  induction f with
  | id X => exact (Hom.cast_id _ _).symm
  | α_hom X Y Z => exact (Hom.cast_α_hom _ _).symm
  | α_inv X Y Z => exact (Hom.cast_α_inv _ _).symm
  | l_hom X => exact (Hom.cast_l_hom _ _).symm
  | l_inv X => exact (Hom.cast_l_inv _ _).symm
  | ρ_hom X => exact (Hom.cast_ρ_hom _ _).symm
  | ρ_inv X => exact (Hom.cast_ρ_inv _ _).symm
  | coupon g => exact (Substitution.id_coupon S g).symm
  | comp f g ihf ihg =>
    rw [Hom.subst_comp, ihf, ihg]
    exact Hom.cast_comp_cast _ _ _ f g
  | whiskerLeft X f ih =>
    rw [Hom.subst_whiskerLeft, ih]
    exact Hom.whiskerLeft_cast _ _ f _ _
  | whiskerRight f X ih =>
    rw [Hom.subst_whiskerRight, ih]
    exact Hom.whiskerRight_cast _ _ f _ _
  | tensor f g ihf ihg =>
    rw [Hom.subst_tensor, ihf, ihg]
    exact Hom.cast_tensor_cast _ _ _ _ f g _ _

/-- Applying two raw substitutions successively agrees with applying their composite
`σ.comp τ`. -/
@[simp]
theorem Hom.subst_subst {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    (f.subst σ).subst τ =
      (f.subst (σ.comp τ)).cast (Substitution.comp_projectObj_as σ τ X).symm
        (Substitution.comp_projectObj_as σ τ Y).symm := by
  induction f with
  | id X => exact (Hom.cast_id _ _).symm
  | α_hom X Y Z => exact (Hom.cast_α_hom _ _).symm
  | α_inv X Y Z => exact (Hom.cast_α_inv _ _).symm
  | l_hom X => exact (Hom.cast_l_hom _ _).symm
  | l_inv X => exact (Hom.cast_l_inv _ _).symm
  | ρ_hom X => exact (Hom.cast_ρ_hom _ _).symm
  | ρ_inv X => exact (Hom.cast_ρ_inv _ _).symm
  | coupon g => simp [Substitution.comp_coupon]
  | comp f g ihf ihg =>
    rw [Hom.subst_comp, Hom.subst_comp, ihf, ihg]
    exact Hom.cast_comp_cast _ _ _ _ _
  | whiskerLeft X f ih =>
    refine (congrArg (Hom.subst τ) (Hom.subst_whiskerLeft σ X f)).trans
      ((Hom.subst_whiskerLeft τ (projectObj σ.obj X).as (f.subst σ)).trans ?_)
    rw [ih, Hom.subst_whiskerLeft]
    exact Hom.whiskerLeft_cast _ _ _ _ _
  | whiskerRight f X ih =>
    refine (congrArg (Hom.subst τ) (Hom.subst_whiskerRight σ f X)).trans
      ((Hom.subst_whiskerRight τ (f.subst σ) (projectObj σ.obj X).as).trans ?_)
    rw [ih, Hom.subst_whiskerRight]
    exact Hom.whiskerRight_cast _ _ _ _ _
  | tensor f g ihf ihg =>
    refine (congrArg (Hom.subst τ) (Hom.subst_tensor σ f g)).trans
      ((Hom.subst_tensor τ (f.subst σ) (g.subst σ)).trans ?_)
    rw [ihf, ihg, Hom.subst_tensor]
    exact Hom.cast_tensor_cast _ _ _ _ _ _ _ _

end FreeMonoidal

namespace Substitution

open FreeMonoidal

@[simp]
theorem id_comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) : (id S).comp σ = σ := by
  refine ext_cast (fun a ↦ by simp) fun g ↦ ?_
  rw [comp_coupon, id_coupon, Hom.subst_cast, Hom.subst_coupon, Hom.cast_cast, Hom.cast_cast]
  exact Hom.cast_rfl _

@[simp]
theorem comp_id {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (σ : Substitution S T) : σ.comp (id T) = σ := by
  refine ext_cast (fun a ↦ by simp [projectObj_congr (id_obj T)]) fun g ↦ ?_
  rw [comp_coupon, Hom.id_subst, Hom.cast_cast, Hom.cast_cast]
  exact Hom.cast_rfl _

theorem comp_assoc {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} {V : TensorSignature.{u₄, v₄}}
    (σ : Substitution S T) (τ : Substitution T U) (ρ : Substitution U V) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  refine ext_cast (fun a ↦ ?_) fun g ↦ ?_
  · rw [comp_obj, comp_obj, comp_obj, projectObj_projectObj_as]
    exact projectObj_congr (fun b ↦ (comp_obj τ ρ b).symm) (σ.obj a).as
  · rw [comp_coupon, comp_coupon, comp_coupon, Hom.subst_cast, Hom.subst_subst,
      Hom.cast_cast, Hom.cast_cast, Hom.cast_cast]

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
    ((φ.src_coupon g).trans (projectObj_as (FreeMonoidal.of ∘ φ.obj) (S.src g)).symm)
    ((φ.tgt_coupon g).trans (projectObj_as (FreeMonoidal.of ∘ φ.obj) (S.tgt g)).symm)

@[simp]
theorem toSubstitution_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (a : S.Obj) :
    φ.toSubstitution.obj a = FreeMonoidal.of (φ.obj a) := by
  rfl

/-- Boundary compatibility for embedding a signature morphism `φ : Hom S T` as a substitution. -/
theorem src_coupon_projectObj_as {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    T.src (φ.coupon g) = (projectObj φ.toSubstitution.obj (S.src g)).as :=
  (φ.src_coupon g).trans (projectObj_as (FreeMonoidal.of ∘ φ.obj) (S.src g)).symm

/-- Target compatibility for embedding a signature morphism `φ : Hom S T` as a substitution. -/
theorem tgt_coupon_projectObj_as {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    (φ : Hom S T) (g : S.Coupon) :
    T.tgt (φ.coupon g) = (projectObj φ.toSubstitution.obj (S.tgt g)).as :=
  (φ.tgt_coupon g).trans (projectObj_as (FreeMonoidal.of ∘ φ.obj) (S.tgt g)).symm

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
  refine Substitution.ext_cast (fun a ↦ by simp) fun g ↦ ?_
  rw [toSubstitution_coupon, Substitution.id_coupon, Hom.cast_cast]
  exact Hom.cast_coupon_congr (Hom.id_coupon S g) _ _ _ _

@[simp]
theorem toSubstitution_comp {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) :
    (φ.comp ψ).toSubstitution = φ.toSubstitution.comp ψ.toSubstitution := by
  have hobj : ∀ a, (φ.comp ψ).toSubstitution.obj a =
      (φ.toSubstitution.comp ψ.toSubstitution).obj a :=
    fun a ↦ by simp [Substitution.comp_obj]
  refine Substitution.ext_cast hobj fun g ↦ ?_
  rw [toSubstitution_coupon, Substitution.comp_coupon, toSubstitution_coupon,
    Hom.subst_cast, Hom.subst_coupon, toSubstitution_coupon, Hom.cast_cast, Hom.cast_cast,
    Hom.cast_cast]
  exact Hom.cast_coupon_congr (Hom.comp_coupon φ ψ g) _ _ _ _

/-- Precomposing a substitution `σ : Substitution T U` with a signature morphism `φ : Hom S T`
replaces each coupon `g` of `S` by `σ.coupon (φ.coupon g)` up to boundary transport. -/
theorem toSubstitution_comp_coupon {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (σ : Substitution T U) (g : S.Coupon) :
    (φ.toSubstitution.comp σ).coupon g = (σ.coupon (φ.coupon g)).cast
      ((congrArg (fun W ↦ (projectObj σ.obj W).as) (φ.src_coupon_projectObj_as g)).trans
        (Substitution.comp_projectObj_as φ.toSubstitution σ (S.src g)))
      ((congrArg (fun W ↦ (projectObj σ.obj W).as) (φ.tgt_coupon_projectObj_as g)).trans
        (Substitution.comp_projectObj_as φ.toSubstitution σ (S.tgt g))) := by
  rw [Substitution.comp_coupon, toSubstitution_coupon, Hom.subst_cast, Hom.subst_coupon,
    Hom.cast_cast]

end Hom

/-! ### Induced strong monoidal functors and monoidal natural isomorphisms -/

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

/-- The strong monoidal functor induced by `Substitution.id S` agrees on objects with the
identity functor. -/
theorem toFunctor_id_obj (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (Substitution.id S).toFunctor.obj X = X :=
  congrArg FreeMonoidal.mk (id_projectObj_as S X.as)

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
      rw [comp_eqToHom_iff, Category.assoc, toFunctor_map_coupon, id_coupon, homMk_cast,
        homMk_coupon, Functor.id_map]
      simp)

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
  congrArg FreeMonoidal.mk (comp_projectObj_as σ τ X.as).symm

/-- The strong monoidal functor induced by a composite substitution `σ.comp τ` is monoidally
naturally isomorphic to the composite functor `σ.toFunctor ⋙ τ.toFunctor`. -/
def toFunctorCompIso {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (σ : Substitution S T) (τ : Substitution T U) :
    (σ.comp τ).toFunctor ≅ σ.toFunctor ⋙ τ.toFunctor :=
  monoidalNatIsoOfEqObj (toFunctor_comp_obj σ τ)
    (by
      simp only [toFunctor_obj, tensorUnit_as, projectObj_tensorUnit, Functor.comp_obj, toFunctor_η,
        Functor.LaxMonoidal.comp_ε, toFunctor_ε, Functor.map_id, Category.comp_id]
      exact (eqToHom_refl _ _).symm)
    (fun _ _ ↦ by
      simp only [toFunctor_obj, tensorObj_as, projectObj_tensorObj, Functor.comp_obj, toFunctor_δ,
        Functor.LaxMonoidal.comp_μ, toFunctor_μ, Functor.map_id, Category.comp_id, Category.id_comp]
      exact TauCeti.eqToHom_tensorHom_eqToHom _ _)
    (fun g ↦ by
      have hl : (σ.comp τ).toFunctor.map (FreeMonoidal.coupon g) =
          eqToHom (toFunctor_comp_obj σ τ ⟨S.src g⟩) ≫
            FreeMonoidal.homMk ((σ.coupon g).subst τ) ≫
            eqToHom (toFunctor_comp_obj σ τ ⟨S.tgt g⟩).symm :=
        (toFunctor_map_coupon (σ.comp τ) g).trans
          ((congrArg FreeMonoidal.homMk (comp_coupon σ τ g)).trans (homMk_cast _ _ _))
      have hr : (σ.toFunctor ⋙ τ.toFunctor).map (FreeMonoidal.coupon g) =
          FreeMonoidal.homMk ((σ.coupon g).subst τ) := by
        rw [Functor.comp_map, toFunctor_map_coupon]
        exact toFunctor_map_homMk τ (σ.coupon g)
      have heq : (eqToHom (toFunctor_comp_obj σ τ ⟨S.src g⟩) ≫
            FreeMonoidal.homMk ((σ.coupon g).subst τ) ≫
            eqToHom (toFunctor_comp_obj σ τ ⟨S.tgt g⟩).symm) ≫
          eqToHom (toFunctor_comp_obj σ τ ⟨S.tgt g⟩) =
          eqToHom (toFunctor_comp_obj σ τ ⟨S.src g⟩) ≫
            FreeMonoidal.homMk ((σ.coupon g).subst τ) :=
        (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          ((Category.assoc _ _ _).trans
            ((congrArg (_ ≫ ·) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans
              (Category.comp_id _))))
      exact (congrArg (· ≫ _) hl).trans (heq.trans (congrArg (_ ≫ ·) hr.symm)))

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
    projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) X =
      eqToIso (σ.projectObj_pullbackObj I.obj X) ≪≫
        projectObjIso α.iso (projectObj σ.obj X).as ≪≫
        eqToIso (σ.projectObj_pullbackObj J.obj X).symm := by
  induction X with
  | of a =>
    ext
    have hL : (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) (.of a)).hom =
        (projectObjIso α.iso (σ.obj a).as).hom :=
      congrArg Iso.hom (projectObjIso_of _ a)
    have hR : (eqToIso (σ.projectObj_pullbackObj I.obj (.of a)) ≪≫
          projectObjIso α.iso (projectObj σ.obj (.of a)).as ≪≫
          eqToIso (σ.projectObj_pullbackObj J.obj (.of a)).symm).hom =
        (projectObjIso α.iso (σ.obj a).as).hom := by
      rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
      exact (congrArg (· ≫ _) (eqToHom_refl (projectObj I.obj (σ.obj a).as) _)).trans
        ((Category.id_comp _).trans
          ((congrArg (_ ≫ ·) (eqToHom_refl (projectObj J.obj (σ.obj a).as) _)).trans
            (Category.comp_id _)))
    exact hL.trans hR.symm
  | unit =>
    ext
    have hL : (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) .unit).hom = 𝟙 (𝟙_ D) :=
      congrArg Iso.hom (projectObjIso_tensorUnit _)
    have hR : (eqToIso (σ.projectObj_pullbackObj I.obj .unit) ≪≫
          projectObjIso α.iso (projectObj σ.obj .unit).as ≪≫
          eqToIso (σ.projectObj_pullbackObj J.obj .unit).symm).hom = 𝟙 (𝟙_ D) := by
      rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
      have h1 : eqToHom (σ.projectObj_pullbackObj I.obj .unit) = 𝟙 (𝟙_ D) :=
        eqToHom_refl (𝟙_ D) rfl
      have hr : (projectObjIso α.iso (projectObj σ.obj .unit).as).hom = 𝟙 (𝟙_ D) :=
        congrArg Iso.hom (projectObjIso_tensorUnit α.iso)
      have h2 : eqToHom (σ.projectObj_pullbackObj J.obj .unit).symm = 𝟙 (𝟙_ D) :=
        eqToHom_refl (𝟙_ D) rfl
      exact (congrArg₂ (· ≫ ·) h1 (congrArg₂ (· ≫ ·) hr h2)).trans
        ((congrArg (𝟙 (𝟙_ D) ≫ ·) (Category.id_comp _)).trans (Category.id_comp _))
    exact hL.trans hR.symm
  | tensor X Y ihX ihY =>
    ext
    have hX := congrArg Iso.hom ihX
    have hY := congrArg Iso.hom ihY
    rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom] at hX hY
    have hL : (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) (X.tensor Y)).hom =
        (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) X).hom ⊗ₘ
          (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) Y).hom :=
      congrArg Iso.hom (projectObjIso_tensor _ X Y)
    have hR : (projectObjIso α.iso (projectObj σ.obj (X.tensor Y)).as).hom =
        (projectObjIso α.iso (projectObj σ.obj X).as).hom ⊗ₘ
          (projectObjIso α.iso (projectObj σ.obj Y).as).hom :=
      congrArg Iso.hom (projectObjIso_tensor α.iso (projectObj σ.obj X).as (projectObj σ.obj Y).as)
    have hsplit : (eqToHom (σ.projectObj_pullbackObj I.obj X) ≫
          (projectObjIso α.iso (projectObj σ.obj X).as).hom ≫
          eqToHom (σ.projectObj_pullbackObj J.obj X).symm) ⊗ₘ
        (eqToHom (σ.projectObj_pullbackObj I.obj Y) ≫
          (projectObjIso α.iso (projectObj σ.obj Y).as).hom ≫
          eqToHom (σ.projectObj_pullbackObj J.obj Y).symm) =
        (eqToHom (σ.projectObj_pullbackObj I.obj X) ⊗ₘ
          eqToHom (σ.projectObj_pullbackObj I.obj Y)) ≫
        ((projectObjIso α.iso (projectObj σ.obj X).as).hom ⊗ₘ
          (projectObjIso α.iso (projectObj σ.obj Y).as).hom) ≫
        (eqToHom (σ.projectObj_pullbackObj J.obj X).symm ⊗ₘ
          eqToHom (σ.projectObj_pullbackObj J.obj Y).symm) := by
      simp only [MonoidalCategory.tensorHom_comp_tensorHom]
    have hmerge : (eqToHom (σ.projectObj_pullbackObj I.obj X) ⊗ₘ
          eqToHom (σ.projectObj_pullbackObj I.obj Y)) ≫
        ((projectObjIso α.iso (projectObj σ.obj X).as).hom ⊗ₘ
          (projectObjIso α.iso (projectObj σ.obj Y).as).hom) ≫
        (eqToHom (σ.projectObj_pullbackObj J.obj X).symm ⊗ₘ
          eqToHom (σ.projectObj_pullbackObj J.obj Y).symm) =
        (eqToIso (σ.projectObj_pullbackObj I.obj (X.tensor Y)) ≪≫
          projectObjIso α.iso (projectObj σ.obj (X.tensor Y)).as ≪≫
          eqToIso (σ.projectObj_pullbackObj J.obj (X.tensor Y)).symm).hom := by
      rw [TauCeti.eqToHom_tensorHom_eqToHom, TauCeti.eqToHom_tensorHom_eqToHom,
        Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom, hR]
      rfl
    exact (hL.trans (congrArg₂ (· ⊗ₘ ·) hX hY)).trans (hsplit.trans hmerge)

private theorem projectObjIso_eqToIso {A : Type*} {f g : A → D} (h : ∀ a, f a = g a)
    (X : FreeMonoidalCategory A) :
    projectObjIso (fun a ↦ eqToIso (h a)) X = eqToIso (projectObj_congr h X) := by
  induction X with
  | of a =>
    ext
    rw [projectObjIso_of, eqToIso.hom, eqToIso.hom]
    dsimp only [projectObj]
  | unit =>
    ext
    have hL : (projectObjIso (fun a ↦ eqToIso (h a)) .unit).hom = 𝟙 (𝟙_ D) :=
      congrArg Iso.hom (projectObjIso_tensorUnit _)
    have hR : eqToHom (projectObj_congr h .unit) = 𝟙 (𝟙_ D) := eqToHom_refl (𝟙_ D) rfl
    exact hL.trans hR.symm
  | tensor X Y ihX ihY =>
    ext
    have hX := congrArg Iso.hom ihX
    have hY := congrArg Iso.hom ihY
    rw [eqToIso.hom] at hX hY
    rw [show X.tensor Y = X ⊗ Y from rfl, projectObjIso_tensor, MonoidalCategory.tensorIso_hom,
      hX, hY, eqToIso.hom]
    exact eqToHom_tensorHom_eqToHom _ _

variable (D) in
/-- Pull back interpretations of `T` in `D` and their isomorphisms along a substitution
`σ : Substitution S T`. -/
@[expose] def pullback (σ : Substitution S T) : Interpretation T D ⥤ Interpretation S D where
  obj I := ⟨σ.pullbackObj I.obj, σ.pullbackCoupon I.obj I.coupon⟩
  map {I J} α :=
    { iso a := projectObjIso α.iso (σ.obj a).as
      comm g := by
        -- Expose `projectObj` so `eqToHom` rewrites avoid implicit transparency mismatch.
        change σ.pullbackCoupon I.obj I.coupon g ≫
            (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) (S.tgt g)).hom =
          (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) (S.src g)).hom ≫
            σ.pullbackCoupon J.obj J.coupon g
        have hnat := ((Interpretation.extension T D).map α).iso.hom.hom.hom.naturality
          (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
            (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g))
        simp only [Interpretation.extension_map_iso_hom_hom_hom_app] at hnat
        have hsrc : (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) (S.src g)).hom =
            eqToHom (σ.projectObj_pullbackObj I.obj (S.src g)) ≫
              (projectObjIso α.iso (projectObj σ.obj (S.src g)).as).hom ≫
              eqToHom (σ.projectObj_pullbackObj J.obj (S.src g)).symm := by
          rw [projectObjIso_pullbackObj, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
        have htgt : (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) (S.tgt g)).hom =
            eqToHom (σ.projectObj_pullbackObj I.obj (S.tgt g)) ≫
              (projectObjIso α.iso (projectObj σ.obj (S.tgt g)).as).hom ≫
              eqToHom (σ.projectObj_pullbackObj J.obj (S.tgt g)).symm := by
          rw [projectObjIso_pullbackObj, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
        rw [hsrc, htgt]
        have hcancelL : ∀ {A₁ A₂ B₁ B₂ C₁ C₂ : D}
            (p₁ : A₁ = A₂) (p₂ : B₁ = B₂) (p₃ : B₂ = B₁) (p₄ : C₁ = C₂)
            (f : A₂ ⟶ B₁) (k : B₁ ⟶ C₁),
            (eqToHom p₁ ≫ f ≫ eqToHom p₂) ≫ eqToHom p₃ ≫ k ≫ eqToHom p₄ =
              eqToHom p₁ ≫ (f ≫ k) ≫ eqToHom p₄ := by
          intro _ _ _ _ _ _ p₁ p₂ p₃ p₄ f k; subst p₁ p₂ p₄; simp
        have hcancelR : ∀ {A₁ A₂ B₁ B₂ C₁ C₂ : D}
            (p₁ : A₁ = A₂) (p₂ : B₁ = B₂) (p₃ : B₂ = B₁) (p₄ : C₁ = C₂)
            (k : A₂ ⟶ B₁) (f : B₁ ⟶ C₁),
            (eqToHom p₁ ≫ k ≫ eqToHom p₂) ≫ eqToHom p₃ ≫ f ≫ eqToHom p₄ =
              eqToHom p₁ ≫ (k ≫ f) ≫ eqToHom p₄ := by
          intro _ _ _ _ _ _ p₁ p₂ p₃ p₄ k f; subst p₁ p₂ p₄; simp
        refine ((congrArg (· ≫ _) (σ.pullbackCoupon_def I.obj I.coupon g)).trans
          (hcancelL _ _ _ _ _ _)).trans ?_
        refine (congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _) hnat).trans ?_
        exact ((congrArg (_ ≫ ·) (σ.pullbackCoupon_def J.obj J.coupon g)).trans
          (hcancelR _ _ _ _ _ _)).symm }
  map_id I := Interpretation.hom_ext fun a ↦ by
    dsimp
    rw [show Interpretation.Hom.iso (𝟙 I) = fun b ↦ Iso.refl (I.obj b) from
        funext (Interpretation.id_iso I), projectObjIso_refl, Iso.refl_hom]
    rfl
  map_comp α β := Interpretation.hom_ext fun a ↦ by
    dsimp
    rw [show Interpretation.Hom.iso (α ≫ β) = fun b ↦ α.iso b ≪≫ β.iso b from
        funext (Interpretation.comp_iso α β), projectObjIso_trans, Iso.trans_hom]
    rfl

@[simp]
theorem pullback_obj_obj (σ : Substitution S T) (I : Interpretation T D) :
    ((σ.pullback D).obj I).obj = σ.pullbackObj I.obj :=
  rfl

@[simp]
theorem pullback_obj_coupon (σ : Substitution S T) (I : Interpretation T D) :
    ((σ.pullback D).obj I).coupon = σ.pullbackCoupon I.obj I.coupon :=
  rfl

@[simp]
theorem pullback_map_iso (σ : Substitution S T) {I J : Interpretation T D} (α : I ⟶ J)
    (a : S.Obj) :
    ((σ.pullback D).map α).iso a = projectObjIso α.iso (σ.obj a).as :=
  rfl

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
  -- Align `Interpretation.extension` object projections with `FreeMonoidal.lift` transparency.
  change ((Interpretation.extension T D).map α).iso.hom.hom.hom.app (σ.toFunctor.obj X) ≫
      (σ.toFunctorCompLiftIso J.obj J.coupon).hom.app X =
    (σ.toFunctorCompLiftIso I.obj I.coupon).hom.app X ≫
      ((Interpretation.extension S D).map ((σ.pullback D).map α)).iso.hom.hom.hom.app X
  have h1 := Interpretation.extension_map_iso_hom_hom_hom_app α (σ.toFunctor.obj X)
  have h2 := σ.toFunctorCompLiftIso_hom_app J.obj J.coupon X
  have h3 := σ.toFunctorCompLiftIso_hom_app I.obj I.coupon X
  have h4 := Interpretation.extension_map_iso_hom_hom_hom_app ((σ.pullback D).map α) X
  have hiso : (projectObjIso ((σ.pullback D).map α).iso X.as).hom =
      eqToHom (σ.projectObj_pullbackObj I.obj X.as) ≫
        (projectObjIso α.iso (projectObj σ.obj X.as).as).hom ≫
        eqToHom (σ.projectObj_pullbackObj J.obj X.as).symm := by
    -- Expose `fun a ↦ projectObjIso α.iso (σ.obj a).as` at `projectObj` transparency.
    change (projectObjIso (fun a ↦ projectObjIso α.iso (σ.obj a).as) X.as).hom = _
    rw [projectObjIso_pullbackObj, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
  have hcancel : ∀ {A₁ A₂ B₁ B₂ : D} (p : A₁ = A₂) (q : B₁ = B₂) (f : A₂ ⟶ B₂),
      f ≫ eqToHom q.symm = eqToHom p.symm ≫ eqToHom p ≫ f ≫ eqToHom q.symm := by
    intro _ _ _ _ p q f; subst p; simp
  refine (congrArg₂ (· ≫ ·) h1 h2).trans ?_
  refine (hcancel (σ.projectObj_pullbackObj I.obj X.as)
    (σ.projectObj_pullbackObj J.obj X.as)
    (projectObjIso α.iso (σ.toFunctor.obj X).as).hom).trans ?_
  exact congrArg₂ (· ≫ ·) h3.symm (h4.trans hiso).symm

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
    ((σ.precomp D).obj F).of = MonoidalFunctor.of (σ.toFunctor ⋙ F.of.toFunctor) :=
  rfl

@[simp]
theorem precomp_map_iso_hom_hom_hom (σ : Substitution S T)
    {F G : Core (MonoidalFunctor T.FreeMonoidal D)} (α : F ⟶ G) :
    ((σ.precomp D).map α).iso.hom.hom.hom =
      Functor.whiskerLeft σ.toFunctor α.iso.hom.hom.hom :=
  rfl

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
      -- Unfold `Core`/`MonoidalFunctor` composition to match `toFunctorCompLiftIso_natural`.
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
  rw [extensionPullbackIso]
  simp only [NatIso.ofComponents_hom_app]
  rfl

/-- Pulling back a generator-object assignment along `Substitution.id S` returns the same
assignment. -/
theorem pullback_id_obj (fo : S.Obj → D) : (id S).pullbackObj fo = fo :=
  funext fun a ↦ by simp [pullbackObj]

variable (D) in
/-- Pulling back interpretations along `Substitution.id S` is naturally isomorphic to the identity
functor on `Interpretation S D`. -/
def pullbackIdIso : (id S).pullback D ≅ 𝟭 (Interpretation S D) :=
  NatIso.ofComponents
    (fun I ↦ (Groupoid.isoEquivHom _ _).symm
      { iso a := eqToIso (congrFun (pullback_id_obj I.obj) a)
        comm g := by
          -- Expose `projectObj` so `eqToHom` rewrites avoid implicit transparency mismatch.
          change (id S).pullbackCoupon I.obj I.coupon g ≫
              (projectObjIso (fun a ↦ eqToIso (congrFun (pullback_id_obj I.obj) a))
                (S.tgt g)).hom =
            (projectObjIso (fun a ↦ eqToIso (congrFun (pullback_id_obj I.obj) a))
                (S.src g)).hom ≫ I.coupon g
          rw [projectObjIso_eqToIso, projectObjIso_eqToIso, eqToIso.hom, eqToIso.hom]
          have hmid : (FreeMonoidal.lift I.obj I.coupon).map
              (FreeMonoidal.homMk (X := projectObj (id S).obj (S.src g))
                (Y := projectObj (id S).obj (S.tgt g)) ((id S).coupon g)) =
              eqToHom (congrArg (FreeMonoidal.lift I.obj I.coupon).obj
                  (congrArg FreeMonoidal.mk (id_projectObj_as S (S.src g)))) ≫
                I.coupon g ≫
                eqToHom (congrArg (FreeMonoidal.lift I.obj I.coupon).obj
                  (congrArg FreeMonoidal.mk (id_projectObj_as S (S.tgt g)).symm)) := by
            refine (congrArg (FreeMonoidal.lift I.obj I.coupon).map
              ((congrArg FreeMonoidal.homMk (id_coupon S g)).trans
                (FreeMonoidal.homMk_cast _ _ _))).trans ?_
            rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
            exact congrArg (_ ≫ ·) (congrArg (· ≫ _) (lift_map_coupon _ _ g))
          have hmerge : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ : D}
              (p₁ : A₁ = A₂) (p₂ : A₂ = A₃) (p₃ : A₁ = A₃)
              (q₁ : B₃ = B₂) (q₂ : B₂ = B₁) (q₃ : B₁ = B₃) (f : A₃ ⟶ B₃),
              (eqToHom p₁ ≫ (eqToHom p₂ ≫ f ≫ eqToHom q₁) ≫ eqToHom q₂) ≫ eqToHom q₃ =
                eqToHom p₃ ≫ f := by
            intro _ _ _ _ _ _ p₁ p₂ p₃ q₁ q₂ q₃ f; subst p₁ p₂ q₁ q₂; simp
          refine (congrArg (· ≫ _) ((pullbackCoupon_def _ _ _ g).trans
            (congrArg (fun k ↦ _ ≫ k ≫ _) hmid))).trans ?_
          exact hmerge _ _ _ _ _ _ _ })
    (fun {I J} α ↦ Interpretation.hom_ext fun a ↦ by
      -- Expose `projectObj` and unfold `eqToIso.hom` to avoid implicit transparency mismatch.
      change (projectObjIso α.iso ((id S).obj a).as).hom ≫
          eqToHom (congrFun (pullback_id_obj J.obj) a) =
        eqToHom (congrFun (pullback_id_obj I.obj) a) ≫ (α.iso a).hom
      have hof : ∀ {X₁ X₂ : Interpretation S D} (β : X₁ ⟶ X₂) (w : FreeMonoidalCategory S.Obj)
          (hw : w = .of a),
          (projectObjIso β.iso w).hom =
            eqToHom (congrArg (projectObj X₁.obj) hw) ≫ (β.iso a).hom ≫
              eqToHom (congrArg (projectObj X₂.obj) hw).symm := by
        intro X₁ X₂ β w hw; subst hw
        have h1 : eqToHom (congrArg (projectObj X₁.obj) (rfl : .of a = .of a)) =
            𝟙 (X₁.obj a) :=
          eqToHom_refl _ rfl
        have h2 : eqToHom (congrArg (projectObj X₂.obj) (rfl : .of a = .of a)).symm =
            𝟙 (X₂.obj a) :=
          eqToHom_refl _ rfl
        exact (congrArg Iso.hom (projectObjIso_of β.iso a)).trans
          ((Category.id_comp _).symm.trans (congrArg₂ (· ≫ ·) h1.symm
            ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) h2.symm))))
      have hconj : ∀ {A₁ A₂ B₁ B₂ : D} (p p' : A₁ = A₂) (q : B₂ = B₁) (q' : B₁ = B₂) (f : A₂ ⟶ B₂),
          (eqToHom p ≫ f ≫ eqToHom q) ≫ eqToHom q' = eqToHom p' ≫ f := by
        intro _ _ _ _ p p' q q' f; subst p q; simp
      rw [hof α ((id S).obj a).as (congrArg FreeMonoidal.as (id_obj S a))]
      exact hconj _ _ _ _ _)

@[simp]
theorem pullbackIdIso_hom_app_iso (I : Interpretation S D) (a : S.Obj) :
    ((pullbackIdIso D).hom.app I).iso a = eqToIso (congrFun (pullback_id_obj I.obj) a) := by
  rw [pullbackIdIso]
  simp only [NatIso.ofComponents_hom_app]
  rfl

/-- Pulling back a generator-object assignment along `σ.comp τ` agrees with pulling back along `τ`
and then along `σ`. -/
theorem comp_pullbackObj {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (fo : U.Obj → D) :
    (σ.comp τ).pullbackObj fo = σ.pullbackObj (τ.pullbackObj fo) :=
  funext fun a ↦ by
    rw [pullbackObj_apply, comp_obj, pullbackObj_apply, projectObj_projectObj_as]
    exact projectObj_congr (fun b ↦ (pullbackObj_apply τ fo b).symm) (σ.obj a).as

variable (D) in
/-- Pulling back interpretations along `σ.comp τ` is naturally isomorphic to pulling back along `τ`
and then along `σ`. -/
def pullbackCompIso {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) :
    (σ.comp τ).pullback D ≅ τ.pullback D ⋙ σ.pullback D :=
  NatIso.ofComponents
    (fun I ↦ (Groupoid.isoEquivHom _ _).symm
      { iso a := eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a)
        comm g := by
          -- Expose `projectObj` so `eqToHom` rewrites avoid implicit transparency mismatch.
          change (σ.comp τ).pullbackCoupon I.obj I.coupon g ≫
              (projectObjIso (fun a ↦ eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a))
                (S.tgt g)).hom =
            (projectObjIso (fun a ↦ eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a))
                (S.src g)).hom ≫
              σ.pullbackCoupon (τ.pullbackObj I.obj) (τ.pullbackCoupon I.obj I.coupon) g
          have hnat := (τ.toFunctorCompLiftIso I.obj I.coupon).hom.naturality
            (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
              (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g))
          simp only [Functor.comp_map, toFunctor_map_homMk, toFunctorCompLiftIso_hom_app] at hnat
          rw [projectObjIso_eqToIso, projectObjIso_eqToIso, eqToIso.hom, eqToIso.hom]
          have hmap : (FreeMonoidal.lift I.obj I.coupon).map
              (FreeMonoidal.homMk (X := projectObj τ.obj (projectObj σ.obj (S.src g)).as)
                (Y := projectObj τ.obj (projectObj σ.obj (S.tgt g)).as)
                ((σ.coupon g).subst τ)) =
              eqToHom (τ.projectObj_pullbackObj I.obj (projectObj σ.obj (S.src g)).as).symm ≫
                (FreeMonoidal.lift (τ.pullbackObj I.obj) (τ.pullbackCoupon I.obj I.coupon)).map
                  (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
                    (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g)) ≫
                eqToHom (τ.projectObj_pullbackObj I.obj (projectObj σ.obj (S.tgt g)).as) :=
            ((comp_eqToHom_iff _ _ _).mp hnat).trans (Category.assoc _ _ _)
          have hmerge : ∀ {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : D}
              (p₁ : A₁ = A₂) (p₂ : A₂ = A₃) (p₃ : A₃ = A₄) (p₄ : A₁ = A₅) (p₅ : A₅ = A₄)
              (q₁ : B₄ = B₃) (q₂ : B₃ = B₂) (q₃ : B₂ = B₁) (q₄ : B₁ = B₅) (q₅ : B₄ = B₅)
              (f : A₄ ⟶ B₄),
              (eqToHom p₁ ≫ (eqToHom p₂ ≫ (eqToHom p₃ ≫ f ≫ eqToHom q₁) ≫ eqToHom q₂) ≫
                  eqToHom q₃) ≫ eqToHom q₄ =
                eqToHom p₄ ≫ eqToHom p₅ ≫ f ≫ eqToHom q₅ := by
            intro _ _ _ _ _ _ _ _ _ _ p₁ p₂ p₃ p₄ p₅ q₁ q₂ q₃ q₄ q₅ f
            subst p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄; simp
          have hmid : (FreeMonoidal.lift I.obj I.coupon).map
              (FreeMonoidal.homMk (X := projectObj (σ.comp τ).obj (S.src g))
                (Y := projectObj (σ.comp τ).obj (S.tgt g)) ((σ.comp τ).coupon g)) =
              eqToHom (congrArg (FreeMonoidal.lift I.obj I.coupon).obj
                  (congrArg FreeMonoidal.mk (comp_projectObj_as σ τ (S.src g)).symm)) ≫
                (eqToHom (τ.projectObj_pullbackObj I.obj (projectObj σ.obj (S.src g)).as).symm ≫
                  (FreeMonoidal.lift (τ.pullbackObj I.obj)
                    (τ.pullbackCoupon I.obj I.coupon)).map
                    (FreeMonoidal.homMk (X := projectObj σ.obj (S.src g))
                      (Y := projectObj σ.obj (S.tgt g)) (σ.coupon g)) ≫
                  eqToHom (τ.projectObj_pullbackObj I.obj (projectObj σ.obj (S.tgt g)).as)) ≫
                eqToHom (congrArg (FreeMonoidal.lift I.obj I.coupon).obj
                  (congrArg FreeMonoidal.mk (comp_projectObj_as σ τ (S.tgt g)))) := by
            rw [comp_coupon, FreeMonoidal.homMk_cast, Functor.map_comp, Functor.map_comp,
              eqToHom_map, eqToHom_map]
            exact congrArg (_ ≫ ·) (congrArg (· ≫ _) hmap)
          refine (congrArg (· ≫ _) ((pullbackCoupon_def _ _ _ g).trans
            (congrArg (fun k ↦ _ ≫ k ≫ _) hmid))).trans ?_
          refine Eq.trans ?_ (congrArg (eqToHom _ ≫ ·)
            (σ.pullbackCoupon_def (τ.pullbackObj I.obj) (τ.pullbackCoupon I.obj I.coupon) g).symm)
          exact hmerge _ _ _ _ _ _ _ _ _ _ _ })
    (fun {I J} α ↦ Interpretation.hom_ext fun a ↦ by
      -- Expose `projectObj` and unfold `eqToIso.hom` to avoid implicit transparency mismatch.
      change (projectObjIso α.iso ((σ.comp τ).obj a).as).hom ≫
          eqToHom (congrFun (comp_pullbackObj σ τ J.obj) a) =
        eqToHom (congrFun (comp_pullbackObj σ τ I.obj) a) ≫
          (projectObjIso ((τ.pullback D).map α).iso (σ.obj a).as).hom
      have hcomp : ∀ {X₁ X₂ : Interpretation U D} (β : X₁ ⟶ X₂)
          (w : FreeMonoidalCategory U.Obj) (hw : w = (projectObj τ.obj (σ.obj a).as).as),
          (projectObjIso β.iso w).hom =
            eqToHom (congrArg (projectObj X₁.obj) hw) ≫
              (projectObjIso β.iso (projectObj τ.obj (σ.obj a).as).as).hom ≫
              eqToHom (congrArg (projectObj X₂.obj) hw).symm := by
        intro X₁ X₂ β w hw; subst hw; simp
      have hpull : (projectObjIso (fun b ↦ projectObjIso α.iso (τ.obj b).as) (σ.obj a).as).hom =
          eqToHom (τ.projectObj_pullbackObj I.obj (σ.obj a).as) ≫
            (projectObjIso α.iso (projectObj τ.obj (σ.obj a).as).as).hom ≫
            eqToHom (τ.projectObj_pullbackObj J.obj (σ.obj a).as).symm := by
        rw [projectObjIso_pullbackObj, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom]
      have hjoin : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ : D}
          (p : A₁ = A₂) (p' : A₁ = A₃) (p'' : A₃ = A₂)
          (q : B₂ = B₁) (q' : B₁ = B₃) (q₁ : B₂ = B₃) (f : A₂ ⟶ B₂),
          (eqToHom p ≫ f ≫ eqToHom q) ≫ eqToHom q' =
            eqToHom p' ≫ eqToHom p'' ≫ f ≫ eqToHom q₁ := by
        intro _ _ _ _ _ _ p p' p'' q q' q₁ f; subst p p'' q; simp
      rw [hcomp α ((σ.comp τ).obj a).as (congrArg FreeMonoidal.as (comp_obj σ τ a)),
        show (projectObjIso ((τ.pullback D).map α).iso (σ.obj a).as).hom =
          (projectObjIso (fun b ↦ projectObjIso α.iso (τ.obj b).as) (σ.obj a).as).hom from rfl,
        hpull]
      exact hjoin _ _ _ _ _ _ _)

@[simp]
theorem pullbackCompIso_hom_app_iso {U : TensorSignature.{u₄, v₄}} (σ : Substitution S T)
    (τ : Substitution T U) (I : Interpretation U D) (a : S.Obj) :
    ((pullbackCompIso D σ τ).hom.app I).iso a =
      eqToIso (congrFun (comp_pullbackObj σ τ I.obj) a) := by
  rw [pullbackCompIso]
  simp only [NatIso.ofComponents_hom_app]
  rfl

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
  have htriple : ∀ {A₁ A₂ A₃ A₄ : D} (p₁ : A₁ = A₂) (p₂ : A₂ = A₃) (p₃ : A₃ = A₄),
      eqToHom p₁ ≫ eqToHom p₂ ≫ eqToHom p₃ = eqToHom (p₁.trans (p₂.trans p₃)) := by
    intro _ _ _ _ p₁ p₂ p₃; subst p₁ p₂ p₃; simp
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
    exact htriple _ _ _
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
  have hcongr := Functor.congr_hom h (FreeMonoidal.coupon a)
  refine (FreeMonoidal.coupon_eq_iff hsrc htgt).mp ?_
  have hconj : ∀ {X X' Y Y' : T.FreeMonoidal} (p : X = X') (q : Y = Y') (f : X ⟶ Y),
      eqToHom p ≫ (eqToHom p.symm ≫ f ≫ eqToHom q) ≫ eqToHom q.symm = f := by
    intro _ _ _ _ p q f; subst p q; simp
  have htriple : ∀ {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : T.FreeMonoidal}
      (p₁ : X₁ = X₂) (p₂ : X₂ = X₃) (p₃ : X₃ = X₄)
      (q₁ : Y₄ = Y₃) (q₂ : Y₃ = Y₂) (q₃ : Y₂ = Y₁) (f : X₄ ⟶ Y₄),
      eqToHom p₁ ≫ (eqToHom p₂ ≫ (eqToHom p₃ ≫ f ≫ eqToHom q₁) ≫ eqToHom q₂) ≫ eqToHom q₃ =
        eqToHom (p₁.trans (p₂.trans p₃)) ≫ f ≫ eqToHom (q₁.trans (q₂.trans q₃)) := by
    intro _ _ _ _ _ _ _ _ p₁ p₂ p₃ q₁ q₂ q₃ f; subst p₁ p₂ p₃ q₁ q₂ q₃; simp
  have hl : eqToHom (congrArg FreeMonoidal.mk (φ.src_coupon_projectObj_as a)) ≫
      φ.toFunctor.map (FreeMonoidal.coupon a) ≫
      eqToHom (congrArg FreeMonoidal.mk (φ.tgt_coupon_projectObj_as a)).symm =
      FreeMonoidal.coupon (c₁ a) :=
    (congrArg (fun k ↦ _ ≫ k ≫ _) (φ.toFunctor_map_coupon a)).trans (hconj _ _ _)
  have hr : eqToHom (congrArg FreeMonoidal.mk (φ.src_coupon_projectObj_as a)) ≫
      (eqToHom (congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj ⟨S.src a⟩) h) ≫
        ψ.toFunctor.map (FreeMonoidal.coupon a) ≫
        eqToHom (congrArg (fun F : S.FreeMonoidal ⥤ T.FreeMonoidal ↦ F.obj ⟨S.tgt a⟩) h).symm) ≫
      eqToHom (congrArg FreeMonoidal.mk (φ.tgt_coupon_projectObj_as a)).symm =
      eqToHom (congrArg FreeMonoidal.mk hsrc) ≫ FreeMonoidal.coupon (c₂ a) ≫
        eqToHom (congrArg FreeMonoidal.mk htgt).symm :=
    (congrArg (fun k ↦ _ ≫ (_ ≫ k ≫ _) ≫ _) (ψ.toFunctor_map_coupon a)).trans
      (htriple _ _ _ _ _ _ _)
  exact hl.symm.trans ((congrArg (fun k ↦ _ ≫ k ≫ _) hcongr).trans hr)

@[simp]
theorem toFunctor_inj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {φ ψ : Hom S T} : φ.toFunctor = ψ.toFunctor ↔ φ = ψ :=
  toFunctor_injective.eq_iff

/-- The strong monoidal functor induced by `Hom.id S` agrees on objects with the identity
functor. -/
theorem toFunctor_id_obj (S : TensorSignature.{u, v}) (X : S.FreeMonoidal) :
    (Hom.id S).toFunctor.obj X = X := by
  rw [toFunctor, toSubstitution_id]
  exact FreeMonoidal.projectObj_of_self X

/-- The strong monoidal functor induced by `φ.comp ψ` agrees on objects with the composite functor
`φ.toFunctor ⋙ ψ.toFunctor`. -/
theorem toFunctor_comp_obj {S : TensorSignature.{u₁, v₁}} {T : TensorSignature.{u₂, v₂}}
    {U : TensorSignature.{u₃, v₃}} (φ : Hom S T) (ψ : Hom T U) (X : S.FreeMonoidal) :
    (φ.comp ψ).toFunctor.obj X = (φ.toFunctor ⋙ ψ.toFunctor).obj X := by
  rw [toFunctor, toSubstitution_comp]
  exact (FreeMonoidal.projectObj_projectObj_as ψ.toSubstitution.obj φ.toSubstitution.obj X.as).symm

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
        Functor.leftUnitor φ.toFunctor =
      eqToIso (congrArg toFunctor (Hom.id_comp φ)) := by
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
        Functor.rightUnitor φ.toFunctor =
      eqToIso (congrArg toFunctor (Hom.comp_id φ)) := by
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
