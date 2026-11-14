/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.EqToHom
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Braided.Basic
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Substitution

/-!
# Braided substitution of tensor expressions for coupons

A `TensorSignature.BraidedSubstitution S T` replaces object generators of `S` by formal tensor
words in `T.FreeBraided` and coupons of `S` by raw braided morphism expressions in `T` between the
substituted source and target words. An object generator may be replaced by the empty word or by a
multi-letter tensor word, and a multi-port coupon retains its substituted multi-port boundaries.

`FreeBraided.Hom.subst` performs this replacement on raw braided terms, commuting with composition,
whiskering, tensor products, associators, unitors, and positive and negative braidings. The strong
braided functor `BraidedSubstitution.toFunctor` is the universal lift of the substitution data, and
`BraidedSubstitution.toFunctor_map_homMk` identifies its morphism action with raw substitution;
`FreeBraided.HomEquiv.subst` deduces that raw substitution respects the braided monoidal axioms.

Braided substitutions form a category: `BraidedSubstitution.id` and `BraidedSubstitution.comp`
satisfy the left-unit, right-unit, and associativity laws strictly (`id_comp`, `comp_id`,
`comp_assoc`), and `toFunctor` preserves identities and composition up to monoidal natural
isomorphism (`idToFunctorIso`, `compToFunctorIso`). Every monoidal substitution embeds into a
braided substitution via `Substitution.toBraided`, compatibly with `FreeMonoidal.toFreeBraided`.

The construction extends `TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Substitution` by
braided crossings and substitution composition. The mathematical setting is Joyal and Street,
*The geometry of tensor calculus I*, §§1, 3.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
-/

public section

universe u v u' v' u'' v'' u''' v'''

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

/-- A typed braided substitution between tensor signatures: object generators are replaced by
formal tensor words in `T.FreeBraided`, and coupons by raw braided expressions between the
substituted source and target words. -/
@[ext]
structure BraidedSubstitution (S : TensorSignature.{u, v}) (T : TensorSignature.{u', v'}) where
  /-- The formal tensor word replacing each object generator. -/
  obj : S.Obj → T.FreeBraided
  /-- The raw braided expression replacing each coupon. -/
  coupon : ∀ g : S.Coupon, FreeBraided.Hom
    (projectObj obj (S.src g)).as (projectObj obj (S.tgt g)).as

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}
  {U : TensorSignature.{u'', v''}} {V : TensorSignature.{u''', v'''}}

namespace BraidedSubstitution

/-- Pointwise extensionality for braided substitutions using heterogeneous equality on coupons. -/
theorem ext' {σ₁ σ₂ : BraidedSubstitution S T} (h₁ : ∀ a, σ₁.obj a = σ₂.obj a)
    (h₂ : ∀ g, σ₁.coupon g ≍ σ₂.coupon g) : σ₁ = σ₂ := by
  cases σ₁ with | mk obj₁ c₁ =>
  cases σ₂ with | mk obj₂ c₂ =>
  have hobj : obj₁ = obj₂ := funext h₁
  subst hobj
  congr
  funext g
  exact eq_of_heq (h₂ g)

end BraidedSubstitution

namespace FreeBraided

/-- Substitute formal tensor words for object generators and raw braided expressions for
coupons. -/
def Hom.subst (σ : BraidedSubstitution S T) : ∀ {X Y}, Hom X Y →
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
  | _, _, .β_hom X Y => .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .β_inv X Y => .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .coupon g => σ.coupon g
  | _, _, .comp f g => (f.subst σ).comp (g.subst σ)
  | _, _, .whiskerLeft X f => (f.subst σ).whiskerLeft (projectObj σ.obj X).as
  | _, _, .whiskerRight f X => (f.subst σ).whiskerRight (projectObj σ.obj X).as
  | _, _, .tensor f g => (f.subst σ).tensor (g.subst σ)

@[simp]
theorem Hom.subst_id (σ : BraidedSubstitution S T) (X) :
    (Hom.id X).subst σ = .id (projectObj σ.obj X).as := (rfl)

@[simp]
theorem Hom.subst_coupon (σ : BraidedSubstitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := (rfl)

@[simp]
theorem Hom.subst_comp (σ : BraidedSubstitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := (rfl)

@[simp]
theorem Hom.subst_tensor (σ : BraidedSubstitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := (rfl)

@[simp]
theorem Hom.subst_whiskerLeft (σ : BraidedSubstitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (projectObj σ.obj X).as := (rfl)

@[simp]
theorem Hom.subst_whiskerRight (σ : BraidedSubstitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (projectObj σ.obj X).as := (rfl)

@[simp]
theorem Hom.subst_α_hom (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_hom X Y Z).subst σ =
      .α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := (rfl)

@[simp]
theorem Hom.subst_α_inv (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_inv X Y Z).subst σ =
      .α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := (rfl)

@[simp]
theorem Hom.subst_l_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (projectObj σ.obj X).as := (rfl)

@[simp]
theorem Hom.subst_l_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (projectObj σ.obj X).as := (rfl)

@[simp]
theorem Hom.subst_ρ_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (projectObj σ.obj X).as := (rfl)

@[simp]
theorem Hom.subst_ρ_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (projectObj σ.obj X).as := (rfl)

@[simp]
theorem Hom.subst_β_hom (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_hom X Y).subst σ =
      .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as := (rfl)

@[simp]
theorem Hom.subst_β_inv (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_inv X Y).subst σ =
      .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as := (rfl)

theorem Hom.subst_cast_heq (σ : BraidedSubstitution S T)
    {X X' Y Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y') (f : Hom X Y) :
    (f.cast hX hY).subst σ ≍ f.subst σ := by
  subst hX hY
  rw [Hom.cast_rfl]

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

variable (σ : BraidedSubstitution S T)

/-- The strong braided functor induced by a braided substitution. Its object action is exposed so
that raw substituted expressions have definitionally matching endpoints in representative
computation rules. -/
@[expose] def toFunctor : S.FreeBraided ⥤ T.FreeBraided :=
  FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal := inferInstanceAs
  (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Monoidal

instance : σ.toFunctor.Braided := inferInstanceAs
  (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Braided

@[simp]
theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_ε _ _

@[simp]
theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_η _ _

@[simp]
theorem toFunctor_μ (X Y : S.FreeBraided) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_μ _ _ X Y

@[simp]
theorem toFunctor_δ (X Y : S.FreeBraided) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_δ _ _ X Y

@[simp]
theorem toFunctor_obj (X : S.FreeBraided) :
    σ.toFunctor.obj X = projectObj σ.obj X.as := rfl

@[simp]
theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeBraided.coupon g) = FreeBraided.homMk (σ.coupon g) :=
  FreeBraided.lift_map_coupon _ _ g

/-- Interpreting a raw braided expression by `σ.toFunctor` produces the equivalence class of its
raw substitution `f.subst σ`. -/
@[simp]
theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    σ.toFunctor.map (FreeBraided.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeBraided.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | β_hom X Y => exact lift_map_braiding_hom _ _ ⟨X⟩ ⟨Y⟩
  | β_inv X Y => exact lift_map_braiding_inv _ _ ⟨X⟩ ⟨Y⟩
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

end BraidedSubstitution

namespace FreeBraided

/-- Braided substitution preserves the relation generated by the braided monoidal axioms. -/
theorem HomEquiv.subst (σ : BraidedSubstitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

private theorem Hom.id_heq {X X' : FreeMonoidalCategory S.Obj} (hX : X = X') :
    (Hom.id X : Hom X X) ≍ (Hom.id X' : Hom X' X') := by
  subst hX; rfl

private theorem Hom.α_hom_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    (Hom.α_hom X Y Z : Hom _ _) ≍ (Hom.α_hom X' Y' Z' : Hom _ _) := by
  subst hX hY hZ; rfl

private theorem Hom.α_inv_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    (Hom.α_inv X Y Z : Hom _ _) ≍ (Hom.α_inv X' Y' Z' : Hom _ _) := by
  subst hX hY hZ; rfl

private theorem Hom.l_hom_heq {X X' : FreeMonoidalCategory S.Obj} (hX : X = X') :
    (Hom.l_hom X : Hom _ _) ≍ (Hom.l_hom X' : Hom _ _) := by
  subst hX; rfl

private theorem Hom.l_inv_heq {X X' : FreeMonoidalCategory S.Obj} (hX : X = X') :
    (Hom.l_inv X : Hom _ _) ≍ (Hom.l_inv X' : Hom _ _) := by
  subst hX; rfl

private theorem Hom.ρ_hom_heq {X X' : FreeMonoidalCategory S.Obj} (hX : X = X') :
    (Hom.ρ_hom X : Hom _ _) ≍ (Hom.ρ_hom X' : Hom _ _) := by
  subst hX; rfl

private theorem Hom.ρ_inv_heq {X X' : FreeMonoidalCategory S.Obj} (hX : X = X') :
    (Hom.ρ_inv X : Hom _ _) ≍ (Hom.ρ_inv X' : Hom _ _) := by
  subst hX; rfl

private theorem Hom.β_hom_heq {X X' Y Y' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') :
    (Hom.β_hom X Y : Hom _ _) ≍ (Hom.β_hom X' Y' : Hom _ _) := by
  subst hX hY; rfl

private theorem Hom.β_inv_heq {X X' Y Y' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') :
    (Hom.β_inv X Y : Hom _ _) ≍ (Hom.β_inv X' Y' : Hom _ _) := by
  subst hX hY; rfl

private theorem Hom.comp_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : Hom X Y} {f' : Hom X' Y'} {g : Hom Y Z} {g' : Hom Y' Z'}
    (hf : f ≍ f') (hg : g ≍ g') : f.comp g ≍ f'.comp g' := by
  subst hX hY hZ; cases hf; cases hg; rfl

private theorem Hom.whiskerLeft_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : Hom Y Z} {f' : Hom Y' Z'} (hf : f ≍ f') :
    f.whiskerLeft X ≍ f'.whiskerLeft X' := by
  subst hX hY hZ; cases hf; rfl

private theorem Hom.whiskerRight_heq {X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : Hom X Y} {f' : Hom X' Y'} (hf : f ≍ f') :
    f.whiskerRight Z ≍ f'.whiskerRight Z' := by
  subst hX hY hZ; cases hf; rfl

private theorem Hom.tensor_heq {W W' X X' Y Y' Z Z' : FreeMonoidalCategory S.Obj}
    (hW : W = W') (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : Hom W Y} {f' : Hom W' Y'} {g : Hom X Z} {g' : Hom X' Z'}
    (hf : f ≍ f') (hg : g ≍ g') : f.tensor g ≍ f'.tensor g' := by
  subst hW hX hY hZ; cases hf; cases hg; rfl

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

/-! ### Identity and composition of braided substitutions -/

/-- The coupon action of `BraidedSubstitution.id`. -/
def idCoupon (S : TensorSignature.{u, v}) (g : S.Coupon) :
    FreeBraided.Hom (projectObj FreeBraided.of (S.src g)).as
      (projectObj FreeBraided.of (S.tgt g)).as :=
  (Hom.coupon g).cast
    (congrArg FreeBraided.as (projectObj_of_eq (S.src g))).symm
    (congrArg FreeBraided.as (projectObj_of_eq (S.tgt g))).symm

/-- The identity braided substitution on `S`, sending each object generator to itself and each
coupon to itself along the canonical word identification `projectObj_of_eq`. -/
@[expose] def id (S : TensorSignature.{u, v}) : BraidedSubstitution S S where
  obj := FreeBraided.of
  coupon := idCoupon S

@[simp]
theorem id_obj (a : S.Obj) : (id S).obj a = FreeBraided.of a := rfl

private theorem id_projectObj_as (X : FreeMonoidalCategory S.Obj) :
    (projectObj (id S).obj X).as = X :=
  congrArg FreeBraided.as (projectObj_of_eq X)

/-- Substituting the identity braided substitution into any raw braided expression leaves it
unchanged (heterogeneously, and strictly after casting endpoints). -/
theorem subst_id_heq {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    f.subst (id S) ≍ f := by
  induction f with
  | id X => exact Hom.id_heq (id_projectObj_as X)
  | α_hom X Y Z =>
    exact Hom.α_hom_heq (id_projectObj_as X) (id_projectObj_as Y) (id_projectObj_as Z)
  | α_inv X Y Z =>
    exact Hom.α_inv_heq (id_projectObj_as X) (id_projectObj_as Y) (id_projectObj_as Z)
  | l_hom X => exact Hom.l_hom_heq (id_projectObj_as X)
  | l_inv X => exact Hom.l_inv_heq (id_projectObj_as X)
  | ρ_hom X => exact Hom.ρ_hom_heq (id_projectObj_as X)
  | ρ_inv X => exact Hom.ρ_inv_heq (id_projectObj_as X)
  | β_hom X Y => exact Hom.β_hom_heq (id_projectObj_as X) (id_projectObj_as Y)
  | β_inv X Y => exact Hom.β_inv_heq (id_projectObj_as X) (id_projectObj_as Y)
  | coupon g => exact Hom.cast_heq _ _ (Hom.coupon g)
  | comp _ _ hf hg =>
    exact Hom.comp_heq (id_projectObj_as _) (id_projectObj_as _) (id_projectObj_as _) hf hg
  | whiskerLeft _ _ hf =>
    exact Hom.whiskerLeft_heq (id_projectObj_as _) (id_projectObj_as _) (id_projectObj_as _) hf
  | whiskerRight _ _ hf =>
    exact Hom.whiskerRight_heq (id_projectObj_as _) (id_projectObj_as _) (id_projectObj_as _) hf
  | tensor _ _ hf hg =>
    exact Hom.tensor_heq (id_projectObj_as _) (id_projectObj_as _)
      (id_projectObj_as _) (id_projectObj_as _) hf hg

/-- Interpreting a word along composite generator images agrees with iterating `projectObj`. -/
theorem comp_projectObj_eq (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    projectObj (fun a ↦ projectObj τ.obj (σ.obj a).as) X =
      projectObj τ.obj (projectObj σ.obj X).as := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor _ _ hX hY => exact congrArg₂ (· ⊗ ·) hX hY

/-- The coupon action of `BraidedSubstitution.comp`. -/
def compCoupon (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) (g : S.Coupon) :
    FreeBraided.Hom (projectObj (fun a ↦ projectObj τ.obj (σ.obj a).as) (S.src g)).as
      (projectObj (fun a ↦ projectObj τ.obj (σ.obj a).as) (S.tgt g)).as :=
  ((σ.coupon g).subst τ).cast
    (congrArg FreeBraided.as (comp_projectObj_eq τ σ (S.src g))).symm
    (congrArg FreeBraided.as (comp_projectObj_eq τ σ (S.tgt g))).symm

/-- Composition of braided substitutions: `τ.comp σ` first applies `σ` and then `τ`. -/
@[expose] def comp (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) :
    BraidedSubstitution S U where
  obj a := projectObj τ.obj (σ.obj a).as
  coupon := compCoupon τ σ

@[simp]
theorem comp_obj (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) (a : S.Obj) :
    (τ.comp σ).obj a = projectObj τ.obj (σ.obj a).as := rfl

private theorem comp_projectObj_as (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    (projectObj τ.obj (projectObj σ.obj X).as).as = (projectObj (τ.comp σ).obj X).as :=
  (congrArg FreeBraided.as (comp_projectObj_eq τ σ X)).symm

/-- Iterated raw braided substitution agrees with substituting the composite braided
substitution. -/
theorem subst_comp_heq (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    (f.subst σ).subst τ ≍ f.subst (τ.comp σ) := by
  induction f with
  | id X => exact Hom.id_heq (comp_projectObj_as τ σ X)
  | α_hom X Y Z =>
    exact Hom.α_hom_heq (comp_projectObj_as τ σ X) (comp_projectObj_as τ σ Y)
      (comp_projectObj_as τ σ Z)
  | α_inv X Y Z =>
    exact Hom.α_inv_heq (comp_projectObj_as τ σ X) (comp_projectObj_as τ σ Y)
      (comp_projectObj_as τ σ Z)
  | l_hom X => exact Hom.l_hom_heq (comp_projectObj_as τ σ X)
  | l_inv X => exact Hom.l_inv_heq (comp_projectObj_as τ σ X)
  | ρ_hom X => exact Hom.ρ_hom_heq (comp_projectObj_as τ σ X)
  | ρ_inv X => exact Hom.ρ_inv_heq (comp_projectObj_as τ σ X)
  | β_hom X Y => exact Hom.β_hom_heq (comp_projectObj_as τ σ X) (comp_projectObj_as τ σ Y)
  | β_inv X Y => exact Hom.β_inv_heq (comp_projectObj_as τ σ X) (comp_projectObj_as τ σ Y)
  | coupon g => exact (Hom.cast_heq _ _ ((σ.coupon g).subst τ)).symm
  | comp _ _ hf hg =>
    exact Hom.comp_heq (comp_projectObj_as τ σ _) (comp_projectObj_as τ σ _)
      (comp_projectObj_as τ σ _) hf hg
  | whiskerLeft _ _ hf =>
    exact Hom.whiskerLeft_heq (comp_projectObj_as τ σ _) (comp_projectObj_as τ σ _)
      (comp_projectObj_as τ σ _) hf
  | whiskerRight _ _ hf =>
    exact Hom.whiskerRight_heq (comp_projectObj_as τ σ _) (comp_projectObj_as τ σ _)
      (comp_projectObj_as τ σ _) hf
  | tensor _ _ hf hg =>
    exact Hom.tensor_heq (comp_projectObj_as τ σ _) (comp_projectObj_as τ σ _)
      (comp_projectObj_as τ σ _) (comp_projectObj_as τ σ _) hf hg

@[simp]
theorem id_comp (σ : BraidedSubstitution S T) : (id T).comp σ = σ :=
  ext' (fun a ↦ projectObj_of_eq (σ.obj a).as) fun g ↦
    (Hom.cast_heq _ _ _).trans (subst_id_heq (σ.coupon g))

@[simp]
theorem comp_id (σ : BraidedSubstitution S T) : σ.comp (id S) = σ := by
  refine ext' (fun _ ↦ rfl) (fun g ↦ ?_)
  exact (Hom.cast_heq _ _ _).trans (Hom.subst_cast_heq σ _ _ (Hom.coupon g))

/-- Composition of braided substitutions is associative. -/
theorem comp_assoc (υ : BraidedSubstitution U V) (τ : BraidedSubstitution T U)
    (σ : BraidedSubstitution S T) :
    (υ.comp τ).comp σ = υ.comp (τ.comp σ) := by
  refine ext' (fun a ↦ comp_projectObj_eq υ τ (σ.obj a).as) (fun g ↦ ?_)
  have hL : ((υ.comp τ).comp σ).coupon g ≍ ((σ.coupon g).subst τ).subst υ :=
    (Hom.cast_heq _ _ _).trans (subst_comp_heq υ τ (σ.coupon g)).symm
  have hR : (υ.comp (τ.comp σ)).coupon g ≍ ((σ.coupon g).subst τ).subst υ :=
    (Hom.cast_heq _ _ _).trans (Hom.subst_cast_heq υ _ _ ((σ.coupon g).subst τ))
  exact hL.trans hR.symm

/-! ### Functoriality of `toFunctor` up to monoidal natural isomorphism -/

private theorem freeBraided_comp_eqToHom_comp {U : TensorSignature.{u'', v''}}
    {A' A B B' : U.FreeBraided} (hA : A' = A) (hB : B = B')
    {f : A' ⟶ A} {g : B ⟶ B'} (hf : f = eqToHom hA) (hg : g = eqToHom hB)
    (hab : A = B) (ha'b' : A' = B') :
    f ≫ eqToHom hab ≫ g = eqToHom ha'b' := by
  rw [hf, hg, eqToHom_trans, eqToHom_trans]

private theorem freeBraided_eq_comp_eqToHom {U : TensorSignature.{u'', v''}}
    {A₁ A₂ B₁ B₂ : U.FreeBraided} {f : A₁ ⟶ B₁} {g : A₂ ⟶ B₂}
    (hA : A₁ = A₂) (hB : B₁ = B₂)
    (hf : f = eqToHom hA ≫ g ≫ eqToHom hB.symm) :
    f ≫ eqToHom hB = eqToHom hA ≫ g := by
  rw [hf, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem wordIso_eqToIso_hom {D : Type*} [Category* D] [MonoidalCategory D]
    (F G : S.FreeBraided ⥤ D) [F.Monoidal] [G.Monoidal]
    (h : ∀ X : S.FreeBraided, F.obj X = G.obj X)
    (h_unit : Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε G =
      eqToHom (h (𝟙_ S.FreeBraided)))
    (h_tensor : ∀ X Y : S.FreeBraided,
      Functor.OplaxMonoidal.δ F X Y ≫ (eqToHom (h X) ⊗ₘ eqToHom (h Y)) ≫
        Functor.LaxMonoidal.μ G X Y = eqToHom (h (X ⊗ Y)))
    (X : FreeMonoidalCategory S.Obj) :
    (FreeBraided.wordIso F G (fun a ↦ eqToIso (h (FreeBraided.of a))) X).hom =
      eqToHom (h ⟨X⟩) := by
  induction X with
  | of a =>
    exact (congrArg Iso.hom (FreeBraided.wordIso_of F G _ a)).trans (eqToIso.hom _)
  | unit =>
    exact (FreeBraided.wordIso_tensorUnit_hom F G _).trans h_unit
  | tensor Y Z hY hZ =>
    exact (FreeBraided.wordIso_tensor_hom F G _ ⟨Y⟩ ⟨Z⟩).trans
      ((congrArg
        (fun m ↦
          Functor.OplaxMonoidal.δ F ⟨Y⟩ ⟨Z⟩ ≫ m ≫ Functor.LaxMonoidal.μ G ⟨Y⟩ ⟨Z⟩)
        (congrArg₂ (· ⊗ₘ ·) hY hZ)).trans (h_tensor ⟨Y⟩ ⟨Z⟩))

private theorem id_toFunctor_obj (X : S.FreeBraided) :
    (id S).toFunctor.obj X = (𝟭 S.FreeBraided).obj X :=
  projectObj_of_eq X.as

private theorem wordIso_id_hom (X : FreeMonoidalCategory S.Obj) :
    (FreeBraided.wordIso (id S).toFunctor (𝟭 S.FreeBraided)
      (fun a ↦ eqToIso (id_toFunctor_obj (FreeBraided.of a))) X).hom =
      eqToHom (id_toFunctor_obj ⟨X⟩) := by
  refine wordIso_eqToIso_hom _ _ id_toFunctor_obj ?_ (fun Y Z ↦ ?_) X
  · exact (congrArg₂ (· ≫ ·) (id S).toFunctor_η Functor.LaxMonoidal.id_ε).trans
      ((Category.comp_id _).trans (eqToHom_refl _ _).symm)
  · refine (congrArg (fun m ↦ _ ≫ m ≫ _) (TauCeti.eqToHom_tensorHom_eqToHom _ _)).trans ?_
    refine freeBraided_comp_eqToHom_comp rfl rfl ?_ ?_ _ _
    · exact ((id S).toFunctor_δ Y Z).trans (eqToHom_refl _ _).symm
    · exact (Functor.LaxMonoidal.id_μ Y Z).trans (eqToHom_refl _ _).symm

/-- The strong braided functor of the identity substitution is monoidally naturally isomorphic to
the identity functor on `S.FreeBraided`. -/
def idToFunctorIso (S : TensorSignature.{u, v}) :
    (id S).toFunctor ≅ 𝟭 S.FreeBraided :=
  FreeBraided.monoidalNatIso fun g ↦ by
    rw [wordIso_id_hom, wordIso_id_hom]
    exact freeBraided_eq_comp_eqToHom _ _
      (((id S).toFunctor_map_coupon g).trans (FreeBraided.homMk_cast _ _ (Hom.coupon g)))

instance (S : TensorSignature.{u, v}) : NatTrans.IsMonoidal (idToFunctorIso S).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (FreeBraided.monoidalNatIso _).hom)

@[simp]
theorem idToFunctorIso_hom_app_of (a : S.Obj) :
    (idToFunctorIso S).hom.app (FreeBraided.of a) = 𝟙 (FreeBraided.of a) :=
  (FreeBraided.monoidalNatIso_hom_app _ (FreeBraided.of a)).trans
    ((wordIso_id_hom (.of a)).trans (eqToHom_refl _ _))

private theorem comp_toFunctor_obj (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (X : S.FreeBraided) :
    (τ.comp σ).toFunctor.obj X = (σ.toFunctor ⋙ τ.toFunctor).obj X :=
  comp_projectObj_eq τ σ X.as

private theorem wordIso_comp_hom (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    (FreeBraided.wordIso (τ.comp σ).toFunctor (σ.toFunctor ⋙ τ.toFunctor)
      (fun a ↦ eqToIso (comp_toFunctor_obj τ σ (FreeBraided.of a))) X).hom =
      eqToHom (comp_toFunctor_obj τ σ ⟨X⟩) := by
  refine wordIso_eqToIso_hom _ _ (comp_toFunctor_obj τ σ) ?_ (fun Y Z ↦ ?_) X
  · have hε : Functor.LaxMonoidal.ε (σ.toFunctor ⋙ τ.toFunctor) = 𝟙 _ :=
      (Functor.LaxMonoidal.comp_ε σ.toFunctor τ.toFunctor).trans
        ((congrArg₂ (· ≫ ·) τ.toFunctor_ε
          ((congrArg τ.toFunctor.map σ.toFunctor_ε).trans (Functor.map_id _ _))).trans
          (Category.comp_id _))
    exact (congrArg₂ (· ≫ ·) (τ.comp σ).toFunctor_η hε).trans
      ((Category.comp_id _).trans (eqToHom_refl _ _).symm)
  · refine (congrArg (fun m ↦ _ ≫ m ≫ _) (TauCeti.eqToHom_tensorHom_eqToHom _ _)).trans ?_
    refine freeBraided_comp_eqToHom_comp rfl rfl ?_ ?_ _ _
    · exact ((τ.comp σ).toFunctor_δ Y Z).trans (eqToHom_refl _ _).symm
    · exact (Functor.LaxMonoidal.comp_μ σ.toFunctor τ.toFunctor Y Z).trans
        ((congrArg₂ (· ≫ ·) (τ.toFunctor_μ _ _)
          ((congrArg τ.toFunctor.map (σ.toFunctor_μ Y Z)).trans (Functor.map_id _ _))).trans
          ((Category.comp_id _).trans (eqToHom_refl _ _).symm))

/-- The strong braided functor of a composite substitution `τ.comp σ` is monoidally naturally
isomorphic to `σ.toFunctor ⋙ τ.toFunctor`. -/
def compToFunctorIso (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) :
    (τ.comp σ).toFunctor ≅ σ.toFunctor ⋙ τ.toFunctor :=
  FreeBraided.monoidalNatIso fun g ↦ by
    rw [wordIso_comp_hom, wordIso_comp_hom]
    have hrhs : (σ.toFunctor ⋙ τ.toFunctor).map (FreeBraided.coupon g) =
        FreeBraided.homMk ((σ.coupon g).subst τ) :=
      (congrArg τ.toFunctor.map (σ.toFunctor_map_coupon g)).trans
        (τ.toFunctor_map_homMk (σ.coupon g))
    exact freeBraided_eq_comp_eqToHom _ _
      (((τ.comp σ).toFunctor_map_coupon g).trans
        ((FreeBraided.homMk_cast _ _ ((σ.coupon g).subst τ)).trans
          (congrArg (fun m ↦ eqToHom _ ≫ m ≫ eqToHom _) hrhs.symm)))

instance (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T) :
    NatTrans.IsMonoidal (compToFunctorIso τ σ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (FreeBraided.monoidalNatIso _).hom)

@[simp]
theorem compToFunctorIso_hom_app_of (τ : BraidedSubstitution T U) (σ : BraidedSubstitution S T)
    (a : S.Obj) :
    (compToFunctorIso τ σ).hom.app (FreeBraided.of a) = 𝟙 ((τ.comp σ).obj a) :=
  (FreeBraided.monoidalNatIso_hom_app _ (FreeBraided.of a)).trans
    ((wordIso_comp_hom τ σ (.of a)).trans (eqToHom_refl _ _))

end BraidedSubstitution

namespace Substitution

/-! ### Comparison with monoidal substitutions -/

/-- Interpreting a word along `FreeMonoidal.toFreeBraided.obj ∘ σ.obj` agrees with applying
`FreeMonoidal.toFreeBraided` to `projectObj σ.obj X`. -/
theorem toFreeBraided_projectObj_eq (σ : Substitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    projectObj (fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a)) X =
      FreeMonoidal.toFreeBraided.obj (projectObj σ.obj X) := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor _ _ hX hY => exact congrArg₂ (· ⊗ ·) hX hY

private theorem toFreeBraided_projectObj_as (σ : Substitution S T)
    (X : FreeMonoidalCategory S.Obj) :
    (projectObj (fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a)) X).as =
      (projectObj σ.obj X).as :=
  congrArg FreeBraided.as (toFreeBraided_projectObj_eq σ X)

/-- The coupon action of `Substitution.toBraided`. -/
def toBraidedCoupon (σ : Substitution S T) (g : S.Coupon) :
    FreeBraided.Hom (projectObj (fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a)) (S.src g)).as
      (projectObj (fun a ↦ FreeMonoidal.toFreeBraided.obj (σ.obj a)) (S.tgt g)).as :=
  ((σ.coupon g).toBraided).cast
    (toFreeBraided_projectObj_as σ (S.src g)).symm
    (toFreeBraided_projectObj_as σ (S.tgt g)).symm

/-- Embed a monoidal substitution `Substitution S T` into a `BraidedSubstitution S T`. -/
@[expose] def toBraided (σ : Substitution S T) : BraidedSubstitution S T where
  obj a := FreeMonoidal.toFreeBraided.obj (σ.obj a)
  coupon := toBraidedCoupon σ

@[simp]
theorem toBraided_obj (σ : Substitution S T) (a : S.Obj) :
    σ.toBraided.obj a = FreeMonoidal.toFreeBraided.obj (σ.obj a) := rfl

private theorem toBraided_toFunctor_obj (σ : Substitution S T) (X : S.FreeMonoidal) :
    (FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor).obj X =
      (σ.toFunctor ⋙ FreeMonoidal.toFreeBraided).obj X :=
  toFreeBraided_projectObj_eq σ X.as

private theorem wordIso_toBraided_hom (σ : Substitution S T) (X : FreeMonoidalCategory S.Obj) :
    (FreeMonoidal.wordIso (FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor)
      (σ.toFunctor ⋙ FreeMonoidal.toFreeBraided)
      (fun a ↦ eqToIso (toBraided_toFunctor_obj σ (FreeMonoidal.of a))) X).hom =
      eqToHom (toBraided_toFunctor_obj σ ⟨X⟩) := by
  let F := FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor
  let G := σ.toFunctor ⋙ FreeMonoidal.toFreeBraided
  let e := fun a ↦ eqToIso (toBraided_toFunctor_obj σ (FreeMonoidal.of a))
  induction X with
  | of a =>
    exact (congrArg Iso.hom (FreeMonoidal.wordIso_of F G e a)).trans (eqToIso.hom _)
  | unit =>
    have hη : Functor.OplaxMonoidal.η F = 𝟙 _ :=
      (Functor.OplaxMonoidal.comp_η FreeMonoidal.toFreeBraided σ.toBraided.toFunctor).trans
        ((congrArg₂ (· ≫ ·)
          ((congrArg σ.toBraided.toFunctor.map FreeMonoidal.toFreeBraided_η).trans
            (Functor.map_id _ _))
          σ.toBraided.toFunctor_η).trans (Category.id_comp _))
    have hε : Functor.LaxMonoidal.ε G = 𝟙 _ :=
      (Functor.LaxMonoidal.comp_ε σ.toFunctor FreeMonoidal.toFreeBraided).trans
        ((congrArg₂ (· ≫ ·) FreeMonoidal.toFreeBraided_ε
          ((congrArg FreeMonoidal.toFreeBraided.map σ.toFunctor_ε).trans
            (Functor.map_id _ _))).trans (Category.comp_id _))
    exact (FreeMonoidal.wordIso_tensorUnit_hom F G e).trans
      ((congrArg₂ (· ≫ ·) hη hε).trans
        ((Category.comp_id _).trans (eqToHom_refl _ _).symm))
  | tensor Y Z hY hZ =>
    refine (FreeMonoidal.wordIso_tensor_hom F G e ⟨Y⟩ ⟨Z⟩).trans ?_
    refine (congrArg
      (fun m ↦
        Functor.OplaxMonoidal.δ F ⟨Y⟩ ⟨Z⟩ ≫ m ≫ Functor.LaxMonoidal.μ G ⟨Y⟩ ⟨Z⟩)
      ((congrArg₂ (· ⊗ₘ ·) hY hZ).trans
        (TauCeti.eqToHom_tensorHom_eqToHom _ _))).trans ?_
    refine BraidedSubstitution.freeBraided_comp_eqToHom_comp rfl rfl ?_ ?_ _ _
    · have hδ := congrArg σ.toBraided.toFunctor.map (FreeMonoidal.toFreeBraided_δ ⟨Y⟩ ⟨Z⟩)
      exact (Functor.OplaxMonoidal.comp_δ
        FreeMonoidal.toFreeBraided σ.toBraided.toFunctor ⟨Y⟩ ⟨Z⟩).trans
        ((congrArg₂ (· ≫ ·) (hδ.trans (Functor.map_id _ _))
          (σ.toBraided.toFunctor_δ _ _)).trans
          ((Category.id_comp _).trans (eqToHom_refl _ _).symm))
    · have hμ := congrArg FreeMonoidal.toFreeBraided.map (σ.toFunctor_μ ⟨Y⟩ ⟨Z⟩)
      exact (Functor.LaxMonoidal.comp_μ
        σ.toFunctor FreeMonoidal.toFreeBraided ⟨Y⟩ ⟨Z⟩).trans
        ((congrArg₂ (· ≫ ·) (FreeMonoidal.toFreeBraided_μ _ _)
          (hμ.trans (Functor.map_id _ _))).trans
          ((Category.comp_id _).trans (eqToHom_refl _ _).symm))

/-- `FreeMonoidal.toFreeBraided` intertwines `σ.toFunctor` and `σ.toBraided.toFunctor` up to a
monoidal natural isomorphism. -/
def toBraidedToFunctorIso (σ : Substitution S T) :
    FreeMonoidal.toFreeBraided ⋙ σ.toBraided.toFunctor ≅
      σ.toFunctor ⋙ FreeMonoidal.toFreeBraided :=
  FreeMonoidal.monoidalNatIso fun g ↦ by
    rw [wordIso_toBraided_hom, wordIso_toBraided_hom]
    have hrhs : (σ.toFunctor ⋙ FreeMonoidal.toFreeBraided).map (FreeMonoidal.coupon g) =
        FreeBraided.homMk (X := ⟨(projectObj σ.obj (S.src g)).as⟩)
          (Y := ⟨(projectObj σ.obj (S.tgt g)).as⟩) (σ.coupon g).toBraided :=
      (congrArg FreeMonoidal.toFreeBraided.map (σ.toFunctor_map_coupon g)).trans
        (FreeMonoidal.toFreeBraided_map_homMk (σ.coupon g))
    exact BraidedSubstitution.freeBraided_eq_comp_eqToHom _ _
      ((congrArg σ.toBraided.toFunctor.map (FreeMonoidal.toFreeBraided_map_coupon g)).trans
        ((σ.toBraided.toFunctor_map_coupon g).trans
          ((FreeBraided.homMk_cast _ _ (σ.coupon g).toBraided).trans
            (congrArg (fun m ↦ eqToHom _ ≫ m ≫ eqToHom _) hrhs.symm))))

instance (σ : Substitution S T) : NatTrans.IsMonoidal (toBraidedToFunctorIso σ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (FreeMonoidal.monoidalNatIso _).hom)

end Substitution

end TauCeti.TensorSignature
