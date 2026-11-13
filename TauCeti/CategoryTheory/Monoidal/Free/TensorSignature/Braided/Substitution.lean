/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Braided.Basic

/-!
# Substitution of braided tensor expressions for coupons

A `TensorSignature.BraidedSubstitution S T` replaces object generators of `S` by formal tensor
words in `T.FreeBraided` and coupons of `S` by raw braided morphism expressions in `T` with the
substituted source and target boundaries. Object generators may be sent to the unit or to composite
tensor words, and nullary coupons retain their unit boundaries.

`FreeBraided.Hom.subst` performs this replacement on raw expressions before quotienting by the
braided monoidal axioms; `FreeBraided.HomEquiv.subst` shows that it preserves the braided
congruence. On equivalence classes, `BraidedSubstitution.toFunctor` is the strong braided functor
given by `FreeBraided.lift`, and `BraidedSubstitution.toFunctor_map_homMk` identifies its action on
representatives with raw substitution.

## Main definitions and results

* `TauCeti.TensorSignature.BraidedSubstitution S T`: typed raw braided substitutions between tensor
  signatures across independent universes.
* `FreeBraided.Hom.subst` and `FreeBraided.HomEquiv.subst`: raw braided substitution and its
  soundness with respect to the braided monoidal axioms.
* `BraidedSubstitution.toFunctor` and `BraidedSubstitution.toFunctor_map_homMk`: the induced strong
  braided functor `S.FreeBraided ⥤ T.FreeBraided` and its agreement with `FreeBraided.Hom.subst` on
  representatives.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

/-- A typed braided substitution between tensor signatures. Generating objects are replaced by
objects of `T.FreeBraided`, and coupons by raw braided morphism expressions with the substituted
source and target words. The object and coupon universes of `S` and `T` are independent. -/
@[ext]
structure BraidedSubstitution (S : TensorSignature.{u, v}) (T : TensorSignature.{u', v'}) where
  /-- The tensor word in `T.FreeBraided` replacing each generating object of `S`. -/
  obj : S.Obj → T.FreeBraided
  /-- The raw braided morphism expression replacing each coupon of `S`. -/
  coupon : ∀ g : S.Coupon,
    FreeBraided.Hom (projectObj obj (S.src g)).as (projectObj obj (S.tgt g)).as

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}

namespace FreeBraided

/-- Substitute formal tensor words for generating objects and raw braided expressions for coupons.
Endpoints are interpreted by `FreeMonoidalCategory.projectObj`. -/
def Hom.subst (σ : BraidedSubstitution S T) :
    ∀ {X Y : FreeMonoidalCategory S.Obj},
      Hom X Y → Hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .id X => .id (projectObj σ.obj X).as
  | _, _, .α_hom X Y Z =>
    .α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .α_inv X Y Z =>
    .α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as
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
    (Hom.id X).subst σ = .id (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_coupon (σ : BraidedSubstitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := by rfl

@[simp]
theorem Hom.subst_comp (σ : BraidedSubstitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_tensor (σ : BraidedSubstitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_whiskerLeft (σ : BraidedSubstitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_whiskerRight (σ : BraidedSubstitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_α_hom (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_hom X Y Z).subst σ =
      .α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_α_inv (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_inv X Y Z).subst σ =
      .α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_l_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_l_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_β_hom (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_hom X Y).subst σ = .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as := by rfl

@[simp]
theorem Hom.subst_β_inv (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_inv X Y).subst σ = .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as := by rfl

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

variable (σ : BraidedSubstitution S T)

-- Exposed so that `σ.toFunctor.obj ⟨X⟩` reduces to `projectObj σ.obj X`, matching the dependent
-- endpoint types of `FreeBraided.homMk (f.subst σ)` in `toFunctor_map_homMk`.
/-- The strong braided functor induced by a raw braided substitution: the universal lift of `σ.obj`
and the equivalence classes of `σ.coupon`. -/
@[expose] def toFunctor : S.FreeBraided ⥤ T.FreeBraided :=
  FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal :=
  inferInstanceAs (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Monoidal

instance : σ.toFunctor.Braided :=
  inferInstanceAs (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Braided

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

/-- Applying `σ.toFunctor` to the equivalence class of a raw braided expression gives the
equivalence class of its raw substitution `f.subst σ`. -/
@[simp]
theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    σ.toFunctor.map (FreeBraided.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeBraided.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id σ.obj _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom σ.obj _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv σ.obj _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom σ.obj _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv σ.obj _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom σ.obj _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv σ.obj _ ⟨X⟩
  | β_hom X Y => exact lift_map_braiding_hom σ.obj _ ⟨X⟩ ⟨Y⟩
  | β_inv X Y => exact lift_map_braiding_inv σ.obj _ ⟨X⟩ ⟨Y⟩
  | coupon g => exact (congrArg σ.toFunctor.map (homMk_coupon g)).trans (lift_map_coupon σ.obj _ g)
  | comp f g hf hg =>
    exact (liftMap_comp σ.obj _ (homMk f) (homMk g)).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X f hf =>
    exact (lift_map_whiskerLeft σ.obj _ ⟨X⟩ (homMk f)).trans
      (congrArg (projectObj σ.obj X ◁ ·) hf)
  | whiskerRight f X hf =>
    exact (lift_map_whiskerRight σ.obj _ (homMk f) ⟨X⟩).trans
      (congrArg (· ▷ projectObj σ.obj X) hf)
  | tensor f g hf hg =>
    exact (lift_map_tensorHom σ.obj _ (homMk f) (homMk g)).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

end BraidedSubstitution

namespace FreeBraided

/-- Raw braided substitution preserves the congruence generated by the braided monoidal axioms,
without requiring any equation among the replacing coupons. -/
theorem HomEquiv.subst (σ : BraidedSubstitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeBraided

end TauCeti.TensorSignature
