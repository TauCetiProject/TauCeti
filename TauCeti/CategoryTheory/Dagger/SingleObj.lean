/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Linear.SingleObj

/-!
# Dagger structure on single-object categories

A star monoid `M` makes `CategoryTheory.SingleObj M` a dagger category in which categorical
composition is opposite to multiplication (`f ≫ g = g * f`), so `dagger` is `star` and
`End (SingleObj.star M)` recovers `M` with its original multiplication and star. When `A` is a
star ring (or `R`-star algebra), `SingleObj A` inherits `DaggerPreadditive`, `DaggerLinear`, and
the canonical `⋆`-algebra isomorphism `SingleObj.toEndStarAlgEquiv`.
-/

public section

open CategoryTheory TauCeti

universe w u v

namespace CategoryTheory.SingleObj

instance instDaggerCategory (M : Type u) [Monoid M] [StarMul M] :
    DaggerCategory (SingleObj M) where
  dagger f := Star.star f
  dagger_id _ := star_one M
  dagger_comp f g := star_mul g f
  dagger_dagger := star_star

/-- In `SingleObj M`, the categorical dagger is the monoid `star`. -/
theorem dagger_as_star {M : Type u} [Monoid M] [StarMul M] {X Y : SingleObj M} (f : X ⟶ Y) :
    dagger f = Star.star f := (rfl)

/-- Unitary arrows in `SingleObj M` are precisely elements of `unitary M`. -/
theorem isUnitary_iff_mem_unitary {M : Type u} [Monoid M] [StarMul M] {X Y : SingleObj M}
    (f : X ⟶ Y) : IsUnitary f ↔ (f : M) ∈ unitary M :=
  (isUnitary_iff f).trans (Unitary.mem_iff (U := (f : M))).symm

instance instDaggerPreadditive (A : Type u) [Ring A] [StarRing A] :
    DaggerPreadditive (SingleObj A) where
  dagger_add := star_add

instance instDaggerLinear (R : Type w) (A : Type u) [Semiring R] [Star R] [Ring A] [StarRing A]
    [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A] :
    DaggerLinear R (SingleObj A) where
  dagger_smul := star_smul

/-- The endomorphism `⋆`-algebra of the unique object of `SingleObj A` is canonically isomorphic
to `A`. -/
def toEndStarAlgEquiv (R : Type w) (A : Type u) [CommSemiring R] [Ring A] [StarRing A]
    [Algebra R A] : A ≃⋆ₐ[R] End (SingleObj.star A) where
  toEquiv := (toEndAlgEquiv R A).toEquiv
  map_mul' := map_mul (toEndAlgEquiv R A)
  map_add' := map_add (toEndAlgEquiv R A)
  map_smul' := map_smul (toEndAlgEquiv R A)
  map_star' a := by
    ext
    simp [dagger_as_star]

/-- Forward evaluation of `SingleObj.toEndStarAlgEquiv`. -/
@[simp] theorem toEndStarAlgEquiv_apply {R : Type w} {A : Type u} [CommSemiring R] [Ring A]
    [StarRing A] [Algebra R A] (a : A) : toEndStarAlgEquiv R A a = .of a := by
  simp [toEndStarAlgEquiv]

/-- Inverse evaluation of `SingleObj.toEndStarAlgEquiv`. -/
@[simp] theorem toEndStarAlgEquiv_symm_apply {R : Type w} {A : Type u} [CommSemiring R] [Ring A]
    [StarRing A] [Algebra R A] (f : End (SingleObj.star A)) :
    (toEndStarAlgEquiv R A).symm f = f.asHom := by
  simp [toEndStarAlgEquiv]

/-- A monoid homomorphism commuting with `star` induces a dagger-preserving functor between
single-object categories. -/
theorem preservesDagger_mapHom {M : Type u} {N : Type v} [Monoid M] [StarMul M] [Monoid N]
    [StarMul N] (φ : M →* N) (hφ : ∀ x, φ (Star.star x) = Star.star (φ x)) :
    (SingleObj.mapHom M N φ).PreservesDagger where
  map_dagger := hφ

end CategoryTheory.SingleObj
