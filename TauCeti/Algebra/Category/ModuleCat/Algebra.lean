/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.BilinearMap
-- Non-public: the finiteness transfer for linear maps is used only inside the proof.
import TauCeti.RingTheory.Noetherian.LinearMap

/-!
# Finitely generated morphism modules over a finite algebra

For an algebra `A` over a commutative ring `R`, Mathlib's scoped `ModuleCat.Algebra.instLinear`
makes `ModuleCat A` an `R`-linear category. When `R` is Noetherian and `A` is finitely generated
as an `R`-module (for instance an Artin algebra, or a finite-dimensional algebra over a field), the
morphisms between two finitely generated `A`-modules form a finitely generated `R`-module (the
instance `ModuleCat.finite_hom_of_finite`, and `FGModuleCat.finite_hom` in `FGModuleCat A`). This is
the Hom-finiteness that dimension and length counts in the module category of such an algebra rest
on.

The morphism space is identified with the `A`-linear maps by `ModuleCat.homLinearEquiv`, and
those embed in maps into a power of the target by `TauCeti.isNoetherian_linearMap_of_finite`.

Morphisms into a bundled module `B` are compared with the `A`-linear maps into a module `W` with a
compatible native `R`-action and `W ≃ₗ[A] B` by `ModuleCat.homLinearEquivOfLinearEquiv`; this
compares the `R`-action of the `R`-linear structure of `ModuleCat A` with the native one.

A module bundled in `ModuleCat A` remembers only the action of `A`. `ModuleCat.moduleOfAlgebra`
recovers its `R`-action through the algebra map, for any commutative base ring `R`; Mathlib records
this for algebras over a field in `ModuleCat.moduleOfAlgebraModule`.
-/

public section

open CategoryTheory

open scoped ModuleCat.Algebra

universe u v w

namespace ModuleCat

/-- A module over an `R`-algebra, as a module over `R`. Mathlib records this for algebras over a
field in `ModuleCat.moduleOfAlgebraModule`. -/
abbrev moduleOfAlgebra (R : Type u) [CommRing R] {B : Type v} [Ring B] [Algebra R B]
    (M : ModuleCat.{w} B) : Module R M :=
  Module.restrictScalars R B M

attribute [local instance] moduleOfAlgebra in
/-- The action of `R` given by `ModuleCat.moduleOfAlgebra` is the action through the algebra map. -/
theorem isScalarTower_moduleOfAlgebra (R : Type u) [CommRing R] {B : Type v} [Ring B] [Algebra R B]
    (M : ModuleCat.{w} B) : IsScalarTower R B M :=
  IsScalarTower.restrictScalars R B M

section HomTransport

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The bundled `Hom` equivalence `(Y ⟶ N) ≃ (Y →ₗ[A] N)` carries postcomposition with `g` to
postcomposition with the underlying linear map of `g`. -/
theorem homLinearEquiv_comp_rightComp {M N Y : ModuleCat.{w} A} (g : M ⟶ N) :
    (homLinearEquiv (S := R) : (Y ⟶ N) ≃ₗ[R] (Y →ₗ[A] N)).toLinearMap ∘ₗ
        Linear.rightComp R Y g =
      g.hom.compRight R ∘ₗ (homLinearEquiv (S := R) : (Y ⟶ M) ≃ₗ[R] (Y →ₗ[A] M)).toLinearMap :=
  LinearMap.ext fun _ ↦ rfl

variable {W : Type w} [AddCommGroup W] [Module A W] [Module R W] [IsScalarTower R A W]
  {B : ModuleCat.{w} A} (eW : W ≃ₗ[A] B)

/-- Morphisms into a bundled module `B` are the `A`-linear maps into `W`, for `W ≃ₗ[A] B`. On the
left, `R` acts through the `R`-linear structure of `ModuleCat A`, and on the right through its
action on `W`. -/
noncomputable def homLinearEquivOfLinearEquiv (N : ModuleCat.{w} A) :
    (N ⟶ B) ≃ₗ[R] (N →ₗ[A] W) where
  toFun f := eW.symm.toLinearMap ∘ₗ f.hom
  invFun g := ofHom (eW.toLinearMap ∘ₗ g)
  map_add' f g := LinearMap.ext fun x ↦ eW.symm.map_add (f x) (g x)
  -- Both actions of `c` are the action of `algebraMap R A c`.
  map_smul' c f := LinearMap.ext fun x ↦
    (eW.symm.map_smul (algebraMap R A c) (f.hom x)).trans
      (IsScalarTower.algebraMap_smul (M := W) A c (eW.symm (f.hom x)))
  left_inv f := by ext; simp
  right_inv g := by ext; simp

@[simp]
theorem homLinearEquivOfLinearEquiv_apply {N : ModuleCat.{w} A} (f : N ⟶ B) (x : N) :
    homLinearEquivOfLinearEquiv R eW N f x = eW.symm (f x) :=
  (rfl)

@[simp]
theorem homLinearEquivOfLinearEquiv_symm_apply {N : ModuleCat.{w} A} (g : N →ₗ[A] W) :
    (homLinearEquivOfLinearEquiv R eW N).symm g = ofHom (eW.toLinearMap ∘ₗ g) :=
  (rfl)

/-- Transporting `Hom` along `W ≃ B` carries precomposition with the underlying linear map of
`f : N ⟶ N'` to precomposition with `f`. -/
theorem homLinearEquivOfLinearEquiv_symm_comp_lcomp {N N' : ModuleCat.{w} A} (f : N ⟶ N') :
    (homLinearEquivOfLinearEquiv R eW N).symm.toLinearMap ∘ₗ f.hom.lcomp R W =
      Linear.leftComp R B f ∘ₗ (homLinearEquivOfLinearEquiv R eW N').symm.toLinearMap :=
  LinearMap.ext fun _ ↦ by ext; simp

end HomTransport

variable {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- Morphisms between finitely generated modules over a finite algebra over a Noetherian ring form a
finitely generated module over the base ring. -/
instance finite_hom_of_finite (M N : ModuleCat.{w} A) [Module.Finite A M]
    [Module.Finite A N] : Module.Finite R (M ⟶ N) := by
  have : Module.Finite R N := Module.Finite.trans A N
  exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := R)).symm

end ModuleCat

namespace FGModuleCat

variable {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- Morphisms in `FGModuleCat A`, for a finite algebra `A` over a Noetherian ring, form a finitely
generated module over the base ring. -/
instance finite_hom (X Y : FGModuleCat.{w} A) : Module.Finite R (X ⟶ Y) :=
  Module.Finite.equiv (InducedCategory.homLinearEquiv (R := R)).symm

end FGModuleCat
