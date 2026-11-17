/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.CategoryTheory.Monoidal.Braided.Adjunction
public import TauCeti.CategoryTheory.Monoidal.Internal.Module

import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Change of rings and tensor products of modules

Restriction and extension of scalars along a morphism of commutative rings are compatible with the
symmetric braiding on module categories (`TauCeti.ModuleCat.restrictScalarsLaxBraided`,
`TauCeti.ModuleCat.extendScalarsBraided`).

For a morphism `f : A →+* P` and a `P`-module `M`, tensoring an extension of scalars with `M`
over `P` is tensoring with `M` over `A`: `M ⊗[P] (P ⊗[A] X) ≅ M ⊗[A] X`, naturally in the
`A`-module `X` (`ModuleCat.extendScalarsCompTensorLeftIso`). This computes `Tor` over `A` by a
projective resolution over `P` after a flat extension of scalars.

For a morphism `f : R →+* S` of commutative rings, `ModuleCat.extendScalars_ε_apply` and
`ModuleCat.extendScalars_μ_tmul` record the elementwise action of the monoidal unit and tensorator
of `ModuleCat.extendScalars f`. For commutative `A`-algebras `P` and `R`, the functor induced on
commutative monoid objects by `ModuleCat.extendScalars (algebraMap A P)` agrees with the tensor
product `P`-algebra `P ⊗[A] R` (`ModuleCat.extendScalarsCommAlgIso`).
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.ModuleCat

universe u

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction of scalars between module categories preserves the symmetric braiding. -/
instance restrictScalarsLaxBraided : (_root_.ModuleCat.restrictScalars f).LaxBraided where
  braided _ _ := _root_.ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl

/-- Extension of scalars between module categories preserves the symmetric braiding. -/
instance extendScalarsBraided : (_root_.ModuleCat.extendScalars.{u, u, u} f).Braided :=
  (_root_.ModuleCat.extendRestrictScalarsAdj f).leftAdjointBraided

end

end TauCeti.ModuleCat

namespace ModuleCat

open scoped TensorProduct ChangeOfRings

universe u

section ProjectionFormula

variable {A P : Type u} [CommRing A] [CommRing P] (f : A →+* P)

/-- The `A`-linear equivalence `M ⊗[P] (P ⊗[A] X) ≃ M ⊗[A] X`, `m ⊗ (s ⊗ x) ↦ (s • m) ⊗ x`,
where `A` acts through `f`. -/
private noncomputable def tensorExtendScalarsLinearEquiv (M : ModuleCat.{u} P)
    (X : ModuleCat.{u} A) :
    (restrictScalars f).obj (M ⊗ (extendScalars f).obj X) ≃ₗ[A]
      ((restrictScalars f).obj M ⊗ X : ModuleCat A) :=
  letI := f.toAlgebra
  letI : Module A M := Module.compHom M f
  haveI : IsScalarTower A P M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A P P M X).restrictScalars A

/-- **Projection formula for extension of scalars.** For `f : A →+* P` and a `P`-module `M`,
`M ⊗[P] (P ⊗[A] X) ≅ M ⊗[A] X` as `A`-modules, naturally in the `A`-module `X`; it sends
`m ⊗ (s ⊗ x)` to `(s • m) ⊗ x`. -/
noncomputable def extendScalarsCompTensorLeftIso (M : ModuleCat.{u} P) :
    extendScalars.{u, u, u} f ⋙ tensorLeft M ⋙ restrictScalars.{u} f ≅
      tensorLeft ((restrictScalars f).obj M) :=
  (NatIso.ofComponents (fun X ↦ (tensorExtendScalarsLinearEquiv f M X).toModuleIso.symm)
    fun _ ↦ by apply MonoidalCategory.tensor_ext; intros; rfl).symm

/-- The forward map of `extendScalarsCompTensorLeftIso` sends `m ⊗ (s ⊗ x)` to `(s • m) ⊗ x`. -/
@[simp]
theorem extendScalarsCompTensorLeftIso_hom_app_tmul (M : ModuleCat.{u} P) (X : ModuleCat.{u} A)
    (m : M) (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj (M ⊗ (extendScalars f).obj X) ⟶
        (restrictScalars f).obj M ⊗ X) → _) ((extendScalarsCompTensorLeftIso f M).hom.app X)
        (TensorProduct.tmul P (M := M) (N := (extendScalars f).obj X) m (s ⊗ₜ[A, f] x)) =
      TensorProduct.tmul A (M := (restrictScalars f).obj M) (N := X) (s • m) x :=
  (rfl)

/-- The inverse of `extendScalarsCompTensorLeftIso` sends `m ⊗ x` to `m ⊗ (1 ⊗ x)`. -/
@[simp]
theorem extendScalarsCompTensorLeftIso_inv_app_tmul (M : ModuleCat.{u} P) (X : ModuleCat.{u} A)
    (m : (restrictScalars f).obj M) (x : X) :
    (Hom.hom : ((restrictScalars f).obj M ⊗ X ⟶
        (restrictScalars f).obj (M ⊗ (extendScalars f).obj X)) → _)
        ((extendScalarsCompTensorLeftIso f M).inv.app X)
        (TensorProduct.tmul A (M := (restrictScalars f).obj M) (N := X) m x) =
      TensorProduct.tmul P (M := M) (N := (extendScalars f).obj X) m ((1 : P) ⊗ₜ[A, f] x) :=
  (rfl)

end ProjectionFormula

section Monoidal

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The monoidal unit `Functor.LaxMonoidal.ε (extendScalars f)` sends `s : S` to `s ⊗ₜ 1`. -/
@[simp]
theorem extendScalars_ε_apply (s : S) :
    Functor.LaxMonoidal.ε (extendScalars.{u, u, u} f) s = s ⊗ₜ[R, f] (1 : R) :=
  letI := f.toAlgebra
  (ConcreteCategory.congr_hom (extendScalars_ε f) s).trans
    (TensorProduct.AlgebraTensorModule.rid_symm_apply R S s)

/-- On pure tensors, the tensorator `Functor.LaxMonoidal.μ (extendScalars f)` sends
`(s₁ ⊗ₜ m₁) ⊗ₜ (s₂ ⊗ₜ m₂)` to `(s₁ * s₂) ⊗ₜ (m₁ ⊗ₜ m₂)`. -/
@[simp]
theorem extendScalars_μ_tmul (M₁ M₂ : ModuleCat.{u} R) (s₁ s₂ : S) (m₁ : M₁) (m₂ : M₂) :
    Functor.LaxMonoidal.μ (extendScalars.{u, u, u} f) M₁ M₂
        (TensorProduct.tmul S (M := (extendScalars f).obj M₁) (N := (extendScalars f).obj M₂)
          (s₁ ⊗ₜ[R, f] m₁) (s₂ ⊗ₜ[R, f] m₂)) =
      (s₁ * s₂) ⊗ₜ[R, f] (TensorProduct.tmul R (M := M₁) (N := M₂) m₁ m₂ : ↑(M₁ ⊗ M₂)) :=
  letI := f.toAlgebra
  (ConcreteCategory.congr_hom (extendScalars_μ f M₁ M₂) _).trans
    (TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul R S m₁ m₂ s₁ s₂)

end Monoidal

section CommAlg

variable {A : Type u} [CommRing A]

/-- Extension of scalars of a commutative `A`-algebra `R` along `algebraMap A P` via
`ModuleCat.extendScalars` on commutative monoid objects agrees with the `P`-algebra `P ⊗[A] R`. -/
noncomputable def extendScalarsCommAlgIso (P : Type u) [CommRing P] [Algebra A P]
    (R : CommAlgCat.{u} A) :
    CommAlgCat.of P (P ⊗[A] R) ≅
      CommMonModuleEquivalenceCommAlgebra.functor.obj
        ((extendScalars.{u, u, u} (algebraMap A P)).mapCommMon.obj
          (CommMonModuleEquivalenceCommAlgebra.inverse.obj R)) :=
  let φ := algebraMap A P
  let G := extendScalars.{u, u, u} φ
  let R₀ := ModuleCat.of A R
  let R' := CommMonModuleEquivalenceCommAlgebra.inverse.obj R
  let B := CommMonModuleEquivalenceCommAlgebra.functor.obj (G.mapCommMon.obj R')
  let eLin : (P ⊗[A] R) ≃ₗ[P] B :=
    (extendScalarsAlgebraMapIso (S := P) R₀).symm.toLinearEquiv
  let eAlg : (P ⊗[A] R) ≃ₐ[P] B :=
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct eLin
      (fun p₁ p₂ r₁ r₂ ↦ by
        have he (p : P) (r : R) : eLin (p ⊗ₜ[A] r) = p ⊗ₜ[A, φ] (r : R'.X) :=
          extendScalarsAlgebraMapIso_inv_tmul R₀ p r
        symm
        refine (CommMonModuleEquivalenceCommAlgebra.functor_obj_mapCommMon_mul G R' _ _).trans ?_
        refine (congrArg (fun z ↦ G.map (MonObj.mul (X := R'.X))
            (Functor.LaxMonoidal.μ G R'.X R'.X z))
          (congrArg₂ (TensorProduct.tmul P (M := G.obj R'.X) (N := G.obj R'.X))
            (he p₁ r₁) (he p₂ r₂))).trans ?_
        refine (congrArg (G.map (MonObj.mul (X := R'.X)))
          (extendScalars_μ_tmul φ R'.X R'.X p₁ p₂ r₁ r₂)).trans ?_
        refine (ExtendScalars.map_tmul φ (MonObj.mul (X := R'.X)) (p₁ * p₂) _).trans ?_
        rw [CommMonModuleEquivalenceCommAlgebra.inverse_obj_mul]
        exact (congrArg (fun x : R₀ ↦ (p₁ * p₂) ⊗ₜ[A, φ] x)
          (LinearMap.mul'_apply (R := A) (a := r₁) (b := r₂))).trans (he (p₁ * p₂) (r₁ * r₂)).symm)
      (by
        symm
        refine (CommMonModuleEquivalenceCommAlgebra.functor_obj_mapCommMon_one G R').trans ?_
        refine (congrArg (G.map (MonObj.one (X := R'.X))) (extendScalars_ε_apply φ 1)).trans ?_
        refine (ExtendScalars.map_tmul φ (MonObj.one (X := R'.X)) 1 (1 : A)).trans ?_
        rw [CommMonModuleEquivalenceCommAlgebra.inverse_obj_one]
        exact (congrArg (fun x : R₀ ↦ (1 : P) ⊗ₜ[A, φ] x) (map_one (algebraMap A R))).trans
          (extendScalarsAlgebraMapIso_inv_tmul R₀ 1 1).symm)
  CommAlgCat.isoMk eAlg

-- Normalize `CommAlgCat.of` carrier projections so `@[simp]` matches after projection reduction.
/-- `extendScalarsCommAlgIso` sends `p ⊗ r` to `p ⊗ r`. -/
@[simp]
theorem extendScalarsCommAlgIso_hom_tmul (P : Type u) [CommRing P] [Algebra A P]
    (R : CommAlgCat.{u} A) (p : P) (r : R) :
    dsimp% only (extendScalarsCommAlgIso P R).hom (p ⊗ₜ[A] r) = p ⊗ₜ[A, algebraMap A P] r :=
  (Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply
    (C := CommMonModuleEquivalenceCommAlgebra.functor.obj
      ((extendScalars.{u, u, u} (algebraMap A P)).mapCommMon.obj
        (CommMonModuleEquivalenceCommAlgebra.inverse.obj R))) _ _ _ _).trans
    (extendScalarsAlgebraMapIso_inv_tmul (ModuleCat.of A R) p r)

/-- The inverse of `extendScalarsCommAlgIso` sends `p ⊗ r` to `p ⊗ r`. -/
@[simp]
theorem extendScalarsCommAlgIso_inv_tmul (P : Type u) [CommRing P] [Algebra A P]
    (R : CommAlgCat.{u} A) (p : P) (r : R) :
    dsimp% only (extendScalarsCommAlgIso P R).inv (p ⊗ₜ[A, algebraMap A P] r) = p ⊗ₜ[A] r :=
  (congrArg (extendScalarsCommAlgIso P R).inv
    (extendScalarsCommAlgIso_hom_tmul P R p r).symm).trans
    (ConcreteCategory.congr_hom (extendScalarsCommAlgIso P R).hom_inv_id (p ⊗ₜ[A] r))

end CommAlg

end ModuleCat
