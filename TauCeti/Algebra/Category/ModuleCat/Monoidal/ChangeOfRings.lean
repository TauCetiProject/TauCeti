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

For commutative `A`-algebras `P` and `R`, the functor induced on commutative monoid objects by
`ModuleCat.extendScalars (algebraMap A P)` agrees with the tensor product `P`-algebra `P ⊗[A] R`
(`ModuleCat.extendScalarsCommAlgIso`).
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

section CommAlg

open scoped MonObj MonModuleEquivalenceAlgebra

attribute [local instance] MonModuleEquivalenceAlgebra.MonObj.toCommRing

variable {A : Type u} [CommRing A]

/-- Extension of scalars of a commutative `A`-algebra `R` along `algebraMap A P` via
`ModuleCat.extendScalars` on commutative monoid objects agrees with the `P`-algebra `P ⊗[A] R`. -/
noncomputable def extendScalarsCommAlgIso (P : Type u) [CommRing P] [Algebra A P]
    (R : CommAlgCat.{u} A) :
    CommAlgCat.of P (P ⊗[A] R) ≅
      CommMonModuleEquivalenceCommAlgebra.functor.obj
        ((extendScalars.{u, u, u} (algebraMap A P)).mapCommMon.obj
          (CommMonModuleEquivalenceCommAlgebra.inverse.obj R)) :=
  CommAlgCat.isoMk <|
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
      (extendScalarsAlgebraMapIso (S := P) (ModuleCat.of A R)).symm.toLinearEquiv
      (fun p₁ p₂ r₁ r₂ ↦ by
        let φ := algebraMap A P
        let G := extendScalars.{u, u, u} φ
        let R₀ := ModuleCat.of A R
        let R₀₂ : ModuleCat.{u} A := R₀ ⊗ R₀
        let M := G.mapCommMon.obj (CommMonModuleEquivalenceCommAlgebra.inverse.obj R)
        let eLin : (P ⊗[A] R) ≃ₗ[P] M.X :=
          (extendScalarsAlgebraMapIso (S := P) R₀).symm.toLinearEquiv
        have heLin (p : P) (r : R) : eLin (p ⊗ₜ[A] r) = show M.X from p ⊗ₜ[A, φ] (r : R₀) :=
          extendScalarsAlgebraMapIso_inv_tmul R₀ p r
        have hμ (q₁ q₂ : R) :
            (Functor.LaxMonoidal.μ G R₀ R₀)
                (((1 : P) ⊗ₜ[A, φ] (q₁ : R₀)) ⊗ₜ[P] ((1 : P) ⊗ₜ[A, φ] (q₂ : R₀))) =
              (1 : P) ⊗ₜ[A, φ] ((q₁ : R₀) ⊗ₜ[A] (q₂ : R₀) : ↑R₀₂) :=
          (congrArg (Functor.LaxMonoidal.μ G R₀ R₀)
            (extendScalars_δ_tmul φ R₀ R₀ q₁ q₂).symm).trans
            (ConcreteCategory.congr_hom (Functor.Monoidal.δ_μ G R₀ R₀)
              ((1 : P) ⊗ₜ[A, φ] ((q₁ : R₀) ⊗ₜ[A] (q₂ : R₀) : ↑R₀₂)))
        have h1 (q₁ q₂ : R) :
            eLin (1 ⊗ₜ[A] q₁) * eLin (1 ⊗ₜ[A] q₂) = eLin (1 ⊗ₜ[A] (q₁ * q₂)) :=
          (congrArg₂ (· * ·) (heLin 1 q₁) (heLin 1 q₂)).trans <|
            ((congrArg (G.map (ofHom (LinearMap.mul' A R))) (hμ q₁ q₂)).trans
              (ExtendScalars.map_tmul φ (ofHom (LinearMap.mul' A R)) 1
                ((q₁ : R₀) ⊗ₜ[A] (q₂ : R₀) : ↑R₀₂))).trans
              (heLin 1 (q₁ * q₂)).symm
        have hsmul (p : P) (r : R) : eLin (p ⊗ₜ[A] r) = p • eLin (1 ⊗ₜ[A] r) := by
          rw [← eLin.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change eLin ((p₁ * p₂) ⊗ₜ[A] (r₁ * r₂)) = eLin (p₁ ⊗ₜ[A] r₁) * eLin (p₂ ⊗ₜ[A] r₂)
        rw [hsmul (p₁ * p₂), hsmul p₁, hsmul p₂, ← h1, smul_mul_smul_comm])
      (by
        let φ := algebraMap A P
        let G := extendScalars.{u, u, u} φ
        let R₀ := ModuleCat.of A R
        let M := G.mapCommMon.obj (CommMonModuleEquivalenceCommAlgebra.inverse.obj R)
        let eLin : (P ⊗[A] R) ≃ₗ[P] M.X :=
          (extendScalarsAlgebraMapIso (S := P) R₀).symm.toLinearEquiv
        have hε : Functor.LaxMonoidal.ε G (1 : P) = (1 : P) ⊗ₜ[A, φ] (1 : A) :=
          let _ := φ.toAlgebra
          (ConcreteCategory.congr_hom (extendScalars_ε φ) (1 : P)).trans
            (TensorProduct.AlgebraTensorModule.rid_symm_apply A P (1 : P))
        change eLin (1 ⊗ₜ[A] 1) = 1
        exact (extendScalarsAlgebraMapIso_inv_tmul R₀ 1 1).trans <|
          ((ExtendScalars.map_tmul φ (ofHom (Algebra.linearMap A R)) 1 (1 : A)).trans
            (congrArg ((1 : P) ⊗ₜ[A, φ] ·) (map_one (algebraMap A R)))).symm.trans <|
            (congrArg (G.map (ofHom (Algebra.linearMap A R))) hε).symm)

/-- `extendScalarsCommAlgIso` sends `p ⊗ r` to `p ⊗ r`. -/
@[simp]
theorem extendScalarsCommAlgIso_hom_tmul (P : Type u) [CommRing P] [Algebra A P]
    (R : CommAlgCat.{u} A) (p : P) (r : R) :
    (extendScalarsCommAlgIso P R).hom (p ⊗ₜ[A] r) = p ⊗ₜ[A, algebraMap A P] r :=
  (Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply
    (C := ((extendScalars.{u, u, u} (algebraMap A P)).mapCommMon.obj
      (CommMonModuleEquivalenceCommAlgebra.inverse.obj R)).X) _ _ _ _).trans
    (extendScalarsAlgebraMapIso_inv_tmul (ModuleCat.of A R) p r)

/-- The inverse of `extendScalarsCommAlgIso` sends `p ⊗ r` to `p ⊗ r`. -/
theorem extendScalarsCommAlgIso_inv_tmul (P : Type u) [CommRing P] [Algebra A P]
    (R : CommAlgCat.{u} A) (p : P) (r : R) :
    (extendScalarsCommAlgIso P R).inv (p ⊗ₜ[A, algebraMap A P] r) = p ⊗ₜ[A] r :=
  (congrArg (extendScalarsCommAlgIso P R).inv
    (extendScalarsCommAlgIso_hom_tmul P R p r).symm).trans
    (ConcreteCategory.congr_hom (extendScalarsCommAlgIso P R).hom_inv_id (p ⊗ₜ[A] r))

end CommAlg

end ModuleCat
