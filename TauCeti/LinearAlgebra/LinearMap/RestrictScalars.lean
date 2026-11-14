/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.LinearAlgebra.Quotient.Basic
import TauCeti.LinearAlgebra.LinearMap.Ker
import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Kernels and cokernels under restriction of scalars

For a tower of scalars `R → S` and an `S`-linear map `f`, the kernel and cokernel of `f`, with
their `R`-module structures, are those of the underlying `R`-linear map
(`LinearMap.kerRestrictScalarsEquiv`, `LinearMap.cokerRestrictScalarsEquiv`). A commuting square
`f' ∘ e₁ = e₂ ∘ f` of `R`-linear isomorphisms between `S`-modules therefore induces `R`-linear
isomorphisms of the `S`-kernels and `S`-cokernels (`LinearMap.kerCongrOfComp`,
`LinearMap.cokerCongrOfComp`). If `e₁` and `e₂` send `a • x` to `s • e x`, so do the induced
isomorphisms (`LinearMap.kerCongrOfComp_smul`, `LinearMap.cokerCongrOfComp_smul`). For the tower
`ℝ → ℂ` with `a = I` and `s = ±I`, this says the induced isomorphisms are complex linear or
conjugate-linear.
-/

public section

noncomputable section

namespace LinearMap

section Ker

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[S] N)

/-- The kernel of an `S`-linear map, with its `R`-module structure, is the kernel of the
underlying `R`-linear map. -/
def kerRestrictScalarsEquiv : ker f ≃ₗ[R] ker (f.restrictScalars R) :=
  ((ker f).restrictScalarsEquiv R).symm.restrictScalars R

theorem coe_kerRestrictScalarsEquiv_apply (x : ker f) :
    (f.kerRestrictScalarsEquiv R x : M) = x :=
  (rfl)

theorem coe_kerRestrictScalarsEquiv_symm_apply (x : ker (f.restrictScalars R)) :
    ((f.kerRestrictScalarsEquiv R).symm x : M) = x :=
  (rfl)

variable {R} {M' N' : Type*} [AddCommMonoid M'] [Module R M'] [Module S M']
  [IsScalarTower R S M'] [AddCommMonoid N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
  {f' : M' →ₗ[S] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
  (h : f'.restrictScalars R ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f.restrictScalars R)

/-- The `R`-linear isomorphism of `S`-kernels induced by a commuting square `f' ∘ e₁ = e₂ ∘ f`
of `R`-linear isomorphisms: the restriction of `e₁`. -/
def kerCongrOfComp : ker f ≃ₗ[R] ker f' :=
  (f.kerRestrictScalarsEquiv R).trans ((e₁.ofSubmodules _ _
    ((f.restrictScalars R).map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)).trans
      (f'.kerRestrictScalarsEquiv R).symm)

@[simp]
theorem coe_kerCongrOfComp_apply (x : ker f) : (kerCongrOfComp f e₁ e₂ h x : M') = e₁ x :=
  (rfl)

@[simp]
theorem coe_kerCongrOfComp_symm_apply (x : ker f') :
    ((kerCongrOfComp f e₁ e₂ h).symm x : M) = e₁.symm x := by
  obtain ⟨x, rfl⟩ := (kerCongrOfComp f e₁ e₂ h).surjective x
  simp

/-- If `e₁` sends `a • x` to `s • e₁ x`, so does the induced isomorphism of kernels. -/
theorem kerCongrOfComp_smul {a s : S} (he₁ : ∀ x, e₁ (a • x) = s • e₁ x) (x : ker f) :
    kerCongrOfComp f e₁ e₂ h (a • x) = s • kerCongrOfComp f e₁ e₂ h x :=
  Subtype.ext (by simp [he₁])

end Ker

section Coker

variable (R : Type*) {S M N : Type*} [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[S] N)

/-- The cokernel of an `S`-linear map, with its `R`-module structure, is the cokernel of the
underlying `R`-linear map. -/
def cokerRestrictScalarsEquiv : (N ⧸ range (f.restrictScalars R)) ≃ₗ[R] N ⧸ range f :=
  (Submodule.quotEquivOfEq _ _ (range_restrictScalars f)).trans
    (Submodule.Quotient.restrictScalarsEquiv R (range f))

@[simp]
theorem cokerRestrictScalarsEquiv_mk (y : N) :
    f.cokerRestrictScalarsEquiv R (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

@[simp]
theorem cokerRestrictScalarsEquiv_symm_mk (y : N) :
    (f.cokerRestrictScalarsEquiv R).symm (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

variable {R} {M' N' : Type*} [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M'] [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
  {f' : M' →ₗ[S] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
  (h : f'.restrictScalars R ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f.restrictScalars R)

/-- The `R`-linear isomorphism of `S`-cokernels induced by a commuting square
`f' ∘ e₁ = e₂ ∘ f` of `R`-linear isomorphisms: the map of quotients induced by `e₂`. -/
def cokerCongrOfComp : (N ⧸ range f) ≃ₗ[R] N' ⧸ range f' :=
  (f.cokerRestrictScalarsEquiv R).symm.trans ((Submodule.Quotient.equiv _ _ e₂
    ((f.restrictScalars R).map_range_eq_range_of_comp_eq e₁.surjective h)).trans
      (f'.cokerRestrictScalarsEquiv R))

@[simp]
theorem cokerCongrOfComp_mk (y : N) :
    cokerCongrOfComp f e₁ e₂ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e₂ y) :=
  (rfl)

@[simp]
theorem cokerCongrOfComp_symm_mk (y : N') :
    (cokerCongrOfComp f e₁ e₂ h).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (e₂.symm y) := by
  rw [LinearEquiv.symm_apply_eq, cokerCongrOfComp_mk, LinearEquiv.apply_symm_apply]

/-- If `e₂` sends `a • y` to `s • e₂ y`, so does the induced isomorphism of cokernels. -/
theorem cokerCongrOfComp_smul {a s : S} (he₂ : ∀ y, e₂ (a • y) = s • e₂ y)
    (y : N ⧸ range f) :
    cokerCongrOfComp f e₁ e₂ h (a • y) = s • cokerCongrOfComp f e₁ e₂ h y := by
  induction y using Submodule.Quotient.induction_on with
  | H y => rw [← Submodule.Quotient.mk_smul, cokerCongrOfComp_mk, cokerCongrOfComp_mk, he₂,
      Submodule.Quotient.mk_smul]

end Coker

end LinearMap
