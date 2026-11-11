/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.LinearAlgebra.LinearMap.Ker
import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Kernels and cokernels of complex-linear maps as real modules

The kernel and cokernel of a complex-linear map `f`, with their real structures, are those of the
underlying real-linear map (`LinearMap.kerRestrictScalarsEquiv`,
`LinearMap.cokerRestrictScalarsEquiv`). A commuting square `f' ∘ e₁ = e₂ ∘ f` of real-linear
isomorphisms between complex modules therefore induces real-linear isomorphisms of the complex
kernels and cokernels (`LinearMap.kerCongrOfComp`, `LinearMap.cokerCongrOfComp`). If `e₁` and
`e₂` multiply by a scalar `s` whenever `I` acts, so do the induced isomorphisms
(`LinearMap.kerCongrOfComp_I_smul`, `LinearMap.cokerCongrOfComp_I_smul`); for `s = I` they are
complex linear and for `s = -I` conjugate-linear.
-/

public section

noncomputable section

open Complex

namespace LinearMap

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (f : M →ₗ[ℂ] N)

/-- The kernel of a complex-linear map, with its real structure, is the kernel of the underlying
real-linear map. -/
def kerRestrictScalarsEquiv : ker f ≃ₗ[ℝ] ker (f.restrictScalars ℝ) :=
  ((ker f).restrictScalarsEquiv ℝ).symm.restrictScalars ℝ

theorem coe_kerRestrictScalarsEquiv_apply (x : ker f) :
    (f.kerRestrictScalarsEquiv x : M) = x :=
  (rfl)

theorem coe_kerRestrictScalarsEquiv_symm_apply (x : ker (f.restrictScalars ℝ)) :
    (f.kerRestrictScalarsEquiv.symm x : M) = x :=
  (rfl)

/-- The cokernel of a complex-linear map, with its real structure, is the cokernel of the
underlying real-linear map. -/
def cokerRestrictScalarsEquiv : (N ⧸ range (f.restrictScalars ℝ)) ≃ₗ[ℝ] N ⧸ range f :=
  (Submodule.quotEquivOfEq _ _ (range_restrictScalars f)).trans
    (Submodule.Quotient.restrictScalarsEquiv ℝ (range f))

@[simp]
theorem cokerRestrictScalarsEquiv_mk (y : N) :
    f.cokerRestrictScalarsEquiv (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

@[simp]
theorem cokerRestrictScalarsEquiv_symm_mk (y : N) :
    f.cokerRestrictScalarsEquiv.symm (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

variable {M' N' : Type*} [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N'] {f' : M' →ₗ[ℂ] N'}
  (e₁ : M ≃ₗ[ℝ] M') (e₂ : N ≃ₗ[ℝ] N')
  (h : f'.restrictScalars ℝ ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f.restrictScalars ℝ)

/-- The real-linear isomorphism of complex kernels induced by a commuting square
`f' ∘ e₁ = e₂ ∘ f` of real-linear isomorphisms: the restriction of `e₁`. -/
def kerCongrOfComp : ker f ≃ₗ[ℝ] ker f' :=
  f.kerRestrictScalarsEquiv.trans ((e₁.ofSubmodules _ _
    ((f.restrictScalars ℝ).map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)).trans
      f'.kerRestrictScalarsEquiv.symm)

@[simp]
theorem coe_kerCongrOfComp_apply (x : ker f) : (kerCongrOfComp f e₁ e₂ h x : M') = e₁ x :=
  (rfl)

@[simp]
theorem coe_kerCongrOfComp_symm_apply (x : ker f') :
    ((kerCongrOfComp f e₁ e₂ h).symm x : M) = e₁.symm x := by
  obtain ⟨x, rfl⟩ := (kerCongrOfComp f e₁ e₂ h).surjective x
  simp

/-- If `e₁` multiplies by `s` whenever `I` acts, so does the induced isomorphism of kernels. -/
theorem kerCongrOfComp_I_smul {s : ℂ} (he₁ : ∀ x, e₁ (I • x) = s • e₁ x) (x : ker f) :
    kerCongrOfComp f e₁ e₂ h (I • x) = s • kerCongrOfComp f e₁ e₂ h x :=
  Subtype.ext (by simp [he₁])

/-- The real-linear isomorphism of complex cokernels induced by a commuting square
`f' ∘ e₁ = e₂ ∘ f` of real-linear isomorphisms: the map of quotients induced by `e₂`. -/
def cokerCongrOfComp : (N ⧸ range f) ≃ₗ[ℝ] N' ⧸ range f' :=
  f.cokerRestrictScalarsEquiv.symm.trans ((Submodule.Quotient.equiv _ _ e₂
    ((f.restrictScalars ℝ).map_range_eq_range_of_comp_eq e₁.surjective h)).trans
      f'.cokerRestrictScalarsEquiv)

@[simp]
theorem cokerCongrOfComp_mk (y : N) :
    cokerCongrOfComp f e₁ e₂ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e₂ y) :=
  (rfl)

@[simp]
theorem cokerCongrOfComp_symm_mk (y : N') :
    (cokerCongrOfComp f e₁ e₂ h).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (e₂.symm y) := by
  rw [LinearEquiv.symm_apply_eq, cokerCongrOfComp_mk, LinearEquiv.apply_symm_apply]

/-- If `e₂` multiplies by `s` whenever `I` acts, so does the induced isomorphism of cokernels. -/
theorem cokerCongrOfComp_I_smul {s : ℂ} (he₂ : ∀ y, e₂ (I • y) = s • e₂ y)
    (y : N ⧸ range f) :
    cokerCongrOfComp f e₁ e₂ h (I • y) = s • cokerCongrOfComp f e₁ e₂ h y := by
  induction y using Submodule.Quotient.induction_on with
  | H y => rw [← Submodule.Quotient.mk_smul, cokerCongrOfComp_mk, cokerCongrOfComp_mk, he₂,
      Submodule.Quotient.mk_smul]

end LinearMap
