/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# `ℂ` as an algebra over a number field through a complex embedding

For a complex embedding `σ : K → ℂ`, `NumberField.ComplexEmbedding.Codomain σ` is a copy of `ℂ`
carrying the `K`-algebra (and `𝓞 K`-algebra) structure given by `σ`, identified with `ℂ` by
`NumberField.ComplexEmbedding.Codomain.equiv`. This lets the scalar extension
`Codomain σ ⊗[𝓞 K] E` of an `𝓞 K`-module `E` along `σ`, its complex fibre `E ⊗_{O_K,σ} ℂ`, be
formed for every `σ` at once. When `s` generates `E`, the complex fibre is the line spanned by
`1 ⊗ s` (`NumberField.ComplexEmbedding.Codomain.exists_eq_smul_one_tmul`). The complex fibres
of `E × F` and of `E ⊗[𝓞 K] F` are the product and the complex tensor product of those of `E` and
`F` (`Codomain.prodEquiv`, `Codomain.tensorProductEquiv`).

Complex conjugation is `𝓞 K`-linear from `Codomain σ` to `Codomain (conjugate σ)`
(`NumberField.ComplexEmbedding.Codomain.conj`), and `Codomain σ` is flat over `𝓞 K` when `K` is a
number field, so the complex fibres of injective maps are injective
(`NumberField.ComplexEmbedding.Codomain.baseChange_injective`).
-/

public noncomputable section

open scoped TensorProduct

namespace NumberField.ComplexEmbedding

variable {K : Type*} [Field K]

/-- The field `ℂ`, regarded as an algebra over `K` (and over its ring of integers) through the
complex embedding `σ`. The complex fibre of an `𝓞 K`-module `E` at `σ` is the scalar extension
`Codomain σ ⊗[𝓞 K] E`, a complex vector space. -/
@[expose] def Codomain (_σ : K →+* ℂ) : Type := ℂ

namespace Codomain

variable (σ : K →+* ℂ)

instance : Field (Codomain σ) := inferInstanceAs (Field ℂ)

instance : Algebra ℂ (Codomain σ) := inferInstanceAs (Algebra ℂ ℂ)

instance : Algebra K (Codomain σ) := σ.toAlgebra

instance : Algebra (𝓞 K) (Codomain σ) := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra

instance : IsScalarTower (𝓞 K) K (Codomain σ) := .of_algebraMap_eq fun _ ↦ rfl

instance : SMulCommClass (𝓞 K) ℂ (Codomain σ) where
  smul_comm a c z := mul_left_comm (G := ℂ) (σ (algebraMap (𝓞 K) K a)) c z

instance : FaithfulSMul (𝓞 K) (Codomain σ) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (σ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K))

/-- The identification of `Codomain σ` with `ℂ`, as `ℂ`-algebras. -/
def equiv : Codomain σ ≃ₐ[ℂ] ℂ := AlgEquiv.refl

instance : Module.Finite ℂ (Codomain σ) := .equiv (equiv σ).symm.toLinearEquiv

@[simp]
theorem algebraMap_equiv (c : Codomain σ) : algebraMap ℂ (Codomain σ) (equiv σ c) = c := (rfl)

@[simp]
theorem equiv_algebraMap (x : K) : equiv σ (algebraMap K (Codomain σ) x) = σ x := (rfl)

@[simp]
theorem equiv_algebraMap_ringOfIntegers (x : 𝓞 K) :
    equiv σ (algebraMap (𝓞 K) (Codomain σ) x) = σ x := (rfl)

/-- In the complex fibre `Codomain σ ⊗[𝓞 K] E`, a pure tensor `c ⊗ x` is the complex multiple
`c • (1 ⊗ x)`. -/
theorem tmul_eq_smul {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] (c : Codomain σ) (x : E) :
    c ⊗ₜ[𝓞 K] x = equiv σ c • (1 ⊗ₜ[𝓞 K] x : Codomain σ ⊗[𝓞 K] E) := by
  -- `equiv σ` is the identity of `ℂ`, and `ℂ` acts on `Codomain σ` by multiplication.
  rw [TensorProduct.smul_tmul']
  exact congrArg (· ⊗ₜ[𝓞 K] x) (mul_one (M := ℂ) c).symm

/-- Complex conjugation `ℂ → ℂ` from `Codomain σ` to `Codomain (conjugate σ)`; it is `𝓞 K`-linear
since `conj (σ a * z) = (conj σ) a * conj z`. -/
def conj : Codomain σ →ₗ[𝓞 K] Codomain (conjugate σ) where
  toFun z := (equiv (conjugate σ)).symm (starRingEnd ℂ (equiv σ z))
  map_add' z w := by simp only [map_add]
  map_smul' a z := by
    apply (equiv (conjugate σ)).injective
    simp only [AlgEquiv.apply_symm_apply, Algebra.smul_def, map_mul, RingHom.id_apply,
      equiv_algebraMap_ringOfIntegers, conjugate_coe_eq]

/-- `Codomain.conj σ` is complex conjugation. -/
@[simp]
theorem equiv_conj (z : Codomain σ) :
    equiv (conjugate σ) (conj σ z) = starRingEnd ℂ (equiv σ z) :=
  AlgEquiv.apply_symm_apply _ _

@[simp]
theorem conj_one : conj σ 1 = 1 := by
  apply (equiv (conjugate σ)).injective
  simp

/-- The complex fibre `f_σ` of an injective `𝓞 K`-linear map is injective, since `ℂ` is flat over
`𝓞 K`. -/
theorem baseChange_injective [NumberField K] {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [AddCommGroup F] [Module (𝓞 K) F] {f : F →ₗ[𝓞 K] E} (hf : Function.Injective f) :
    Function.Injective (f.baseChange (Codomain σ)) := by
  have : Module.Flat (𝓞 K) (Codomain σ) := Module.Flat.trans (𝓞 K) K (Codomain σ)
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- A nonzero element of a flat `𝓞 K`-module stays nonzero in the complex fibre at `σ`, since
`𝓞 K → ℂ` is injective. -/
theorem one_tmul_ne_zero {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Flat (𝓞 K) E]
    {x : E} (hx : x ≠ 0) : (1 : Codomain σ) ⊗ₜ[𝓞 K] x ≠ 0 := fun h =>
  hx (Module.Flat.tensorProduct_mk_injective (𝓞 K) E (Codomain σ) (by simpa using h))

variable {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F]

/-- An integer `a` of `K` acts on the complex fibre at `σ` as the complex number `σ a`. -/
theorem tmul_smul (c : Codomain σ) (a : 𝓞 K) (x : E) :
    c ⊗ₜ[𝓞 K] (a • x) = σ a • (c ⊗ₜ[𝓞 K] x) := by
  -- Both sides are `(σ a * c) ⊗ x`: `𝓞 K` acts on `Codomain σ` through `σ`, and `ℂ` by
  -- multiplication.
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  rfl

/-- If `s` generates `E`, the complex fibre at `σ` is the line spanned by `1 ⊗ s`: every vector is
a complex multiple of `1 ⊗ s`. -/
theorem exists_eq_smul_one_tmul {s : E} (hs : Submodule.span (𝓞 K) {s} = ⊤)
    (u : Codomain σ ⊗[𝓞 K] E) : ∃ c : ℂ, u = c • (1 ⊗ₜ[𝓞 K] s) := by
  have hu : u ∈ (Submodule.span (𝓞 K) {s}).baseChange (Codomain σ) := by
    rw [hs, Submodule.baseChange_top]
    exact Submodule.mem_top
  rw [Submodule.baseChange_span, Set.image_singleton, TensorProduct.mk_apply] at hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
  exact ⟨equiv σ c, by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, tmul_eq_smul]⟩

/-- Elements of `Codomain σ` pass between the factors of a complex tensor product of complex
fibres, since they act as complex numbers. -/
instance compatibleSMul :
    TensorProduct.CompatibleSMul ℂ (Codomain σ) (Codomain σ ⊗[𝓞 K] E) (Codomain σ ⊗[𝓞 K] F) :=
  .of_algebraMap_surjective _ _ fun c ↦ ⟨c, rfl⟩

variable (E F)

/-- The complex fibre of `E × F` at `σ` is the product of the complex fibres of `E` and `F`. -/
def prodEquiv :
    Codomain σ ⊗[𝓞 K] (E × F) ≃ₗ[ℂ] (Codomain σ ⊗[𝓞 K] E) × (Codomain σ ⊗[𝓞 K] F) :=
  (TensorProduct.prodRight (𝓞 K) (Codomain σ) (Codomain σ) E F).restrictScalars ℂ

/-- The complex fibre of `E ⊗[𝓞 K] F` at `σ` is the complex tensor product of the complex fibres
of `E` and `F`. -/
def tensorProductEquiv :
    Codomain σ ⊗[𝓞 K] (E ⊗[𝓞 K] F) ≃ₗ[ℂ] (Codomain σ ⊗[𝓞 K] E) ⊗[ℂ] (Codomain σ ⊗[𝓞 K] F) :=
  ((TensorProduct.AlgebraTensorModule.distribBaseChange (𝓞 K) (Codomain σ) E F).restrictScalars
    ℂ).trans (TensorProduct.equivOfCompatibleSMul ℂ (Codomain σ) ℂ _ _)

variable {E F}

@[simp]
theorem prodEquiv_tmul (c : Codomain σ) (x : E × F) :
    prodEquiv σ E F (c ⊗ₜ x) = (c ⊗ₜ x.1, c ⊗ₜ x.2) :=
  (rfl)

@[simp]
theorem tensorProductEquiv_tmul (c : Codomain σ) (x : E) (y : F) :
    tensorProductEquiv σ E F (c ⊗ₜ (x ⊗ₜ y)) = (c ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y) :=
  (rfl)

end Codomain

end NumberField.ComplexEmbedding
