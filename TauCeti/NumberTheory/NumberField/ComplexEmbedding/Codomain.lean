/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# `ℂ` as an algebra over a number field through a complex embedding

For a complex embedding `σ : K → ℂ`, `NumberField.ComplexEmbedding.Codomain σ` is a copy of `ℂ`
carrying the `K`-algebra (and `𝓞 K`-algebra) structure given by `σ`, identified with `ℂ` by
`NumberField.ComplexEmbedding.Codomain.equiv`. This lets the scalar extension
`Codomain σ ⊗[𝓞 K] E` of an `𝓞 K`-module `E` along `σ`, its complex fibre `E ⊗_{O_K,σ} ℂ`, be
formed for every `σ` at once. The complex fibres of `E × F` and of `E ⊗[𝓞 K] F` are the product
and the complex tensor product of those of `E` and `F` (`Codomain.prodEquiv`,
`Codomain.tensorProductEquiv`).
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

/-- The identification of `Codomain σ` with `ℂ`, as `ℂ`-algebras. -/
def equiv : Codomain σ ≃ₐ[ℂ] ℂ := AlgEquiv.refl

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

variable {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F]

/-- An integer `a` of `K` acts on the complex fibre at `σ` as the complex number `σ a`. -/
theorem tmul_smul (c : Codomain σ) (a : 𝓞 K) (x : E) :
    c ⊗ₜ[𝓞 K] (a • x) = σ a • (c ⊗ₜ[𝓞 K] x) := by
  -- Both sides are `(σ a * c) ⊗ x`: `𝓞 K` acts on `Codomain σ` through `σ`, and `ℂ` by
  -- multiplication.
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  rfl

/-- On the complex fibre at `σ`, an element of `Codomain σ` acts as the corresponding complex
number. -/
theorem smul_eq_equiv_smul (c : Codomain σ) (u : Codomain σ ⊗[𝓞 K] E) :
    c • u = equiv σ c • u :=
  -- `equiv σ` is the identity of `ℂ`, and both actions multiply the left tensor factor by `c`.
  (rfl)

/-- Elements of `Codomain σ` pass between the factors of a complex tensor product of complex
fibres, since they act as complex numbers. -/
instance compatibleSMul :
    TensorProduct.CompatibleSMul ℂ (Codomain σ) (Codomain σ ⊗[𝓞 K] E) (Codomain σ ⊗[𝓞 K] F) where
  smul_tmul c u v := by rw [smul_eq_equiv_smul, smul_eq_equiv_smul, TensorProduct.smul_tmul]

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
