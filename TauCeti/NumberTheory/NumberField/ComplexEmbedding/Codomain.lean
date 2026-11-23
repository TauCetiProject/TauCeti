/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# `ℂ` as an algebra over a number field through a complex embedding

For a complex embedding `σ : K → ℂ`, `NumberField.ComplexEmbedding.Codomain σ` is a copy of `ℂ`
carrying the `K`-algebra (and `𝓞 K`-algebra) structure given by `σ`, identified with `ℂ` by
`NumberField.ComplexEmbedding.Codomain.equiv`. This lets the scalar extension
`Codomain σ ⊗[𝓞 K] E` of an `𝓞 K`-module `E` along `σ`, its complex fibre `E ⊗_{O_K,σ} ℂ`, be
formed for every `σ` at once.
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

end Codomain

end NumberField.ComplexEmbedding
