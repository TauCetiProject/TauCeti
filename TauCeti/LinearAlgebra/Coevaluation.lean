/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Coevaluation

/-!
# Dinaturality of coevaluation

For a finite-dimensional vector space `V`, the coevaluation `coevaluation K V : K → V ⊗ V*`
sends `1` to the canonical tensor `∑ i, b i ⊗ b^i`. This element is balanced: an endomorphism
`f` of `V` may be moved across the tensor sign, where it acts on `V*` by its transpose.
Equivalently, both `(f ⊗ 1) ∘ coevaluation` and `(1 ⊗ fᵀ) ∘ coevaluation` correspond to `f`
under the identification `V ⊗ V* ≃ End V`.

This is the identity used to show that coevaluation is invariant for the antipode-twisted
contragredient action of a Hopf algebra.
-/

public section

open TensorProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Coevaluation is dinatural.** An endomorphism applied to the vector factor of the
coevaluation tensor equals its transpose applied to the dual factor. -/
theorem LinearMap.rTensor_comp_coevaluation (f : V →ₗ[K] V) :
    f.rTensor (Module.Dual K V) ∘ₗ coevaluation K V =
      f.dualMap.lTensor V ∘ₗ coevaluation K V := by
  -- Compare both tensors after the injective identification `V ⊗ V* ≃ End V`.
  let Ψ := (TensorProduct.comm K V (Module.Dual K V)).trans (dualTensorHomEquiv K V V)
  apply LinearMap.ext_ring
  apply Ψ.injective
  ext v
  let b := Module.Basis.ofVectorSpace K V
  have hf : ∑ i, b.repr v i • f (b i) = f v := by
    simp_rw [← map_smul, ← map_sum, b.sum_repr]
  simpa [Ψ, coevaluation_apply_one, b] using hf.trans (b.sum_repr (f v)).symm
