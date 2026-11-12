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
sends `1` to the canonical tensor `∑ i, b i ⊗ b^i`. This element is balanced: for a linear map
`f : V → W` between finite-dimensional spaces, `(f ⊗ 1) ∘ coev_V = (1 ⊗ fᵀ) ∘ coev_W` as maps
`K → W ⊗ V*`. Equivalently, both sides correspond to `f` under the identification
`W ⊗ V* ≃ Hom(V, W)`.

This is the identity used to show that coevaluation is invariant for the antipode-twisted
contragredient action of a Hopf algebra.
-/

public section

open TensorProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Coevaluation is dinatural.** A linear map applied to the vector factor of the
coevaluation tensor of its source equals its transpose applied to the dual factor of the
coevaluation tensor of its target. -/
theorem LinearMap.rTensor_comp_coevaluation (f : V →ₗ[K] W) :
    f.rTensor (Module.Dual K V) ∘ₗ coevaluation K V =
      f.dualMap.lTensor W ∘ₗ coevaluation K W := by
  -- Compare both tensors after the injective identification `W ⊗ V* ≃ Hom(V, W)`.
  let Ψ := (TensorProduct.comm K W (Module.Dual K V)).trans (dualTensorHomEquiv K V W)
  apply LinearMap.ext_ring
  apply Ψ.injective
  ext v
  let b := Module.Basis.ofVectorSpace K V
  let c := Module.Basis.ofVectorSpace K W
  have hf : ∑ i, b.repr v i • f (b i) = f v := by
    simp_rw [← map_smul, ← map_sum, b.sum_repr]
  simpa [Ψ, coevaluation_apply_one, b, c] using hf.trans (c.sum_repr (f v)).symm
