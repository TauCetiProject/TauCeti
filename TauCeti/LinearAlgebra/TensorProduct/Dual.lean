/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# Naturality of tensor duality

The canonical map `E* ⊗ F* → (E ⊗ F)*` commutes with precomposition in both variables.
In particular it transports the tensor product of transposed endomorphisms to the transpose
of their tensor product. This applies to grading operators as well as algebra actions.
For finite projective modules the map is Mathlib's equivalence `TensorProduct.dualDistribEquiv`,
and for linear isomorphisms `α` and `β` naturality reads: pairing with dual factors transported
by `α⁻¹` and `β⁻¹` is pairing after `(α ⊗ β)⁻¹`
(`TensorProduct.dualDistribEquiv_map_symm_dualMap_apply`).
-/

public section

namespace LinearMap

open Module TensorProduct

variable {R E F E' F' : Type*} [CommSemiring R]
  [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]
  [AddCommMonoid E'] [Module R E'] [AddCommMonoid F'] [Module R F']

/-- Tensor duality is contravariantly natural in both module variables. No finiteness or
projectivity is needed for the canonical map to intertwine precomposition. -/
theorem dualDistrib_comp_map_dualMap (f : E →ₗ[R] E') (g : F →ₗ[R] F') :
    dualDistrib R E F ∘ₗ map f.dualMap g.dualMap =
      (map f g).dualMap ∘ₗ dualDistrib R E' F' := by
  ext φ ψ e w
  simp

end LinearMap

namespace TensorProduct

open Module

variable {R E F E' F' : Type*} [CommSemiring R]
  [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]
  [AddCommMonoid E'] [Module R E'] [AddCommMonoid F'] [Module R F']
  [Module.Finite R E] [Projective R E] [Module.Finite R F] [Projective R F]
  [Module.Finite R E'] [Projective R E'] [Module.Finite R F'] [Projective R F']

/-- Pairing through `dualDistribEquiv` with dual factors transported by the inverses of linear
isomorphisms `α` and `β` is pairing after the inverse of `α ⊗ β`. This is the pointwise form of
`LinearMap.dualDistrib_comp_map_dualMap` for `α⁻¹` and `β⁻¹`. -/
theorem dualDistribEquiv_map_symm_dualMap_apply (α : E ≃ₗ[R] E') (β : F ≃ₗ[R] F')
    (ψ : Dual R E ⊗[R] Dual R F) (t : E' ⊗[R] F') :
    dualDistribEquiv R E' F' (map α.symm.dualMap.toLinearMap β.symm.dualMap.toLinearMap ψ) t =
      dualDistribEquiv R E F ψ ((congr α β).symm.toLinearMap t) := by
  have hα : α.symm.dualMap.toLinearMap = α.symm.toLinearMap.dualMap := by ext; simp
  have hβ : β.symm.dualMap.toLinearMap = β.symm.toLinearMap.dualMap := by ext; simp
  simpa only [← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe, LinearMap.comp_apply,
    LinearMap.dualMap_apply, congr_symm, toLinearMap_congr, hα, hβ] using
    congr($(LinearMap.dualDistrib_comp_map_dualMap α.symm.toLinearMap β.symm.toLinearMap) ψ t)

end TensorProduct
