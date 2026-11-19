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
For finite projective modules the map is Mathlib's equivalence `TensorProduct.dualDistribEquiv`.

For finite projective modules `L` and `M`, swapping the factors and identifying `L` with its
double dual gives the canonical isomorphism `L ⊗ M^* ≃ (M ⊗ L^*)^*`
(`TensorProduct.dualFlipEquiv`), which pairs `l ⊗ μ` with `m ⊗ θ` to `μ m * θ l`.
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

variable (R L M : Type*) [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
  [Module.Finite R L] [Projective R L] [Module.Finite R M] [Projective R M]

/-- The canonical isomorphism `L ⊗ M^* ≃ (M ⊗ L^*)^*` of finite projective modules, pairing
`l ⊗ μ` with `m ⊗ θ` to `μ m * θ l`. -/
noncomputable def dualFlipEquiv : L ⊗[R] Dual R M ≃ₗ[R] Dual R (M ⊗[R] Dual R L) :=
  TensorProduct.comm R L (Dual R M) ≪≫ₗ (evalEquiv R L).lTensor (Dual R M) ≪≫ₗ
    dualDistribEquiv R M (Dual R L)

variable {R L M}

/-- `TensorProduct.dualFlipEquiv` pairs `l ⊗ μ` with `m ⊗ θ` to `μ m * θ l`. -/
@[simp]
theorem dualFlipEquiv_tmul_tmul (l : L) (μ : Dual R M) (m : M) (θ : Dual R L) :
    dualFlipEquiv R L M (l ⊗ₜ μ) (m ⊗ₜ θ) = μ m * θ l := by
  simp [dualFlipEquiv, mul_comm]

end TensorProduct
