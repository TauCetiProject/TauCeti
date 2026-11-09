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
