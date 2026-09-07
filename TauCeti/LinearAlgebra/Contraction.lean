/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# The contraction equivalence is the contraction map

For a finite projective module `M` over a commutative semiring `R`, the contraction map
`dualTensorHom R M N : Module.Dual R M ⊗[R] N →ₗ[R] (M →ₗ[R] N)`, which sends a pure tensor
`φ ⊗ₜ y` to `x ↦ φ x • y`, is an isomorphism; Mathlib packages the isomorphism as
`dualTensorHomEquiv R M N`. This file identifies the equivalence with the contraction map.

The identification is what lets a structure defined on `Module.Dual R M ⊗[R] N` be transported to
`M →ₗ[R] N` and then computed on pure tensors: a statement about `dualTensorHomEquiv` becomes one
about `dualTensorHom`, which `dualTensorHom_apply` evaluates. The Hodge structure on an internal
hom is obtained this way. Mathlib states the corresponding identification only for the
basis-dependent companion `dualTensorHomEquivOfBasis`.

## Main results

* `TauCeti.dualTensorHomEquiv_apply`: the forward map of the contraction equivalence is the
  contraction `dualTensorHom`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Module.Finite R M] [Module.Projective R M]

/-- The forward map of the contraction equivalence `M^* ⊗ N ≃ₗ[R] (M →ₗ[R] N)` is the contraction
`dualTensorHom` itself. -/
theorem dualTensorHomEquiv_apply (z : Module.Dual R M ⊗[R] N) :
    dualTensorHomEquiv R M N z = dualTensorHom R M N z :=
  (rfl)

end TauCeti
