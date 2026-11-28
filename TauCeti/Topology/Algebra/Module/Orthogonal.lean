/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Topology.Separation.Basic

/-!
# Topological properties of orthogonal complements for sesquilinear pairings

For any sesquilinear pairing `B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M` into a `T₁` topological module `M`,
the orthogonal complement `S.orthogonalBilin B` of a submodule `S : Submodule R₁ M₁` is closed
whenever `B x` is continuous for every `x ∈ S`.

## Main results

* `Submodule.isClosed_orthogonalBilin`: the orthogonal complement `S.orthogonalBilin B` is closed
  when `B x` is continuous for all `x ∈ S` and `M` is `T₁`.
-/

public section

namespace Submodule

variable {R R₁ R₂ M M₁ M₂ : Type*}
  [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]
  [AddCommMonoid M] [Module R M] [TopologicalSpace M] [T1Space M]
  [AddCommMonoid M₁] [Module R₁ M₁]
  [AddCommMonoid M₂] [Module R₂ M₂] [TopologicalSpace M₂]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R}

/-- The orthogonal complement of a submodule with respect to a sesquilinear pairing that is
continuous in the second variable on each element of the submodule is closed, provided the codomain
is `T₁`. -/
theorem isClosed_orthogonalBilin (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (S : Submodule R₁ M₁)
    (hB : ∀ x ∈ S, Continuous (B x)) :
    IsClosed (S.orthogonalBilin B : Set M₂) := by
  have heq : (S.orthogonalBilin B : Set M₂) = ⋂ x ∈ S, {y : M₂ | B x y = 0} := by
    ext y
    simp
  rw [heq]
  exact isClosed_biInter fun x hx ↦ isClosed_singleton.preimage (hB x hx)

end Submodule
