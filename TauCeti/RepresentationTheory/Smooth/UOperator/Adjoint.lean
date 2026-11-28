/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.UOperator.Basic

/-!
# Adjoints of the `U_t` operators for an invariant sesquilinear form

Let `ρ` be a smooth representation of a topological group `G` (with separately continuous
multiplication) on a module `V` over a commutative `⋆`-ring `A`, let `C` be a compact subgroup of
`G` of invertible pro-order, and let `B : V →ₗ⋆[A] V →ₗ[A] A` be a `ρ`-invariant sesquilinear
form (`B (ρ g x) (ρ g y) = B x y`).

Since the averaging projector `e_C` is self-adjoint for `B`
(`Representation.isSelfAdjoint_smoothAverage`) and `ρ t` has adjoint `ρ t⁻¹`, the operator
`U_t = e_C ∘ ρ(t)` satisfies:

* `Representation.isAdjointPair_uOperator`:
  `(ρ t⁻¹ ∘ₗ e_C, U_t)` is a `B.flip`-adjoint pair, i.e. `B (U_t x) y = B x (ρ t⁻¹ (e_C y))`
  for all `x, y ∈ V`.
* `Representation.apply_uOperator_apply_eq_apply_uOperator_inv_of_mem_invariants`:
  `B (U_t x) y = B x (U_{t⁻¹} y)` for all `x, y ∈ V^C`.

## References

* W. Casselman, *Introduction to the theory of admissible representations of `p`-adic reductive
  groups* (unpublished notes, 1995).
* Adapted from `src/Lib/LocalGL/SphericalChainLemma.lean` and
  `src/Lib/Adelic/Hecke/ClassSums.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

namespace Representation

variable {A G V : Type*} [CommRing A] [StarRing A] [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [AddCommGroup V] [Module A V]
  (ρ : Representation A G V) [IsSmooth ρ]
  (C : Subgroup G) [CompactSpace C] (hC : TauCeti.HasUnitProOrder A C)

/-- For a `ρ`-invariant sesquilinear form `B : V →ₗ⋆[A] V →ₗ[A] A`, `ρ t⁻¹ ∘ₗ e_C` and `U_t`
form an adjoint pair with respect to `B.flip`: `B x (ρ t⁻¹ (e_C y)) = B (U_t x) y` for all
`t ∈ G` and `x, y ∈ V`. -/
theorem isAdjointPair_uOperator (B : V →ₗ⋆[A] V →ₗ[A] A)
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y) (t : G) :
    LinearMap.IsAdjointPair B.flip B.flip
      (ρ t⁻¹ ∘ₗ smoothAverage (ρ.comp C.subtype) hC) (ρ.uOperator C hC t) := by
  intro y x
  simp only [LinearMap.flip_apply, LinearMap.comp_apply, uOperator_apply]
  have hsa := isSelfAdjoint_smoothAverage (ρ.comp C.subtype) hC B (fun c ↦ hB c.val) y (ρ t x)
  simp only [LinearMap.flip_apply] at hsa
  rw [← hsa, ← hB t⁻¹ (ρ t x), inv_self_apply]

/-- On `C`-invariants `V^C`, the adjoint of `U_t` with respect to a `ρ`-invariant sesquilinear form
`B` is `U_{t⁻¹}`: `B (U_t x) y = B x (U_{t⁻¹} y)`. -/
theorem apply_uOperator_apply_eq_apply_uOperator_inv_of_mem_invariants (B : V →ₗ⋆[A] V →ₗ[A] A)
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y) (t : G) {x y : V}
    (hx : x ∈ invariants (ρ.comp C.subtype)) (hy : y ∈ invariants (ρ.comp C.subtype)) :
    B (ρ.uOperator C hC t x) y = B x (ρ.uOperator C hC t⁻¹ y) := by
  have h1 := (isAdjointPair_uOperator ρ C hC B hB t y x).symm
  have hsa := isSelfAdjoint_smoothAverage (ρ.comp C.subtype) hC B (fun c ↦ hB c.val) (ρ t⁻¹ y) x
  simp only [LinearMap.flip_apply, LinearMap.comp_apply] at h1 hsa
  rw [h1, smoothAverage_apply_of_mem_invariants (ρ.comp C.subtype) hC hy, uOperator_apply,
    hsa, smoothAverage_apply_of_mem_invariants (ρ.comp C.subtype) hC hx]

end Representation
