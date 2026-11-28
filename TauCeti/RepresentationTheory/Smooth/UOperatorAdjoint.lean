/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.UOperator

/-!
# Adjoints of the `U_t` operators for an invariant sesquilinear form

Let `ρ` be a smooth representation of a topological group `G` (with separately continuous
multiplication) on a module `V` over a commutative `⋆`-ring `A`, let `C` be a compact subgroup of
`G` of invertible pro-order, and let `B : V →ₗ⋆[A] V →ₗ[A] A` be a `ρ`-invariant sesquilinear
form (`B (ρ g x) (ρ g y) = B x y`).

Since the averaging projector `e_C` is self-adjoint for `B`
(`Representation.isSelfAdjoint_smoothAverage`) and `ρ t` has adjoint `ρ t⁻¹`, the operator
`U_t = e_C ∘ ρ(t)` satisfies:

* `Representation.sesquilinear_uOperator_left`:
  `B (U_t x) y = B x (ρ t⁻¹ (e_C y))` for all `x, y ∈ V`.
* `Representation.sesquilinear_uOperator_left_of_mem_invariants`:
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

/-- For a `ρ`-invariant sesquilinear form `B : V →ₗ⋆[A] V →ₗ[A] A`,
`B (U_t x) y = B x (ρ t⁻¹ (e_C y))` for all `t ∈ G` and `x, y ∈ V`. -/
theorem sesquilinear_uOperator_left (B : V →ₗ⋆[A] V →ₗ[A] A)
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y) (t : G) (x y : V) :
    B (ρ.uOperator C hC t x) y = B x (ρ t⁻¹ (smoothAverage (ρ.comp C.subtype) hC y)) := by
  have hC_inv : ∀ (c : C) x y, B ((ρ.comp C.subtype) c x) ((ρ.comp C.subtype) c y) = B x y :=
    fun c x y ↦ hB c.val x y
  have hsa := isSelfAdjoint_smoothAverage (ρ.comp C.subtype) hC B hC_inv y (ρ t x)
  rw [LinearMap.flip_apply, LinearMap.flip_apply] at hsa
  rw [uOperator_apply, ← hsa, ← hB t⁻¹ (ρ t x), ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self]

/-- On `C`-invariants `V^C`, the adjoint of `U_t` with respect to a `ρ`-invariant sesquilinear form
`B` is `U_{t⁻¹}`: `B (U_t x) y = B x (U_{t⁻¹} y)`. -/
theorem sesquilinear_uOperator_left_of_mem_invariants (B : V →ₗ⋆[A] V →ₗ[A] A)
    (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y) (t : G) {x y : V}
    (hx : x ∈ invariants (ρ.comp C.subtype)) (hy : y ∈ invariants (ρ.comp C.subtype)) :
    B (ρ.uOperator C hC t x) y = B x (ρ.uOperator C hC t⁻¹ y) := by
  have hC_inv : ∀ (c : C) u w, B ((ρ.comp C.subtype) c u) ((ρ.comp C.subtype) c w) = B u w :=
    fun c u w ↦ hB c.val u w
  have hsa := isSelfAdjoint_smoothAverage (ρ.comp C.subtype) hC B hC_inv (ρ t⁻¹ y) x
  rw [LinearMap.flip_apply, LinearMap.flip_apply] at hsa
  rw [sesquilinear_uOperator_left ρ C hC B hB t x y,
    smoothAverage_apply_of_mem_invariants (ρ.comp C.subtype) hC hy,
    uOperator_apply, hsa,
    smoothAverage_apply_of_mem_invariants (ρ.comp C.subtype) hC hx]

end Representation
