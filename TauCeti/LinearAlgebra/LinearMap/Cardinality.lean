/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.GroupTheory.Index

/-!
# Counting a module along the range and the kernel of a linear map

For a (semi)linear map `f : M →ₛₗ[τ₁₂] M₂` between additive groups, the fibres of `f` over its
range are the cosets of the kernel, so the cardinality of `M` is the product of the cardinalities
of the range and of the kernel. Both sides are `Nat.card`, which is `0` on an infinite type, so no
finiteness hypothesis is needed: the statement also says that `M` is infinite exactly when the
range or the kernel is.

This is a counting step of an exact-sequence argument, where a term is compared with the image of
the map leaving it and the image of the map entering it. The companion step, comparing the ranges
of maps intertwined by a surjection on the source and an injection on the target, does not use
linearity and is `Nat.card_range_eq_card_range_of_comp_eq`.
-/

public section

namespace LinearMap

variable {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
  [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]

/-- The cardinality of the source of a semilinear map is the product of the cardinalities of its
range and of its kernel. -/
theorem card_eq_card_range_mul_card_ker (f : M →ₛₗ[τ₁₂] M₂) :
    Nat.card M = Nat.card (range f) * Nat.card (ker f) := by
  have hker : (ker f : Set M) = f ⁻¹' {0} := Set.ext fun _ ↦ mem_ker
  rw [← AddSubgroup.card_ker_mul_card_range f.toAddMonoidHom, mul_comm]
  simp only [← SetLike.coe_sort_coe, coe_range, hker, AddMonoidHom.coe_range,
    AddMonoidHom.coe_ker, toAddMonoidHom_coe]

end LinearMap
