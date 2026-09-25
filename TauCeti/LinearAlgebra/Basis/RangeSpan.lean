/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spans of the images of a basis

A linear map has the same scalar-extended image span when evaluated on a basis as when evaluated
on its entire domain.
-/

public section

namespace Module.Basis

/-- Over a scalar extension, the image of a linear map is spanned by its values on any basis. -/
theorem span_range_eq_span_range_basis
    {R S M N ι : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    (b : Module.Basis ι R M) (f : M →ₗ[R] N) :
    Submodule.span S (Set.range f) = Submodule.span S (Set.range (f ∘ b)) := by
  rw [← LinearMap.coe_range, LinearMap.range_eq_map, ← b.span_eq,
    LinearMap.map_span, Submodule.span_span_of_tower]
  congr 1
  rw [Set.range_comp]

end Module.Basis
