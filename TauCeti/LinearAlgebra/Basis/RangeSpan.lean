/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Spans of the images of a basis

A semilinear map has the same scalar-extended image span when evaluated on a basis as when evaluated
on its entire domain.
-/

public section

namespace Module.Basis

/-- Over a scalar extension, the image of a semilinear map is spanned by its values on any
basis. The ring homomorphism defining semilinearity need not be surjective. -/
theorem span_range_eq_span_range_basis
    {R R' S M N ι : Type*} [Semiring R] [Semiring R'] [Semiring S] [SMul R' S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R' N]
    [Module S N] [IsScalarTower R' S N] {σ : R →+* R'}
    (b : Module.Basis ι R M) (f : M →ₛₗ[σ] N) :
    Submodule.span S (Set.range f) = Submodule.span S (Set.range (f ∘ b)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply (Submodule.image_span_subset f (Set.range b)
      ((Submodule.span S (Set.range (f ∘ b))).restrictScalars R')).mpr ?_ ⟨x, by
        simp [b.span_eq], rfl⟩
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  · exact Submodule.span_mono (Set.range_comp_subset_range _ _)

end Module.Basis
