/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Short-complex variants of the three and four lemmas

This file complements `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four` with isomorphism
variants directly for morphisms of `CategoryTheory.ShortComplex` in an abelian category.

In contrast to `CategoryTheory.Abelian.isIso_of_epi_of_isIso` (which is stated for
`CategoryTheory.ComposableArrows` and assumes exactness of both rows),
`CategoryTheory.ShortComplex.isIso_τ₃_of_epi_of_isIso` deduces `IsIso φ.τ₃` from
`CategoryTheory.ShortComplex.mono_of_epi_of_epi_of_mono` without requiring exactness of the
source short complex `R₁`.
-/

public section

namespace CategoryTheory.ShortComplex

open CategoryTheory Limits

/-- In a morphism `φ : R₁ ⟶ R₂` of short complexes in an abelian category with `R₁.g` and `R₂.g`
epimorphisms and `R₂` exact, if `φ.τ₁` is an epimorphism and `φ.τ₂` is an isomorphism, then
`φ.τ₃` is an isomorphism. -/
theorem isIso_τ₃_of_epi_of_isIso {C : Type*} [Category* C] [Abelian C]
    {R₁ R₂ : ShortComplex C} (φ : R₁ ⟶ R₂) (hR₂ : R₂.Exact)
    [Epi R₁.g] [Epi R₂.g] [Epi φ.τ₁] [IsIso φ.τ₂] : IsIso φ.τ₃ := by
  have : Mono φ.τ₃ :=
    ShortComplex.mono_of_epi_of_epi_of_mono φ hR₂ inferInstance inferInstance inferInstance
  have : Epi (R₁.g ≫ φ.τ₃) := φ.comm₂₃ ▸ epi_comp φ.τ₂ R₂.g
  have : Epi φ.τ₃ := epi_of_epi R₁.g φ.τ₃
  exact isIso_of_mono_of_epi φ.τ₃

end CategoryTheory.ShortComplex
