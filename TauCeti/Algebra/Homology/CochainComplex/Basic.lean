/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Basic lemmas on cochain complexes

Equality lemmas for cochain complexes constructed via `CochainComplex.of`.

## Main results

* `CochainComplex.of_eq`: two cochain complexes built with `CochainComplex.of` over the same
  index type are equal when their degreewise objects are equal and their consecutive differentials
  are heterogeneously equal.
-/

public section

namespace CochainComplex

open CategoryTheory

/-- Two cochain complexes constructed with `CochainComplex.of` are equal when their degreewise
objects are equal and their consecutive differentials are heterogeneously equal. -/
theorem of_eq {V : Type*} [Category* V] [Limits.HasZeroMorphisms V]
    {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
    {F₁ F₂ : α → V} (hF : ∀ n, F₁ n = F₂ n)
    {d₁ : ∀ n, F₁ n ⟶ F₁ (n + 1)} {d₂ : ∀ n, F₂ n ⟶ F₂ (n + 1)}
    (hd : ∀ n, d₁ n ≍ d₂ n)
    {hc₁ : ∀ n, d₁ n ≫ d₁ (n + 1) = 0} {hc₂ : ∀ n, d₂ n ≫ d₂ (n + 1) = 0} :
    CochainComplex.of F₁ d₁ hc₁ = CochainComplex.of F₂ d₂ hc₂ := by
  refine HomologicalComplex.ext (funext hF) ?_
  rintro i _ rfl
  simp only [CochainComplex.of_d, comp_eqToHom_iff, Category.assoc]
  exact (conj_eqToHom_iff_heq' _ _ _ _).2 (hd i)

end CochainComplex
