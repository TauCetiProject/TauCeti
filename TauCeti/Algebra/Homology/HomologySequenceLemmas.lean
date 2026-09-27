/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The middle map of a morphism of short exact sequences of complexes

Let `φ : S₁ ⟶ S₂` be a morphism between two short exact sequences of homological complexes in an
abelian category. Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃` shows that `φ.τ₃`
is a quasi-isomorphism when `φ.τ₁` and `φ.τ₂` are. This file proves the corresponding statement
for the middle map: `φ.τ₂` is a quasi-isomorphism when `φ.τ₁` and `φ.τ₃` are. This lets one
transfer a quasi-isomorphism to the middle terms of short exact sequences after comparing their
outer terms, as for the short exact sequences associated with maps of mapping cones.

## Main results

* `HomologicalComplex.HomologySequence.mono_homologyMap_τ₂`,
  `HomologicalComplex.HomologySequence.epi_homologyMap_τ₂`,
  `HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂`: sufficient conditions for `φ.τ₂`
  to induce a mono, epi or iso in a given degree.
* `HomologicalComplex.HomologySequence.quasiIso_τ₂`: if `φ.τ₁` and `φ.τ₃` are
  quasi-isomorphisms, so is `φ.τ₂`.

-/

public section

open CategoryTheory ComposableArrows Abelian

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

namespace HomologicalComplex

namespace HomologySequence

include hS₁ hS₂

/-- The map `φ.τ₂` is injective on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are injective in
degree `j` and `φ.τ₃` is surjective in the degrees preceding `j`. -/
lemma mono_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : Mono (homologyMap φ.τ₁ j))
    (h₃ : Mono (homologyMap φ.τ₃ j)) :
    Mono (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    -- The exact sequence `H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃)`.
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₁ i hij
    · exact h₂
    · exact h₃
  · have := hS₂.mono_f
    have := mono_homologyMap_of_mono_of_not_rel S₂.f j (by simpa using hj)
    exact mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) this h₂ h₃

/-- The map `φ.τ₂` is surjective on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are surjective in
degree `j` and `φ.τ₁` is injective in the degrees following `j`. -/
lemma epi_homologyMap_τ₂ (j : ι)
    (h₁ : Epi (homologyMap φ.τ₁ j))
    (h₂ : Epi (homologyMap φ.τ₃ j))
    (h₃ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    Epi (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ k, c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    -- The exact sequence `H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃) ⟶ H_k(X₁)`.
    apply epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ j k hjk))
    · exact (composableArrows₅_exact hS₁ j k hjk).δlast.δlast
    · exact (composableArrows₅_exact hS₂ j k hjk).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ k hjk
  · have := hS₁.epi_g
    have := epi_homologyMap_of_epi_of_not_rel S₁.g j (by simpa using hj)
    exact epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₂ j) this h₁ h₂

/-- The map `φ.τ₂` is an isomorphism on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are
isomorphisms in degree `j`, `φ.τ₃` is surjective in the degrees preceding `j`, and `φ.τ₁` is
injective in the degrees following `j`. -/
lemma isIso_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₂ : IsIso (homologyMap φ.τ₁ j))
    (h₃ : IsIso (homologyMap φ.τ₃ j))
    (h₄ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    IsIso (homologyMap φ.τ₂ j) := by
  have := mono_homologyMap_τ₂ φ hS₁ hS₂ j h₁ inferInstance inferInstance
  have := epi_homologyMap_τ₂ φ hS₁ hS₂ j inferInstance inferInstance h₄
  exact isIso_of_mono_of_epi _

/-- **Two out of three for the middle map.** In a morphism of short exact sequences of complexes,
if the outer maps `φ.τ₁` and `φ.τ₃` are quasi-isomorphisms, so is the middle map `φ.τ₂`. -/
lemma quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₂ φ hS₁ hS₂
  all_goals infer_instance

end HomologySequence

end HomologicalComplex
