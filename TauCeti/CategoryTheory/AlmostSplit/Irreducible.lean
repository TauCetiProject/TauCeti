/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Basic

/-!
# Irreducible maps in almost-split sequences

A minimal left almost-split monomorphism is irreducible, and a minimal right almost-split
epimorphism is irreducible. Indeed, a non-split factor must factor back through the almost-split
map; minimality makes the resulting endomorphism invertible, so the other factor splits.
Minimality is essential: adjoining a redundant summand to the middle object preserves the
almost-split factorization property but destroys irreducibility.

The argument is the standard factorization criterion for irreducible maps; see Auslander,
Reiten and Smalø, *Representation Theory of Artin Algebras*, V.5.
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}

/-- A left almost-split monomorphism that is left minimal is irreducible. Left minimality says
that every endomorphism of the target fixing the map is invertible. -/
theorem IsLeftAlmostSplit.isIrreducibleMorphism_of_minimal (hf : IsLeftAlmostSplit f) [Mono f]
    (hmin : ∀ u : Y ⟶ Y, f ≫ u = f → IsIso u) :
    IsIrreducibleMorphism f := by
  rw [isIrreducibleMorphism_iff]
  refine ⟨hf.not_isSplitMono, ?_, ?_⟩
  · intro h
    let : IsSplitEpi f := h
    exact hf.not_isSplitMono (by
      let := isIso_of_mono_of_isSplitEpi f
      infer_instance)
  · intro Z g h hgh
    by_cases hg : IsSplitMono g
    · exact Or.inl hg
    · obtain ⟨t, ht⟩ := hf.factors Z g hg
      right
      have heq : f ≫ (t ≫ h) = f := by rw [← Category.assoc, ht, hgh]
      let := hmin (t ≫ h) heq
      exact isSplitEpi_of_isSplitEpi_comp t h

/-- A right almost-split epimorphism that is right minimal is irreducible. Right minimality says
that every endomorphism of the source fixing the map is invertible. -/
theorem IsRightAlmostSplit.isIrreducibleMorphism_of_minimal (hf : IsRightAlmostSplit f) [Epi f]
    (hmin : ∀ u : X ⟶ X, u ≫ f = f → IsIso u) :
    IsIrreducibleMorphism f := by
  rw [isIrreducibleMorphism_iff]
  refine ⟨?_, hf.not_isSplitEpi, ?_⟩
  · intro h
    let : IsSplitMono f := h
    exact hf.not_isSplitEpi (by
      let := isIso_of_epi_of_isSplitMono f
      infer_instance)
  · intro Z g h hgh
    by_cases hh : IsSplitEpi h
    · exact Or.inr hh
    · obtain ⟨t, ht⟩ := hf.factors Z h hh
      left
      have heq : (g ≫ t) ≫ f = f := by rw [Category.assoc, ht, hgh]
      let := hmin (g ≫ t) heq
      exact isSplitMono_of_isSplitMono_comp g t

end TauCeti
