/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Basic

/-!
# Irreducible maps in almost-split sequences

A left minimal left almost-split map that is not split epic is irreducible; dually, a right
minimal right almost-split map that is not split monic is irreducible. These criteria identify
irreducible maps in almost-split sequences from minimality and the complementary non-splitting
condition.

These are standard criteria for irreducible maps; see Auslander,
Reiten and Smalø, *Representation Theory of Artin Algebras*, V.5.
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}

/-- A left minimal left almost-split map that is not split epic is irreducible. Left minimality
says that every endomorphism of the target fixing the map is invertible. -/
theorem IsLeftAlmostSplit.isIrreducibleMorphism_of_minimal (hf : IsLeftAlmostSplit f)
    (hnot : ¬ IsSplitEpi f)
    (hmin : ∀ u : Y ⟶ Y, f ≫ u = f → IsIso u) :
    IsIrreducibleMorphism f := by
  rw [isIrreducibleMorphism_iff]
  refine ⟨hf.not_isSplitMono, hnot, ?_⟩
  · intro Z g h hgh
    by_cases hg : IsSplitMono g
    · exact Or.inl hg
    · obtain ⟨t, ht⟩ := hf.factors Z g hg
      right
      have heq : f ≫ (t ≫ h) = f := by rw [← Category.assoc, ht, hgh]
      let := hmin (t ≫ h) heq
      exact isSplitEpi_of_isSplitEpi_comp t h

/-- A right minimal right almost-split map that is not split monic is irreducible. Right minimality
says that every endomorphism of the source fixing the map is invertible. -/
theorem IsRightAlmostSplit.isIrreducibleMorphism_of_minimal (hf : IsRightAlmostSplit f)
    (hnot : ¬ IsSplitMono f)
    (hmin : ∀ u : X ⟶ X, u ≫ f = f → IsIso u) :
    IsIrreducibleMorphism f := by
  rw [isIrreducibleMorphism_iff]
  refine ⟨hnot, hf.not_isSplitEpi, ?_⟩
  · intro Z g h hgh
    by_cases hh : IsSplitEpi h
    · exact Or.inr hh
    · obtain ⟨t, ht⟩ := hf.factors Z h hh
      left
      have heq : (g ≫ t) ≫ f = f := by rw [Category.assoc, ht, hgh]
      let := hmin (g ≫ t) heq
      exact isSplitMono_of_isSplitMono_comp g t

end TauCeti
