/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Irreducible maps in almost-split sequences

A left minimal left almost-split map that is not split epic is irreducible; dually, a right
minimal right almost-split map that is not split monic is irreducible. These criteria identify
irreducible maps in almost-split sequences from minimality and the complementary non-splitting
condition. In a preadditive category the same conclusions hold after restricting to a
retract of the source, or projecting onto a retract of the target, respectively. These component
criteria identify the irreducible maps supplied by a decomposition of the middle term.

These are standard criteria for irreducible maps; see Auslander,
Reiten and Smalø, *Representation Theory of Artin Algebras*, V.5.
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}

section Components

variable [Preadditive C]

/-- Restricting a right minimal right almost-split map to a retract of its source gives an
irreducible morphism, provided the restriction is not split monic. -/
theorem IsRightAlmostSplit.isIrreducibleMorphism_comp_of_isSplitMono
    (hf : IsRightAlmostSplit f)
    (hmin : ∀ u : X ⟶ X, u ≫ f = f → IsIso u)
    {Z : C} (i : Z ⟶ X) [IsSplitMono i] (hnot : ¬ IsSplitMono (i ≫ f)) :
    IsIrreducibleMorphism (i ≫ f) := by
  refine isIrreducibleMorphism_iff.mpr ⟨hnot,
    fun h ↦ hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp i f), ?_⟩
  intro W a b hab
  by_cases hb : IsSplitEpi b
  · exact Or.inr hb
  obtain ⟨t, ht⟩ := hf.factors W b hb
  -- Replace the restriction on the chosen retract, leaving its complement fixed.
  let u := 𝟙 X - retraction i ≫ i + retraction i ≫ a ≫ t
  have hu : u ≫ f = f := by
    simp only [u, Preadditive.add_comp, Preadditive.sub_comp, Category.id_comp,
      Category.assoc, ht, hab, sub_add_cancel]
  have := hmin u hu
  have hiu : i ≫ u = a ≫ t := by
    simp [u, Preadditive.comp_add, Preadditive.comp_sub, ← Category.assoc]
  have : IsSplitMono (a ≫ t) := hiu ▸ inferInstanceAs (IsSplitMono (i ≫ u))
  exact Or.inl (isSplitMono_of_isSplitMono_comp a t)

/-- Projecting a left minimal left almost-split map onto a retract of its target gives an
irreducible morphism, provided the projection is not split epic. -/
theorem IsLeftAlmostSplit.isIrreducibleMorphism_comp_of_isSplitEpi
    (hf : IsLeftAlmostSplit f)
    (hmin : ∀ u : Y ⟶ Y, f ≫ u = f → IsIso u)
    {Z : C} (p : Y ⟶ Z) [IsSplitEpi p] (hnot : ¬ IsSplitEpi (f ≫ p)) :
    IsIrreducibleMorphism (f ≫ p) := by
  refine isIrreducibleMorphism_iff.mpr ⟨
    fun h ↦ hf.not_isSplitMono (isSplitMono_of_isSplitMono_comp f p), hnot, ?_⟩
  intro W a b hab
  by_cases ha : IsSplitMono a
  · exact Or.inl ha
  obtain ⟨t, ht⟩ := hf.factors W a ha
  -- Replace the projection onto the chosen retract, leaving its complement fixed.
  let u := 𝟙 Y - p ≫ section_ p + t ≫ b ≫ section_ p
  have hu : f ≫ u = f := by
    simp only [u, Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, ht, hab, sub_add_cancel]
  have := hmin u hu
  have hup : u ≫ p = t ≫ b := by
    simp [u, Preadditive.add_comp, Preadditive.sub_comp, Category.assoc]
  have : IsSplitEpi (t ≫ b) := hup ▸ inferInstanceAs (IsSplitEpi (u ≫ p))
  exact Or.inr (isSplitEpi_of_isSplitEpi_comp t b)

end Components

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
