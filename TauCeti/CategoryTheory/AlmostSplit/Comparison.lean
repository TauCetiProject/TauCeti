/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Basic

/-!
# Split comparison maps for almost-split morphisms

In a commutative square whose lower map is left almost split and whose upper map is
not a split monomorphism, a split monomorphism on sources must be an isomorphism.
Dually, if the upper map is right almost split and the lower map is not a split
epimorphism, a split epimorphism on targets must be an isomorphism.

These comparison principles let uniqueness arguments for almost-split sequences use
locality at just one of the two sequences, without any finiteness assumption on the other.
They require only a category, with no additive or exact structure.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, V.1.
-/

public section

open CategoryTheory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] {X Y X' Y' : C}
  {f : X ⟶ Y} {g : X' ⟶ Y'}

/-- A split monomorphism on sources in a square with left almost-split lower map is
invertible if the upper map is not a split monomorphism. -/
theorem IsLeftAlmostSplit.isIso_of_isSplitMono_of_comm (hg : IsLeftAlmostSplit g)
    (hf : ¬ IsSplitMono f) (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) [IsSplitMono a] : IsIso a := by
  have hr : IsSplitMono (retraction a) := by
    by_contra hr
    obtain ⟨t, ht⟩ := hg.factors X (retraction a) hr
    apply hf
    refine IsSplitMono.mk' ⟨b ≫ t, ?_⟩
    rw [← Category.assoc, h, Category.assoc, ht, IsSplitMono.id]
  exact IsIso.of_mono_retraction a

/-- A split epimorphism on targets in a square with right almost-split upper map is
invertible if the lower map is not a split epimorphism. -/
theorem IsRightAlmostSplit.isIso_of_isSplitEpi_of_comm (hf : IsRightAlmostSplit f)
    (hg : ¬ IsSplitEpi g) (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) [IsSplitEpi b] : IsIso b := by
  have hs : IsSplitEpi (section_ b) := by
    by_contra hs
    obtain ⟨t, ht⟩ := hf.factors Y' (section_ b) hs
    apply hg
    refine IsSplitEpi.mk' ⟨t ≫ a, ?_⟩
    rw [Category.assoc, ← h, ← Category.assoc, ht, IsSplitEpi.id]
  exact IsIso.of_epi_section b

end TauCeti
