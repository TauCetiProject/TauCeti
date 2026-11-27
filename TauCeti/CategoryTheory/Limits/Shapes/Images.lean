/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
import TauCeti.CategoryTheory.EpiMono

/-!
# Images of morphisms with inner inverses

An inner inverse makes the image inclusion split when the factor map onto the image is epic.
-/

public section

open CategoryTheory CategoryTheory.Limits

/-- An inner inverse splits the image inclusion of a map with epic image factor. -/
theorem Quiver.Hom.isSplitMono_image_ι_of_exists_comp_comp_eq_self
    {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y)
    [HasImage f] [Epi (factorThruImage f)] (h : ∃ g : Y ⟶ X, f ≫ g ≫ f = f) :
    IsSplitMono (image.ι f) := by
  rw [← image.fac f] at h
  exact (((factorThruImage f).exists_comp_comp_eq_self_iff_isSplitEpi_and_isSplitMono
    (image.ι f)).mp h).2
