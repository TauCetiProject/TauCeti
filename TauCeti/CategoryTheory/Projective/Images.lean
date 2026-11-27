/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import TauCeti.CategoryTheory.EpiMono

/-!
# Images of morphisms into projective objects

When the factor map onto the image is epic, a morphism into a projective object has an inner
inverse exactly when the image inclusion splits.
-/

public section

open CategoryTheory CategoryTheory.Limits

/-- For a map into a projective object with epic image factor, the image inclusion splits
exactly when the map has an inner inverse. -/
theorem Quiver.Hom.isSplitMono_image_ι_iff_exists_comp_comp_eq_self
    {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y)
    [HasImage f] [Epi (factorThruImage f)] [Projective Y] :
    IsSplitMono (image.ι f) ↔ ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
  have h : (∃ g : Y ⟶ X, f ≫ g ≫ f = f) ↔
      IsSplitEpi (factorThruImage f) ∧ IsSplitMono (image.ι f) := by
    simpa only [image.fac] using
      (factorThruImage f).exists_comp_comp_eq_self_iff_isSplitEpi_and_isSplitMono (image.ι f)
  refine ⟨fun hi ↦ h.mpr ⟨?_, hi⟩, fun hf ↦ (h.mp hf).2⟩
  exact .mk'
    ⟨image.ι f ≫ Projective.factorThru (retraction (image.ι f)) (factorThruImage f), by simp⟩
