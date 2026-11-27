/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

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
  constructor
  · intro h
    let i := image.ι f
    let p := factorThruImage f
    refine ⟨Projective.factorThru (retraction i) p, ?_⟩
    calc
      f ≫ Projective.factorThru (retraction i) p ≫ f =
          p ≫ i ≫ (Projective.factorThru (retraction i) p ≫ p) ≫ i := by
        simp only [Category.assoc, image.fac, image.fac_assoc, i, p]
      _ = f := by rw [Projective.factorThru_comp, IsSplitMono.id_assoc, image.fac]
  · rintro ⟨g, hg⟩
    refine IsSplitMono.mk' ⟨g ≫ factorThruImage f, ?_⟩
    apply (cancel_epi (factorThruImage f)).mp
    apply (cancel_mono (image.ι f)).mp
    simpa only [Category.assoc, image.fac, image.fac_assoc, Category.comp_id] using hg
