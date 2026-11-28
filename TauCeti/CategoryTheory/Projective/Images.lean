/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Split images of maps to projective objects

A map to a projective object with an epimorphic image factorization has a split
image inclusion exactly when the map has an inner inverse.

The image-splitting criterion adapts the projective lifting argument from
[Tau Ceti PR #47044](https://github.com/TauCetiProject/TauCeti/pull/47044).
-/

public section

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] {X Y : C}

/-- If the image factorization of a map to a projective object is epimorphic,
its image inclusion splits exactly when the map has an inner inverse. -/
theorem _root_.Quiver.Hom.isSplitMono_image_ι_iff_exists_comp_comp_eq_self (f : X ⟶ Y)
    [HasImage f] [Epi (factorThruImage f)] [Projective Y] :
    IsSplitMono (image.ι f) ↔ ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
  constructor
  · intro h
    let g := Projective.factorThru (retraction (image.ι f)) (factorThruImage f)
    refine ⟨g, ?_⟩
    calc
      f ≫ g ≫ f = factorThruImage f ≫ image.ι f ≫
          (g ≫ factorThruImage f) ≫ image.ι f := by
        simp only [Category.assoc, image.fac_assoc, image.fac]
      _ = f := by simp [g]
  · rintro ⟨g, hg⟩
    refine ⟨⟨g ≫ factorThruImage f, ?_⟩⟩
    rw [← cancel_epi (factorThruImage f), ← cancel_mono (image.ι f)]
    simpa only [Category.assoc, image.fac_assoc, image.fac, Category.comp_id] using hg

end CategoryTheory
