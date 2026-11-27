/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import TauCeti.CategoryTheory.VonNeumannRegular.Basic

/-!
# Von Neumann regularity in abelian categories with split monomorphisms

In an abelian category where all monomorphisms split, every morphism has an inner inverse.
-/

public section

namespace TauCeti.IsVonNeumannRegularCategory

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- An abelian category in which every monomorphism splits is von Neumann regular. -/
instance [Abelian C] [SplitMonoCategory C] : IsVonNeumannRegularCategory C where
  exists_comp_comp_eq_self {X Y} f := by
    -- A retraction of the kernel of `f` gives a section `s` of its coimage, and a retraction of the
    -- image of `f` gives the rest.
    have := isSplitMono_of_mono (kernel.ι f)
    have := isSplitMono_of_mono (Abelian.image.ι f)
    let s : Abelian.coimage f ⟶ X := cokernel.desc (kernel.ι f)
      (𝟙 X - retraction (kernel.ι f) ≫ kernel.ι f) (by simp [Preadditive.comp_sub])
    have hf : Abelian.coimage.π f ≫ Abelian.coimageImageComparison f =
        f ≫ retraction (Abelian.image.ι f) := by
      simpa using Abelian.coimage_image_factorisation_assoc f (retraction (Abelian.image.ι f))
    refine ⟨retraction (Abelian.image.ι f) ≫ inv (Abelian.coimageImageComparison f) ≫ s, ?_⟩
    rw [Category.assoc, Category.assoc, ← Category.assoc f (retraction _), ← hf]
    simp [s, Preadditive.sub_comp]

end TauCeti.IsVonNeumannRegularCategory
