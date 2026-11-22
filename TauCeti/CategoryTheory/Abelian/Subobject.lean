/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import TauCeti.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Subobject
import TauCeti.CategoryTheory.Abelian.ImageSubobject
import TauCeti.CategoryTheory.Subobject.Image

/-!
# Preimages and images of subobjects in an abelian category

Let `p : Y ⟶ X` be a morphism in an abelian category. The preimage along `p`
(`Subobject.pullback p`) of the image along `p` (`Subobject.exists p`) of a subobject of `Y`
containing the kernel of `p` is that subobject; when `p` is an epimorphism, the image of the
preimage of a subobject of `X` is that subobject. So for an epimorphism `p`, preimages and images
are mutually inverse between the subobjects of `X` and the subobjects of `Y` containing the kernel
of `p`. This is the correspondence theorem for quotients, in the form used to transport subobjects
of a subquotient back to the ambient object.

## Main results

* `CategoryTheory.Subobject.exists_pullback_eq_self_of_epi`: the image of the preimage of a
  subobject of `X` along `p` is that subobject.
* `CategoryTheory.Subobject.pullback_exists_eq_self_of_kernelSubobject_le`: the preimage of the
  image of a subobject of `Y` containing the kernel of `p` is that subobject.
-/

public section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}

namespace CategoryTheory.Subobject

/-- Along an epimorphism, the image of the preimage of a subobject is that subobject. -/
@[simp]
lemma exists_pullback_eq_self_of_epi (p : Y ⟶ X) [Epi p] (K : Subobject X) :
    («exists» p).obj ((pullback p).obj K) = K := by
  rw [exists_eq_imageSubobject, ← (isPullback p K).w, imageSubobject_comp_eq_of_epi,
    imageSubobject_mono, mk_arrow]

/-- The preimage of the image of a subobject containing the kernel is that subobject. -/
lemma pullback_exists_eq_self_of_kernelSubobject_le (p : Y ⟶ X) {S : Subobject Y}
    (hS : kernelSubobject p ≤ S) : (pullback p).obj ((«exists» p).obj S) = S := by
  refine le_antisymm ?_ (le_pullback_exists p S)
  set T := (pullback p).obj ((«exists» p).obj S)
  have hT : (imageSubobject (S.arrow ≫ p)).Factors (T.arrow ≫ p) := by
    rw [← exists_eq_imageSubobject, ← pullback_factors_iff]
    exact factors_self T
  obtain ⟨A', π, _, x, hx⟩ := (imageSubobject_factors_iff_up_to_refinements _ _).1 hT
  have hker : S.Factors (π ≫ T.arrow - x ≫ S.arrow) :=
    factors_of_le _ hS (kernelSubobject_factors _ _ (by simp [hx]))
  have hS' : S.Factors (π ≫ T.arrow) := by
    simpa using factors_add _ _ hker (factors_comp_arrow x)
  calc T = imageSubobject (π ≫ T.arrow) := by
        rw [imageSubobject_comp_eq_of_epi, imageSubobject_mono, mk_arrow]
    _ ≤ S := imageSubobject_le _ (S.factorThru _ hS') (factorThru_arrow _ _ _)

end CategoryTheory.Subobject
