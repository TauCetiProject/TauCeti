/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
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
* `CategoryTheory.Subobject.pullback_exists_eq_kernelSubobject_sup`: for an arbitrary subobject,
  taking its image and then its preimage joins it with the kernel.
* `CategoryTheory.Limits.kernelSubobject_cokernel_π`: the kernel of the cokernel of a
  monomorphism `f` is the subobject represented by `f`.
* `CategoryTheory.ShortComplex.Exact.imageSubobject_comp_inv_eq_kernelSubobject_hom_comp`: the
  exactness of a short complex, as an equality of subobjects, transported along an isomorphism
  `A ≅ S.X₂`.
-/

public section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}

namespace CategoryTheory.Limits

/-- The kernel of the cokernel of a monomorphism `f` is the subobject represented by `f`. -/
@[simp]
lemma kernelSubobject_cokernel_π {W : C} (f : W ⟶ Y) [Mono f] :
    kernelSubobject (cokernel.π f) = Subobject.mk f := by
  rw [← imageSubobject_mono f]
  exact ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).exact_iff_image_eq_kernel.1
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))).symm

end CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

/-- For an exact short complex `S` and an isomorphism `φ : A ≅ S.X₂`, the image of
`S.f ≫ φ.inv` is the kernel of `φ.hom ≫ S.g`: exactness of `S` at `S.X₂`, transported to `A`. -/
lemma Exact.imageSubobject_comp_inv_eq_kernelSubobject_hom_comp {S : ShortComplex C}
    (hS : S.Exact) {A : C} (φ : A ≅ S.X₂) :
    imageSubobject (S.f ≫ φ.inv) = kernelSubobject (φ.hom ≫ S.g) := by
  let S' := ShortComplex.mk (S.f ≫ φ.inv) (φ.hom ≫ S.g) (by simp)
  have e : S ≅ S' := isoMk (Iso.refl _) φ.symm (Iso.refl _) (by simp [S']) (by simp [S'])
  exact S'.exact_iff_image_eq_kernel.1 (exact_of_iso e hS)

end CategoryTheory.ShortComplex

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

/-- The preimage of the image of a subobject is its join with the kernel. -/
lemma pullback_exists_eq_kernelSubobject_sup (p : Y ⟶ X) (S : Subobject Y) :
    (pullback p).obj ((«exists» p).obj S) = kernelSubobject p ⊔ S := by
  refine le_antisymm ?_ (sup_le ?_ (le_pullback_exists p S))
  · calc
      (pullback p).obj ((«exists» p).obj S) ≤
          (pullback p).obj ((«exists» p).obj (kernelSubobject p ⊔ S)) :=
        (pullback p).monotone ((«exists» p).monotone le_sup_right)
      _ = _ := pullback_exists_eq_self_of_kernelSubobject_le p le_sup_left
  · apply ((existsPullbackAdj p).gc _ _).mp
    simp [exists_eq_imageSubobject]

end CategoryTheory.Subobject

namespace CategoryTheory

/-- A composite with an epimorphism is epic exactly when the image of the first map and the
kernel of the epimorphism together generate the middle object. -/
lemma epi_comp_iff_kernelSubobject_sup_imageSubobject_eq_top {W : C} (f : W ⟶ Y)
    (p : Y ⟶ X) [Epi p] :
    Epi (f ≫ p) ↔ kernelSubobject p ⊔ imageSubobject f = ⊤ := by
  rw [← imageSubobject_eq_top_iff_epi, ← Subobject.exists_obj_imageSubobject,
    ← Subobject.pullback_exists_eq_kernelSubobject_sup, ← Subobject.pullback_top p]
  exact (Function.LeftInverse.injective (Subobject.exists_pullback_eq_self_of_epi p)).eq_iff.symm

end CategoryTheory
