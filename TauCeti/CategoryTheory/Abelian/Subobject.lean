/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Order.Bounds.Basic
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
of a subquotient back to the ambient object. This file also gives the explicit formula for the
greatest lower bound of any indexed family of subobjects whose cokernel product exists
(`CategoryTheory.Subobject.isGLB_range_kernelSubobject_piLift`), without requiring `WellPowered C`.

## Main results

* `CategoryTheory.Subobject.exists_pullback_eq_self_of_epi`: the image of the preimage of a
  subobject of `X` along `p` is that subobject.
* `CategoryTheory.Subobject.pullback_exists_eq_self_of_kernelSubobject_le`: the preimage of the
  image of a subobject of `Y` containing the kernel of `p` is that subobject.
* `CategoryTheory.Subobject.isGLB_range_kernelSubobject_piLift`: the greatest lower bound of a
  family of subobjects as a kernel subobject into the product of their cokernels.
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

/-- In an abelian category, the kernel subobject of the map into the product of the cokernels of
a `J`-indexed family of subobjects of `X` is the greatest lower bound of the family, whenever that
product exists. -/
lemma isGLB_range_kernelSubobject_piLift {J : Type*} {X : C} (S : J → Subobject X)
    [HasProduct fun j ↦ cokernel (S j).arrow] :
    IsGLB (Set.range S) (kernelSubobject (Pi.lift fun j ↦ cokernel.π (S j).arrow)) := by
  have hle (T : Subobject X) :
      T ≤ kernelSubobject (Pi.lift fun j ↦ cokernel.π (S j).arrow) ↔ ∀ j, T ≤ S j := by
    refine ⟨fun h j ↦ ?_, fun h ↦ le_kernelSubobject _ _ ?_⟩
    · have hj : T.arrow ≫ cokernel.π (S j).arrow = 0 := by
        have h0 : T.arrow ≫ Pi.lift (fun j ↦ cokernel.π (S j).arrow) = 0 := by
          rw [← Subobject.ofLE_arrow h, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
        simpa using congrArg (· ≫ Pi.π (fun j ↦ cokernel (S j).arrow) j) h0
      rw [← Subobject.mk_arrow (S j), ← kernelSubobject_cokernel_π (S j).arrow]
      exact le_kernelSubobject _ _ hj
    · refine Limits.Pi.hom_ext _ _ fun j ↦ ?_
      simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, zero_comp]
      rw [← Subobject.ofLE_arrow (h j), Category.assoc, cokernel.condition, comp_zero]
  refine ⟨?_, fun T hT ↦ (hle T).2 fun j ↦ hT ⟨j, rfl⟩⟩
  rintro _ ⟨j, rfl⟩
  exact (hle _).1 le_rfl j

end CategoryTheory.Subobject
