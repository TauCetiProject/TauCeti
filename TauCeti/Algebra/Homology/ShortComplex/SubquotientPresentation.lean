/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.CategoryTheory.Abelian.Exact
public import TauCeti.CategoryTheory.Abelian.SubquotientPresentation
import TauCeti.CategoryTheory.Subobject.Image

/-!
# The homology of a short complex as a subquotient of its middle object

The homology of a short complex `S` in an abelian category is the quotient of the kernel of `S.g`
by the image of `S.f`. This file records it as a subquotient presentation of `S.homology` inside
`S.X₂`, with smaller subobject `imageSubobject S.f` and larger subobject `kernelSubobject S.g`
(`CategoryTheory.ShortComplex.homologyPresentation`). Its projection is the canonical
identification of `kernelSubobject S.g` with the cycles of `S` followed by `S.homologyπ`. A
morphism of short complexes maps these presentations to each other through its middle component,
over the induced morphism in homology (`CategoryTheory.ShortComplex.homologyPresentation_mapsTo`).

## Main definitions

* `CategoryTheory.ShortComplex.kernelSubobjectIsoCycles`: the kernel subobject of `S.g` is the
  cycles of `S`.
* `CategoryTheory.ShortComplex.homologyPresentation`: the presentation of `S.homology` inside
  `S.X₂` by `imageSubobject S.f ≤ kernelSubobject S.g`.

## Main results

* `CategoryTheory.ShortComplex.homologyPresentation_mapsTo`: naturality of the presentation in
  morphisms of short complexes.

## References

* [Stacks, Tag 011N](https://stacks.math.columbia.edu/tag/011N)
-/

public section

open CategoryTheory Limits Subobject

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C)

/-- The kernel subobject of `S.g` is the cycles of `S`: both are kernels of `S.g`. -/
noncomputable def kernelSubobjectIsoCycles : (kernelSubobject S.g : C) ≅ S.cycles :=
  kernelSubobjectIso S.g ≪≫ S.cyclesIsoKernel.symm

@[reassoc (attr := simp)]
lemma kernelSubobjectIsoCycles_hom_iCycles :
    S.kernelSubobjectIsoCycles.hom ≫ S.iCycles = (kernelSubobject S.g).arrow := by
  simp [kernelSubobjectIsoCycles]

@[reassoc (attr := simp)]
lemma kernelSubobjectIsoCycles_inv_arrow :
    S.kernelSubobjectIsoCycles.inv ≫ (kernelSubobject S.g).arrow = S.iCycles := by
  simp [kernelSubobjectIsoCycles]

/-- Seen inside the kernel of `S.g`, the image of `S.f` is the kernel of the projection onto the
homology. -/
lemma kernelSubobject_kernelSubobjectIsoCycles_hom_homologyπ :
    kernelSubobject (S.kernelSubobjectIsoCycles.hom ≫ S.homologyπ) =
      (Subobject.pullback (kernelSubobject S.g).arrow).obj (imageSubobject S.f) := by
  -- `S.homologyπ` is a cokernel of `S.toCycles`, so its kernel is the image of `S.toCycles`.
  have hπ : kernelSubobject S.homologyπ = imageSubobject S.toCycles :=
    ((exact_iff_image_eq_kernel (ShortComplex.mk _ _ S.toCycles_comp_homologyπ)).1
      (exact_of_g_is_cokernel _ S.homologyIsCokernel)).symm
  have hf : imageSubobject S.f = (Subobject.map S.iCycles).obj (imageSubobject S.toCycles) := by
    rw [← exists_iso_map, Subobject.exists_obj_imageSubobject, toCycles_i]
  rw [← pullback_kernelSubobject, hπ, hf, ← S.kernelSubobjectIsoCycles_hom_iCycles, pullback_comp,
    pullback_map_self]

/-- The homology of `S` presented inside `S.X₂` as the quotient of the kernel of `S.g` by the
image of `S.f`. Its projection is `S.kernelSubobjectIsoCycles.hom ≫ S.homologyπ`. -/
@[expose] noncomputable def homologyPresentation :
    TauCeti.SubquotientPresentation S.X₂ S.homology :=
  TauCeti.SubquotientPresentation.ofEpi (image_le_kernel _ _ S.zero)
    (S.kernelSubobjectIsoCycles.hom ≫ S.homologyπ)
    S.kernelSubobject_kernelSubobjectIsoCycles_hom_homologyπ

@[simp]
lemma homologyPresentation_B : S.homologyPresentation.B = imageSubobject S.f := (rfl)

@[simp]
lemma homologyPresentation_Z : S.homologyPresentation.Z = kernelSubobject S.g := (rfl)

@[simp]
lemma π_homologyPresentation :
    S.homologyPresentation.π = S.kernelSubobjectIsoCycles.hom ≫ S.homologyπ :=
  TauCeti.SubquotientPresentation.π_ofEpi _ _ _

/-- The projection of the presentation of the homology, as a morphism out of
`kernelSubobject S.g`. -/
lemma π_homologyPresentation' :
    S.homologyPresentation.π = ofLE _ (kernelSubobject S.g) S.homologyPresentation_Z.le ≫
      S.kernelSubobjectIsoCycles.hom ≫ S.homologyπ :=
  TauCeti.SubquotientPresentation.π_ofEpi' _ _ _

/-- A morphism of short complexes maps the presentation of the homology of its source to that of
its target, through its middle component and over the induced morphism in homology. -/
lemma homologyPresentation_mapsTo {S' : ShortComplex C} (α : S ⟶ S') :
    S.homologyPresentation.MapsTo S'.homologyPresentation α.τ₂ (homologyMap α) := by
  have h : kernelSubobjectMap (Arrow.homMk α.τ₂ α.τ₃ α.comm₂₃) ≫
      S'.kernelSubobjectIsoCycles.hom = S.kernelSubobjectIsoCycles.hom ≫ cyclesMap α := by
    simp [← cancel_mono S'.iCycles]
  refine TauCeti.SubquotientPresentation.mapsTo_iff.2
    ⟨ofLE _ _ S.homologyPresentation_Z.le ≫ kernelSubobjectMap (Arrow.homMk α.τ₂ α.τ₃ α.comm₂₃) ≫
      ofLE _ _ S'.homologyPresentation_Z.ge, by simp, ?_⟩
  rw [π_homologyPresentation', π_homologyPresentation']
  simp [ofLE_comp_ofLE_assoc, reassoc_of% h]

end CategoryTheory.ShortComplex
