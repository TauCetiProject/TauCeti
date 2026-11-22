/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import TauCeti.CategoryTheory.Abelian.SubquotientPresentation

/-!
# Subquotient presentation of the homology of a short complex

For a short complex `S : ShortComplex C` in an abelian category `C`, the image subobject
`imageSubobject S.f` lies inside the kernel subobject `kernelSubobject S.g`
(`image_le_kernel S.f S.g S.zero`), and the cokernel of the inclusion
`Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g) _` is canonically isomorphic to
`S.homology` (`CategoryTheory.ShortComplex.cokernelImageToKernelIsoHomology`).

This packages `S.homology` as a subquotient presentation inside `S.X₂`
(`CategoryTheory.ShortComplex.homologyPresentation`), which is functorial in morphisms of short
complexes (`CategoryTheory.ShortComplex.homologyPresentation_map`) and identifies with
`(S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf` when both differentials vanish
(`CategoryTheory.ShortComplex.homologyPresentation_isoOfEq_of_eq_zero`).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- The canonical isomorphism between the cokernel of the inclusion
`imageSubobject S.f ⟶ kernelSubobject S.g` and the homology `S.homology` of a short complex `S`
in an abelian category. -/
noncomputable def cokernelImageToKernelIsoHomology (S : ShortComplex C) :
    cokernel (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
      (image_le_kernel S.f S.g S.zero)) ≅ S.homology :=
  (cokernelEpiComp
    (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g) (image_le_kernel S.f S.g S.zero))
    (factorThruImageSubobject S.f)).symm ≪≫
    cokernel.mapIso _ (kernel.lift S.g S.f S.zero) (Iso.refl _) (kernelSubobjectIso S.g) (by
      rw [Category.assoc, subobject_ofLE_as_imageToKernel, ← Category.assoc,
        factorThruImageSubobject_comp_imageToKernel, Iso.refl_hom, Category.id_comp,
        factorThruKernelSubobject_comp_kernelSubobjectIso]) ≪≫
    S.homologyIsoCokernelLift.symm

@[reassoc]
lemma cokernel_π_comp_cokernelImageToKernelIsoHomology_hom (S : ShortComplex C) :
    cokernel.π (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
        (image_le_kernel S.f S.g S.zero)) ≫ S.cokernelImageToKernelIsoHomology.hom =
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ := by
  simp only [cokernelImageToKernelIsoHomology, Iso.trans_hom, Iso.symm_hom, cokernelEpiComp_inv,
    cokernel.mapIso_hom, cokernel.π_desc_assoc, Category.assoc]
  have hcyc :
      (LeftHomologyData.ofHasKernelOfHasCokernel S).cyclesIso.inv = S.cyclesIsoKernel.inv := by
    rw [← cancel_mono S.iCycles, LeftHomologyData.cyclesIso_inv_comp_iCycles]
    simp
  rw [← hcyc, ← (LeftHomologyData.ofHasKernelOfHasCokernel S).π_comp_homologyIso_inv]
  rfl

/-- The canonical subquotient presentation of `S.homology` inside `S.X₂`, with smaller subobject
`imageSubobject S.f` and larger subobject `kernelSubobject S.g`. -/
noncomputable abbrev homologyPresentation (S : ShortComplex C) :
    TauCeti.SubquotientPresentation S.X₂ S.homology where
  B := imageSubobject S.f
  Z := kernelSubobject S.g
  le := image_le_kernel S.f S.g S.zero
  iso := S.cokernelImageToKernelIsoHomology

@[reassoc]
lemma homologyPresentation_π (S : ShortComplex C) :
    S.homologyPresentation.π =
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ := by
  rw [← TauCeti.SubquotientPresentation.cokernel_π_iso_hom]
  exact S.cokernel_π_comp_cokernelImageToKernelIsoHomology_hom

/-- A morphism of short complexes `φ : S₁ ⟶ S₂` carries `kernelSubobject S₁.g` into
`kernelSubobject S₂.g`. -/
lemma factors_kernelSubobject_map {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (kernelSubobject S₂.g).Factors ((kernelSubobject S₁.g).arrow ≫ φ.τ₂) :=
  (Subobject.factors_iff _ _).mpr
    ⟨kernelSubobjectMap (Arrow.homMk φ.τ₂ φ.τ₃ φ.comm₂₃), kernelSubobjectMap_arrow _⟩

/-- A morphism of short complexes `φ : S₁ ⟶ S₂` carries `imageSubobject S₁.f` into
`imageSubobject S₂.f`. -/
lemma factors_imageSubobject_map {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (imageSubobject S₂.f).Factors ((imageSubobject S₁.f).arrow ≫ φ.τ₂) :=
  (Subobject.factors_iff _ _).mpr
    ⟨imageSubobjectMap (Arrow.homMk φ.τ₁ φ.τ₂ φ.comm₁₂), imageSubobjectMap_arrow _⟩

/-- The morphism induced by `φ.τ₂` between the canonical homology presentations of `S₁` and `S₂`
is `ShortComplex.homologyMap φ`. -/
theorem homologyPresentation_map {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    S₁.homologyPresentation.map S₂.homologyPresentation φ.τ₂
        (factors_imageSubobject_map φ) (factors_kernelSubobject_map φ) =
      ShortComplex.homologyMap φ := by
  apply TauCeti.SubquotientPresentation.map_eq_of_π_comp
  rw [homologyPresentation_π, homologyPresentation_π]
  have hcyc : (kernelSubobject S₂.g).factorThru ((kernelSubobject S₁.g).arrow ≫ φ.τ₂)
        (factors_kernelSubobject_map φ) ≫ (kernelSubobjectIso S₂.g).hom ≫ S₂.cyclesIsoKernel.inv =
      (kernelSubobjectIso S₁.g).hom ≫ S₁.cyclesIsoKernel.inv ≫ ShortComplex.cyclesMap φ := by
    rw [← cancel_mono S₂.iCycles]
    simp
  rw [reassoc_of% hcyc, Category.assoc, Category.assoc, homologyπ_naturality]

/-- When both morphisms of `S` vanish, the comparison isomorphism between `refl S.X₂` and
`S.homologyPresentation` is `(S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf`. -/
lemma homologyPresentation_isoOfEq_of_eq_zero (S : ShortComplex C) (hf : S.f = 0) (hg : S.g = 0) :
    (TauCeti.SubquotientPresentation.refl S.X₂).isoOfEq S.homologyPresentation
        (by simp [hf]) (by simp [hg]) =
      (S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf := by
  ext
  rw [← cancel_epi (TauCeti.SubquotientPresentation.refl S.X₂).π,
    TauCeti.SubquotientPresentation.π_isoOfEq_hom,
    TauCeti.SubquotientPresentation.π_refl, homologyPresentation_π]
  dsimp only [TauCeti.SubquotientPresentation.refl, TauCeti.SubquotientPresentation.ofEpi]
  have hcyc : Subobject.ofLE (⊤ : Subobject S.X₂) (kernelSubobject S.g)
        (by simp [hg] : (⊤ : Subobject S.X₂) ≤ kernelSubobject S.g) ≫
        (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv =
      (⊤ : Subobject S.X₂).arrow ≫ (S.cyclesIsoX₂ hg).inv := by
    rw [← cancel_mono S.iCycles]
    simp
  rw [Iso.trans_hom, Iso.symm_hom, reassoc_of% hcyc]
  simp [asIsoHomologyπ]

end CategoryTheory.ShortComplex
