/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import TauCeti.CategoryTheory.Abelian.SubquotientPresentation
public import TauCeti.CategoryTheory.Subobject.Limits
import TauCeti.CategoryTheory.Subobject.Image

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

private noncomputable def cyclesSubobjectIso (S : ShortComplex C) :
    (kernelSubobject S.g : C) ≅ S.cycles :=
  kernelSubobjectIso S.g ≪≫ S.cyclesIsoKernel.symm

@[reassoc]
private lemma cyclesSubobjectIso_hom_iCycles (S : ShortComplex C) :
    (cyclesSubobjectIso S).hom ≫ S.iCycles = (kernelSubobject S.g).arrow := by
  simp [cyclesSubobjectIso]

@[reassoc]
private lemma factorThruImageSubobject_comp_ofLE_comp_cyclesSubobjectIso (S : ShortComplex C) :
    factorThruImageSubobject S.f ≫
        Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
          (image_le_kernel S.f S.g S.zero) ≫ (cyclesSubobjectIso S).hom =
      S.toCycles := by
  rw [← cancel_mono S.iCycles]
  simp [cyclesSubobjectIso_hom_iCycles]

private noncomputable def isColimitCokernelImageToKernel (S : ShortComplex C) :
    IsColimit (CokernelCofork.ofπ ((cyclesSubobjectIso S).hom ≫ S.homologyπ)
      (by
        rw [← cancel_epi (factorThruImageSubobject S.f), comp_zero,
          factorThruImageSubobject_comp_ofLE_comp_cyclesSubobjectIso_assoc,
          toCycles_comp_homologyπ])) :=
  CokernelCofork.isColimitOfIsColimitOfIff S.homologyIsCokernel
    (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g) (image_le_kernel S.f S.g S.zero))
    (cyclesSubobjectIso S) fun _ φ ↦ by
      rw [← factorThruImageSubobject_comp_ofLE_comp_cyclesSubobjectIso_assoc,
        ← comp_zero (f := factorThruImageSubobject S.f), cancel_epi]

/-- The canonical isomorphism between the cokernel of the inclusion
`imageSubobject S.f ⟶ kernelSubobject S.g` and the homology `S.homology` of a short complex `S`
in an abelian category. -/
noncomputable def cokernelImageToKernelIsoHomology (S : ShortComplex C) :
    cokernel (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
      (image_le_kernel S.f S.g S.zero)) ≅ S.homology :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) (isColimitCokernelImageToKernel S)

@[reassoc]
lemma cokernel_π_comp_cokernelImageToKernelIsoHomology_hom (S : ShortComplex C) :
    cokernel.π (Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
        (image_le_kernel S.f S.g S.zero)) ≫ S.cokernelImageToKernelIsoHomology.hom =
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ := by
  refine (IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (isColimitCokernelImageToKernel S) WalkingParallelPair.one).trans ?_
  simp [cyclesSubobjectIso]

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
  kernelSubobject_factors _ _ (by rw [Category.assoc, φ.comm₂₃, kernelSubobject_arrow_comp_assoc,
    zero_comp])

/-- A morphism of short complexes `φ : S₁ ⟶ S₂` carries `imageSubobject S₁.f` into
`imageSubobject S₂.f`. -/
lemma factors_imageSubobject_map {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (imageSubobject S₂.f).Factors ((imageSubobject S₁.f).arrow ≫ φ.τ₂) := by
  rw [← Subobject.exists_le_iff, Subobject.exists_obj_imageSubobject, ← φ.comm₁₂]
  exact imageSubobject_comp_le φ.τ₁ S₂.f

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
