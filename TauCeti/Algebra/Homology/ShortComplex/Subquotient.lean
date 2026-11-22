/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import TauCeti.CategoryTheory.Abelian.SubquotientPresentation

/-!
# Homology of a short complex as a subquotient presentation

In an abelian category `C`, `CategoryTheory.ShortComplex.homologyPresentation` canonically presents
`S.homology` as `kernelSubobject S.g / imageSubobject S.f` in `S.X₂`, naturally in `S`
(`CategoryTheory.ShortComplex.mapInduced_homologyPresentation`), reducing to the identity
presentation when `S.f = 0` and `S.g = 0` (`homologyPresentation_eq_refl_mapIso`).
-/

public section

open CategoryTheory Limits
open TauCeti (SubquotientPresentation)

namespace CategoryTheory.ShortComplex

universe v u

variable {C : Type u} [Category.{v} C]

section

/-- `imageSubobject S.f ≤ kernelSubobject S.g` for any short complex `S`. -/
theorem imageSubobject_le_kernelSubobject [HasZeroMorphisms C] (S : ShortComplex C)
    [HasImage S.f] [HasEqualizers C] [HasKernel S.g] :
    imageSubobject S.f ≤ kernelSubobject S.g :=
  le_kernelSubobject S.g _ (imageSubobject_arrow_comp_eq_zero S.zero)

/-- A morphism `φ : S ⟶ S'` maps `kernelSubobject S.g` into `kernelSubobject S'.g`. -/
theorem exists_kernelSubobject_le [HasZeroMorphisms C] [HasImages C] [HasEqualizers C]
    {S S' : ShortComplex C} (φ : S ⟶ S') [HasKernel S.g] [HasKernel S'.g] :
    (Subobject.exists φ.τ₂).obj (kernelSubobject S.g) ≤ kernelSubobject S'.g := by
  rw [Subobject.exists_eq_imageSubobject]
  exact le_kernelSubobject S'.g _ (imageSubobject_arrow_comp_eq_zero
    (by rw [Category.assoc, φ.comm₂₃, kernelSubobject_arrow_comp_assoc, zero_comp]))

/-- A morphism `φ : S ⟶ S'` maps `imageSubobject S.f` into `imageSubobject S'.f`. -/
theorem exists_imageSubobject_le [HasZeroMorphisms C] [HasImages C] [HasImageMaps C]
    {S S' : ShortComplex C} (φ : S ⟶ S') :
    (Subobject.exists φ.τ₂).obj (imageSubobject S.f) ≤ imageSubobject S'.f := by
  rw [Subobject.exists_eq_imageSubobject]
  exact imageSubobject_le _ (imageSubobjectMap (Arrow.homMk (f := Arrow.mk S.f) (g := Arrow.mk S'.f)
    φ.τ₁ φ.τ₂ φ.comm₁₂)) (imageSubobjectMap_arrow _)

end

section Abelian

variable [Abelian C]

section

variable (S : ShortComplex C)

private theorem factorThruImageSubobject_comp_ofLE_comp :
    factorThruImageSubobject S.f ≫
      Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
        S.imageSubobject_le_kernelSubobject ≫
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv = S.toCycles := by
  rw [← cancel_mono S.iCycles]
  simp [cyclesIsoKernel]

/-- `imageSubobject S.f ⟶ kernelSubobject S.g` vanishes upon composition with the homology map. -/
theorem ofLE_comp_homologyPresentation_π :
    Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g) S.imageSubobject_le_kernelSubobject ≫
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ = 0 :=
  zero_of_epi_comp (factorThruImageSubobject S.f)
    (by rw [reassoc_of% (factorThruImageSubobject_comp_ofLE_comp S), S.toCycles_comp_homologyπ])

/-- The cokernel cofork presenting `S.homology` as `kernelSubobject S.g / imageSubobject S.f`. -/
noncomputable def homologyIsCokernelOfLE :
    IsColimit (CokernelCofork.ofπ
      ((kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ)
      S.ofLE_comp_homologyPresentation_π) := by
  let e : S.cycles ≅ (kernelSubobject S.g : C) := S.cyclesIsoKernel ≪≫ (kernelSubobjectIso S.g).symm
  have hcomp :
      factorThruImageSubobject S.f ≫
          Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
            S.imageSubobject_le_kernelSubobject =
        S.toCycles ≫ e.hom :=
    (Iso.comp_inv_eq e).mp (by
      simpa [e, Category.assoc] using factorThruImageSubobject_comp_ofLE_comp S)
  have hc : IsColimit (CokernelCofork.ofπ
      ((kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ)
      (by rw [Category.assoc, reassoc_of% (factorThruImageSubobject_comp_ofLE_comp S),
        S.toCycles_comp_homologyπ] :
        (factorThruImageSubobject S.f ≫
          Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
            S.imageSubobject_le_kernelSubobject) ≫
          (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ = 0)) :=
    IsCokernel.ofIso S.toCycles S.homologyIsCokernel _ (Iso.refl S.X₁) e (Iso.refl S.homology)
      (by simpa using hcomp) (by simpa [e] using e.hom_inv_id_assoc S.homologyπ)
  exact isCokernelOfComp (factorThruImageSubobject S.f) _ hc
    S.ofLE_comp_homologyPresentation_π rfl

/-- Canonical presentation of `S.homology` as `kernelSubobject S.g / imageSubobject S.f`. -/
noncomputable abbrev homologyPresentation : SubquotientPresentation S.X₂ S.homology :=
  SubquotientPresentation.ofIsColimit S.imageSubobject_le_kernelSubobject
    ((kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ)
    S.ofLE_comp_homologyPresentation_π S.homologyIsCokernelOfLE

@[reassoc]
theorem homologyPresentation_π :
    S.homologyPresentation.π = (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ :=
  SubquotientPresentation.π_ofIsColimit _ _ _ _

/-- When `S.f = 0` and `S.g = 0`, `S.homologyPresentation` is the identity presentation transported
along `(S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf`. -/
theorem homologyPresentation_eq_refl_mapIso (hf : S.f = 0) (hg : S.g = 0) :
    S.homologyPresentation = (SubquotientPresentation.refl S.X₂).mapIso
      ((S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf) := by
  refine SubquotientPresentation.ext (by simp [hf]) (by simp [hg]) ?_
  calc S.homologyPresentation.π
      = S.homologyPresentation.Z.arrow ≫ (S.cyclesIsoX₂ hg).inv ≫ S.homologyπ := by
        rw [homologyPresentation_π]
        dsimp only [homologyPresentation, SubquotientPresentation.ofIsColimit]
        rw [← Category.assoc, ← Category.assoc]
        refine congrArg (· ≫ S.homologyπ) ?_
        rw [← cancel_mono S.iCycles]
        simp [cyclesIsoKernel]
    _ = _ := by
        rw [SubquotientPresentation.π_mapIso', SubquotientPresentation.π_refl,
          Subobject.ofLE_comp_ofLE_assoc, Subobject.ofLE_arrow_assoc]
        simp [asIsoHomologyπ]

end

/-- Naturality of `homologyPresentation`: the induced map is `ShortComplex.homologyMap φ`. -/
theorem mapInduced_homologyPresentation {S S' : ShortComplex C} (φ : S ⟶ S') :
    S.homologyPresentation.mapInduced S'.homologyPresentation φ.τ₂
        (exists_kernelSubobject_le φ) (exists_imageSubobject_le φ) =
      ShortComplex.homologyMap φ := by
  symm; refine S.homologyPresentation.mapInduced_unique S'.homologyPresentation φ.τ₂ _ _ ?_
  rw [homologyPresentation_π_assoc, homologyPresentation_π]
  dsimp only [homologyPresentation, SubquotientPresentation.ofIsColimit]
  rw [Category.assoc, Category.assoc, ShortComplex.homologyπ_naturality]
  simp only [← Category.assoc]
  refine congrArg (· ≫ S'.homologyπ) ?_
  rw [← cancel_mono S'.iCycles]
  simp only [cyclesIsoKernel_inv, Category.assoc, liftCycles_comp_cyclesMap, liftCycles_i,
    kernelSubobject_arrow_assoc, kernelSubobject_arrow]
  exact (S.homologyPresentation.liftZ_arrow S'.homologyPresentation φ.τ₂ _).symm

end Abelian

end CategoryTheory.ShortComplex
