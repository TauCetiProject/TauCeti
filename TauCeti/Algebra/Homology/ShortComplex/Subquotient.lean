/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import TauCeti.CategoryTheory.Subobject.Subquotient

/-!
# Homology of a short complex as a subquotient presentation

In an abelian category `C`, the homology `S.homology` of a short complex `S : ShortComplex C` is
canonically presented as the subquotient `kernelSubobject S.g / imageSubobject S.f` of `S.X₂`
(`CategoryTheory.ShortComplex.homologyPresentation`).

* `CategoryTheory.ShortComplex.homologyPresentation`: the subquotient presentation of `S.homology`
  in `S.X₂` with denominator `imageSubobject S.f` and numerator `kernelSubobject S.g`.
* `CategoryTheory.ShortComplex.mapInduced_homologyPresentation`: naturality with respect to
  morphisms `φ : S ⟶ S'` of short complexes, showing that the map induced by `φ.τ₂` on
  `homologyPresentation` is `ShortComplex.homologyMap φ`.
* `CategoryTheory.ShortComplex.homologyPresentation_eq_id_transIso`: when both `S.f = 0` and
  `S.g = 0`, `S.homologyPresentation` is the identity presentation transported along
  `(S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category, `imageSubobject S.f ≤ kernelSubobject S.g` for any short complex `S`. -/
theorem imageSubobject_le_kernelSubobject (S : ShortComplex C) :
    imageSubobject S.f ≤ kernelSubobject S.g :=
  le_kernelSubobject S.g _ (imageSubobject_arrow_comp_eq_zero S.zero)

/-- The inclusion `imageSubobject S.f ⟶ kernelSubobject S.g` vanishes upon composition with the
projection to `S.homology`. -/
theorem ofLE_comp_homologyPresentation_π (S : ShortComplex C) :
    Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g) S.imageSubobject_le_kernelSubobject ≫
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ = 0 := by
  have hfac : factorThruImageSubobject S.f ≫
      Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
        S.imageSubobject_le_kernelSubobject ≫
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv = S.toCycles := by
    rw [← cancel_mono S.iCycles]
    simp [cyclesIsoKernel]
  refine zero_of_epi_comp (factorThruImageSubobject S.f) ?_
  rw [reassoc_of% hfac, S.toCycles_comp_homologyπ]

/-- The cokernel cofork presenting `S.homology` as the quotient of `kernelSubobject S.g` by
`imageSubobject S.f` is a colimit. -/
noncomputable def homologyIsCokernelOfLE (S : ShortComplex C) :
    IsColimit (CokernelCofork.ofπ
      ((kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ)
      S.ofLE_comp_homologyPresentation_π) := by
  let e : (kernelSubobject S.g : C) ≅ S.cycles :=
    kernelSubobjectIso S.g ≪≫ S.cyclesIsoKernel.symm
  have hfac : factorThruImageSubobject S.f ≫
      Subobject.ofLE (imageSubobject S.f) (kernelSubobject S.g)
        S.imageSubobject_le_kernelSubobject ≫ e.hom = S.toCycles := by
    rw [← cancel_mono S.iCycles]
    simp [e, cyclesIsoKernel]
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} k hk ↦ S.descHomology (e.inv ≫ k) (by
      rw [← hfac, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hk, comp_zero]))
    (fun {W} k hk ↦ by
      simp only [Category.assoc, S.π_descHomology]
      simpa [e] using Iso.hom_inv_id_assoc e k)
    (fun {W} k hk m hm ↦ by
      have : Epi ((kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ) :=
        inferInstance
      refine (cancel_epi ((kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ)).mp ?_
      rw [hm]
      simp only [Category.assoc, S.π_descHomology]
      exact (by simpa [e] using Iso.hom_inv_id_assoc e k : _ = k).symm)

/-- The canonical subquotient presentation of `S.homology` inside `S.X₂`, with denominator
`imageSubobject S.f` and numerator `kernelSubobject S.g`. -/
noncomputable abbrev homologyPresentation (S : ShortComplex C) :
    TauCeti.SubquotientPresentation S.X₂ S.homology :=
  TauCeti.SubquotientPresentation.ofIsColimit
    S.imageSubobject_le_kernelSubobject
    ((kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ)
    S.ofLE_comp_homologyPresentation_π
    S.homologyIsCokernelOfLE

@[reassoc]
theorem homologyPresentation_π (S : ShortComplex C) :
    S.homologyPresentation.π =
      (kernelSubobjectIso S.g).hom ≫ S.cyclesIsoKernel.inv ≫ S.homologyπ :=
  TauCeti.SubquotientPresentation.ofIsColimit_π _ _ _ _

/-- A morphism `φ : S ⟶ S'` of short complexes maps `kernelSubobject S.g` into
`kernelSubobject S'.g`. -/
theorem exists_kernelSubobject_le {S S' : ShortComplex C} (φ : S ⟶ S') :
    (Subobject.exists φ.τ₂).obj (kernelSubobject S.g) ≤ kernelSubobject S'.g := by
  rw [Subobject.exists_eq_imageSubobject]
  exact le_kernelSubobject S'.g _ (imageSubobject_arrow_comp_eq_zero (by
    rw [Category.assoc, φ.comm₂₃, kernelSubobject_arrow_comp_assoc, zero_comp]))

/-- A morphism `φ : S ⟶ S'` of short complexes maps `imageSubobject S.f` into
`imageSubobject S'.f`. -/
theorem exists_imageSubobject_le {S S' : ShortComplex C} (φ : S ⟶ S') :
    (Subobject.exists φ.τ₂).obj (imageSubobject S.f) ≤ imageSubobject S'.f := by
  rw [Subobject.exists_obj_imageSubobject, ← φ.comm₁₂]
  exact imageSubobject_comp_le φ.τ₁ S'.f

/-- Naturality of `homologyPresentation`: the morphism induced by `φ.τ₂` on homology presentations
is `ShortComplex.homologyMap φ`. -/
theorem mapInduced_homologyPresentation {S S' : ShortComplex C} (φ : S ⟶ S') :
    S.homologyPresentation.mapInduced S'.homologyPresentation φ.τ₂
        (exists_kernelSubobject_le φ) (exists_imageSubobject_le φ) =
      ShortComplex.homologyMap φ := by
  symm
  refine S.homologyPresentation.mapInduced_unique S'.homologyPresentation φ.τ₂ _ _ ?_
  rw [homologyPresentation_π_assoc, homologyPresentation_π, ShortComplex.homologyπ_naturality]
  simp only [← Category.assoc]
  refine congrArg (· ≫ S'.homologyπ) ?_
  rw [← cancel_mono S'.iCycles]
  simp only [cyclesIsoKernel_inv, Category.assoc, liftCycles_comp_cyclesMap, liftCycles_i,
    kernelSubobject_arrow_assoc, kernelSubobject_arrow]
  exact (S.homologyPresentation.liftZ_comp_arrow S'.homologyPresentation φ.τ₂ _).symm

/-- When both differentials of a short complex `S` vanish, `S.homologyPresentation` is the
identity presentation transported along `(S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf`. -/
theorem homologyPresentation_eq_id_transIso (S : ShortComplex C) (hf : S.f = 0) (hg : S.g = 0) :
    S.homologyPresentation =
      (TauCeti.SubquotientPresentation.id S.X₂).transIso
        ((S.cyclesIsoX₂ hg).symm ≪≫ S.asIsoHomologyπ hf) := by
  refine TauCeti.SubquotientPresentation.ext
    ((kernelSubobject_eq_top_iff S.g).mpr hg) ?_
  rw [homologyPresentation_π, TauCeti.SubquotientPresentation.transIso_π,
    TauCeti.SubquotientPresentation.id_π]
  simp only [Iso.trans_hom, Iso.symm_hom, asIsoHomologyπ_hom, ← Category.assoc]
  refine congrArg (· ≫ S.homologyπ) ?_
  rw [← cancel_mono S.iCycles]
  simp [cyclesIsoKernel]

end CategoryTheory.ShortComplex
