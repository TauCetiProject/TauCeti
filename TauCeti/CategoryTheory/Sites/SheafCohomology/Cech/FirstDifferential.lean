/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.FirstDifferential
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.SpectralSequence

/-!
# The first differential of the Čech-to-cohomology spectral sequence

Let `U` be a family of objects of a site and `F` an abelian sheaf with an injective resolution
`I`. The first page (numbered `2`) of the Čech-to-cohomology spectral sequence has the Čech
cochains `Čᵖ(U, Hᵏ(F))` of the cohomology presheaf `V ↦ Hᵏ(V, F)` as objects
(`TauCeti.CategoryTheory.cechToCohomologyFirstPageXIso`). This file identifies its differential:
up to the sign `(-1)^k`, it is the Čech differential `Čᵖ(U, Hᵏ(F)) ⟶ Čᵖ⁺¹(U, Hᵏ(F))` of the
presheaf `Hᵏ(F)` (`TauCeti.CategoryTheory.cechToCohomologySpectralSequence_page_two_d`), so that
the rows of the first page are, up to sign, the Čech complexes `Č(U, Hᵏ(F))` (Stacks,
Lemma 21.10.6 (03AZ)).

This goes in two steps, for any cochain complex `I` of presheaves with values in an abelian
category with products, using the map `TauCeti.CategoryTheory.cechColumnD U I p` from the column
`p` of the Čech double complex to the column `p + 1` given by the Čech differentials of the terms
of `I`.

* The first differential of the spectral sequence of the Čech double complex is, up to the sign
  `(-1)^k`, the map induced by `cechColumnD U I p` on cohomology
  (`TauCeti.CategoryTheory.presheafCechDoubleComplexSpectralSequence_page_two_d`), from the first
  differential of the column filtration
  (`HomologicalComplex₂.columnFiltrationSpectralSequence_page_two_d`).
* With exact products, the map induced by `cechColumnD U I p` on cohomology is the Čech
  differential of the cohomology presheaf of `I`
  (`TauCeti.CategoryTheory.presheafCechColumnHomologyIso_inv_comp_homologyMap_cechColumnD`); the
  same holds after transport along an isomorphism of `Hᵏ(I)` with a presheaf `P`
  (`TauCeti.CategoryTheory.presheafCechDoubleComplexSpectralSequence_page_two_d_comp_iso`), under
  the identification of the first page with the Čech cochains of `P`
  (`TauCeti.CategoryTheory.presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso`). For an
  injective resolution of `F`, `P` is the cohomology presheaf of `F`.

The objects of the second page are identified with the Čech cohomology groups of `U` with
coefficients in `Hᵏ(F)`, the cohomology of the Čech complexes `Č(U, Hᵏ(F))`, in
`TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.SecondPage`.

## References

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech
  cohomology and cohomology, Lemma 21.10.6 (tag 03AZ) for the spectral sequence.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w v u

namespace TauCeti.CategoryTheory

section General

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type*} [Category* A]
  [Abelian A] [HasProducts.{w} A] {ι : Type w} (U : ι → C)

/-- **The first differential of the spectral sequence of the Čech double complex.** Under the
identifications `presheafCechDoubleComplexSpectralSequenceFirstPageXIso` of the first page with
the cohomology of the columns, the differential from `(-k - 2(p + 1), p + 1)` to `(-k - 2p, p)` is
`(-1)^k` times the opposite of the map induced on cohomology in degree `k` by the Čech
differentials `cechColumnD U I p`. -/
theorem presheafCechDoubleComplexSpectralSequence_page_two_d (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (p k : ℕ) :
    (presheafCechDoubleComplexSpectralSequenceFirstPageXIso U I (p + 1) k).inv ≫
      ((presheafCechDoubleComplexSpectralSequence U I).page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (presheafCechDoubleComplexSpectralSequenceFirstPageXIso U I p k).hom =
    ((-1 : ℤ) ^ k) • (homologyMap (cechColumnD U I p) k).op := by
  have h := (presheafCechDoubleComplex U I).columnFiltrationSpectralSequence_page_two_d p k
  rw [Iso.inv_comp_eq] at h
  -- The differential of the double complex is the opposite of `cechColumnD U I p`.
  have hd : homologyMap ((presheafCechDoubleComplex U I).d (p + 1) p) k ≫
      (homologyOp (cechColumn U I p) k).hom =
      (homologyOp (cechColumn U I (p + 1)) k).hom ≫ (homologyMap (cechColumnD U I p) k).op := by
    rw [presheafCechDoubleComplex_d_eq]
    exact homologyOp_hom_naturality _ _
  have hds := (Preadditive.zsmul_comp _ _ _).trans
    ((congrArg ((-1 : ℤ) ^ k • ·) hd).trans (Preadditive.comp_zsmul _ _ _).symm)
  rw [Iso.inv_comp_eq, presheafCechDoubleComplexSpectralSequenceFirstPageXIso_hom,
    presheafCechDoubleComplexSpectralSequenceFirstPageXIso_hom]
  exact ((reassoc_of% h) _).trans ((_ ≫= hds).trans (Category.assoc _ _ _).symm)

/-- **The first differential on Čech cochains of a presheaf isomorphic to the cohomology.** With
exact products, under the identifications
`presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso` of the first page of the spectral
sequence of the Čech double complex with the Čech cochains of a presheaf `P` isomorphic to the
cohomology presheaf `Hᵏ(I)`, the differential from `(-k - 2(p + 1), p + 1)` to `(-k - 2p, p)` is
`(-1)^k` times the opposite of the Čech differential of `P`. -/
theorem presheafCechDoubleComplexSpectralSequence_page_two_d_comp_iso
    (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ)
    [HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) A]
    [HasExactLimitsOfShape (Discrete (Fin (p + 1 + 1) → ι)) A] (k : ℕ) {P : Cᵒᵖ ⥤ A}
    (e : I.homology k ≅ P) :
    ((presheafCechDoubleComplexSpectralSequence U I).page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I p k e).hom =
    (presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso U I (p + 1) k e).hom ≫
      (((-1 : ℤ) ^ k) • (((cechComplexFunctor U).obj P).d p (p + 1)).op) := by
  rw [presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso_hom,
    presheafCechDoubleComplexSpectralSequenceFirstPageXIsoOfIso_hom]
  have h := presheafCechDoubleComplexSpectralSequence_page_two_d U I p k
  rw [Iso.inv_comp_eq] at h
  have hcol := presheafCechColumnHomologyIso_inv_comp_homologyMap_cechColumnD U I p k
  rw [← Category.assoc, ← Iso.eq_comp_inv] at hcol
  have key : ((cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p).map
        e.inv ≫ (presheafCechColumnHomologyIso U I p k).inv) ≫
        homologyMap (cechColumnD U I p) k =
      ((cechComplexFunctor U).obj P).d p (p + 1) ≫
        ((cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) (p + 1)).map
          e.inv ≫ (presheafCechColumnHomologyIso U I (p + 1) k).inv) := by
    have hnat := ((cechComplexFunctor U).map e.inv).comm p (p + 1) =≫
      (presheafCechColumnHomologyIso U I (p + 1) k).inv
    rw [Category.assoc, hcol]
    simp only [Category.assoc] at hnat ⊢
    exact hnat
  rw [reassoc_of% h, Category.assoc, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Preadditive.comp_zsmul, ← op_comp, ← op_comp, key, Preadditive.comp_zsmul]

end General

section Sheaf

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] {ι : Type v} (U : ι → C)
  {F : Sheaf J AddCommGrpCat.{v}} (R : InjectiveResolution F)
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- **The first differential of the Čech-to-cohomology spectral sequence.** Under the
identifications `cechToCohomologyFirstPageXIso` of the first page with the Čech cochains of the
cohomology presheaves `V ↦ Hᵏ(V, F)`, the differential from `(-k - 2(p + 1), p + 1)` to
`(-k - 2p, p)` is `(-1)^k` times the opposite of the Čech differential
`Čᵖ(U, Hᵏ(F)) ⟶ Čᵖ⁺¹(U, Hᵏ(F))`. -/
theorem cechToCohomologySpectralSequence_page_two_d (p k : ℕ) :
    (cechToCohomologyFirstPageXIso U R (p + 1) k).inv ≫
      ((cechToCohomologySpectralSequence U R).page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (cechToCohomologyFirstPageXIso U R p k).hom =
    ((-1 : ℤ) ^ k) • (((cechComplexFunctor U).obj (F.cohomologyPresheaf k)).d p (p + 1)).op := by
  rw [Iso.inv_comp_eq, cechToCohomologyFirstPageXIso_hom, cechToCohomologyFirstPageXIso_hom]
  exact presheafCechDoubleComplexSpectralSequence_page_two_d_comp_iso U R.presheafComplex p k _

end Sheaf

end TauCeti.CategoryTheory
