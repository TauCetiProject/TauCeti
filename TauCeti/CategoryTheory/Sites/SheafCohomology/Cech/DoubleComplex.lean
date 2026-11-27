/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import TauCeti.Algebra.Homology.TotalComplex.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact

/-!
# The Čech double complex of a complex of presheaves

Let `C` be a category with finite products and a terminal object `T`, let `U` be a family of
objects of `C`, and let `I` be a cochain complex of presheaves on `C` with values in a preadditive
category `A` with products. The Čech double complex `Čᵖ(U, Iᵠ)` has the Čech complexes `Č(U, Iᵠ)`
as rows and the complexes `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` as columns.

The spectral sequences of first-quadrant bicomplexes in
`TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Basic` are those of chain complexes. The
double complex of cochain complexes is therefore formed in the opposite category `Aᵒᵖ`
(`TauCeti.CategoryTheory.presheafCechDoubleComplex`), as Mathlib's Čech complex itself is.

The augmentations `Iᵠ(T) ⟶ Č(U, Iᵠ)` of the rows induce an augmentation of the total complex to
the complex of sections `I(T)` (`TauCeti.CategoryTheory.presheafCechTotalAugmentation`, which
needs a zero object in `A` and the total complex). When `A` is abelian and the augmented rows are
exact, it is a quasi-isomorphism (`TauCeti.CategoryTheory.quasiIso_presheafCechTotalAugmentation`).
When `A` is abelian and products of the shape of Čech degree `p` are exact, the cohomology of the
column `p` is the object of Čech cochains of degree `p` of the cohomology presheaves of `I`
(`TauCeti.CategoryTheory.presheafCechColumnHomologyIso`). The Čech differentials of the terms of
`I` form a map from the column `p` to the column `p + 1`
(`TauCeti.CategoryTheory.cechColumnD`), whose opposite is the differential of the double complex
(`TauCeti.CategoryTheory.presheafCechDoubleComplex_d_eq`); under these identifications, the map it
induces on cohomology is the Čech differential of the cohomology presheaf
(`TauCeti.CategoryTheory.presheafCechColumnHomologyIso_inv_comp_homologyMap_cechColumnD`).

## Main definitions

* `TauCeti.CategoryTheory.presheafCechDoubleComplex U I`: the Čech double complex of a cochain
  complex of presheaves, in `Aᵒᵖ`, with the Čech degree as first index.
* `TauCeti.CategoryTheory.presheafCechTotalAugmentation`: the augmentation of its total complex to
  the complex of sections `I(T)`.
* `TauCeti.CategoryTheory.cechColumnD U I p`: the map from the column `p` to the column `p + 1`
  given by the Čech differentials.

## Main results

* `TauCeti.CategoryTheory.quasiIso_presheafCechTotalAugmentation`: the augmentation of the total
  complex is a quasi-isomorphism when the augmented rows are exact.
* `TauCeti.CategoryTheory.presheafCechColumnHomologyIso`: with exact products, the cohomology of a
  column is the object of Čech cochains of the cohomology presheaf.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type*} [Category* A]
  {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)

section Preadditive

variable [Preadditive A] [HasProducts.{w} A]

/-- The Čech complex functor of the family `U`, with values in chain complexes in `Aᵒᵖ`: it sends
a presheaf `P` to the opposite of its Čech complex `Č(U, P)`. -/
abbrev cechOpComplexFunctor : (Cᵒᵖ ⥤ A)ᵒᵖ ⥤ ChainComplex Aᵒᵖ ℕ :=
  (cechComplexFunctor U).op ⋙ opFunctor A (ComplexShape.up ℕ)

/-- The Čech complex functor with values in chain complexes in `Aᵒᵖ` is additive. Instance
synthesis does not unfold the abbreviation to find Mathlib's instance for the composite. -/
instance instAdditiveCechOpComplexFunctor : (cechOpComplexFunctor (A := A) U).Additive :=
  inferInstanceAs ((cechComplexFunctor U).op ⋙ opFunctor A (ComplexShape.up ℕ)).Additive

/-- **The Čech double complex** of a cochain complex of presheaves `I` for the family `U`: the
first-quadrant bicomplex whose term in bidegree `(p, q)` is the opposite of `Čᵖ(U, Iᵠ)`, the
Čech cochains of degree `p` of the presheaf `Iᵠ` (`presheafCechDoubleComplex_X_X`). The first
index is the Čech degree, so that the column `p` is the opposite of the complex
`Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯`, and the row `q` is the opposite of the Čech complex `Č(U, Iᵠ)`. It
lives in `Aᵒᵖ`, where the cochain complexes become the chain complexes to which the spectral
sequences of first-quadrant bicomplexes apply. Its body is exposed so that its terms unfold to
Čech cochains in statements. -/
@[expose] def presheafCechDoubleComplex (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    HomologicalComplex₂ Aᵒᵖ (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip
    (((cechOpComplexFunctor (A := A) U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (I.op : ChainComplex (Cᵒᵖ ⥤ A)ᵒᵖ ℕ))

/-- The term of the Čech double complex in bidegree `(p, q)` is the opposite of `Čᵖ(U, Iᵠ)`. -/
lemma presheafCechDoubleComplex_X_X (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p q : ℕ) :
    ((presheafCechDoubleComplex U I).X p).X q = op (((cechComplexFunctor U).obj (I.X q)).X p) :=
  (rfl)

/-- The differential of the Čech double complex in the Čech direction is the opposite of the
Čech differential of `Č(U, Iᵠ)`. -/
@[simp]
lemma presheafCechDoubleComplex_d_f (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p p' q : ℕ) :
    ((presheafCechDoubleComplex U I).d p p').f q =
      (((cechComplexFunctor U).obj (I.X q)).d p' p).op :=
  (rfl)

/-- The differential of the Čech double complex in the direction of `I` is the opposite of the
map of Čech cochains induced by the differential of `I`. -/
@[simp]
lemma presheafCechDoubleComplex_X_d (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p q q' : ℕ) :
    ((presheafCechDoubleComplex U I).X p).d q q' =
      (((cechComplexFunctor U).map (I.d q' q)).f p).op :=
  (rfl)

/-- The complex of sections `I⁰(T) ⟶ I¹(T) ⟶ ⋯` of a cochain complex of presheaves over `T`. -/
abbrev sectionsCochainComplex (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) : CochainComplex A ℕ :=
  (((evaluation Cᵒᵖ A).obj (op T)).mapHomologicalComplex _).obj I

/-- The column `p` of the Čech double complex, before passing to `Aᵒᵖ`: the complex
`Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` of Čech cochains of degree `p`. -/
abbrev cechColumn (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ) : CochainComplex A ℕ :=
  ((cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I

/-- The map from the column `p` of the Čech double complex, before passing to `Aᵒᵖ`, to the
column `p + 1`, given by the Čech differentials `Čᵖ(U, Iᵠ) ⟶ Čᵖ⁺¹(U, Iᵠ)` of the presheaves
`Iᵠ`. -/
abbrev cechColumnD (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ) :
    cechColumn U I p ⟶ cechColumn U I (p + 1) :=
  (NatTrans.mapHomologicalComplex (Functor.whiskerLeft (cechComplexFunctor U)
    (HomologicalComplex.dNatTrans A (ComplexShape.up ℕ) p (p + 1))) (ComplexShape.up ℕ)).app I

/-- The component of `cechColumnD U I p` in degree `q` is the Čech differential of `Iᵠ`. -/
lemma cechColumnD_f (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p q : ℕ) :
    (cechColumnD U I p).f q = ((cechComplexFunctor U).obj (I.X q)).d p (p + 1) :=
  (rfl)

/-- The differential of the Čech double complex from the column `p + 1` to the column `p` is the
opposite of `cechColumnD U I p`. -/
lemma presheafCechDoubleComplex_d_eq (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ) :
    (presheafCechDoubleComplex U I).d (p + 1) p =
      (opFunctor A (ComplexShape.up ℕ)).map (cechColumnD U I p).op := by
  ext q
  rfl

section Augmentation

variable [HasZeroObject A]

/-- The augmentation `P(T) ⟶ Č(U, P)` of the Čech complex, as a natural transformation in the
presheaf `P`, passed to chain complexes in `Aᵒᵖ`. -/
private def cechOpAugmentation : cechOpComplexFunctor U ⟶
    ((evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A).op ⋙
      opFunctor A (ComplexShape.up ℕ) :=
  Functor.whiskerRight (NatTrans.op (cechAugmentationNatTrans U hT))
    (opFunctor A (ComplexShape.up ℕ))

/-- The functor sending a presheaf `P` to `P(T)`, placed in degree `0` as a chain complex in
`Aᵒᵖ`: the target of `cechOpAugmentation`. -/
private abbrev sectionsOpSingleFunctor (T : C) : (Cᵒᵖ ⥤ A)ᵒᵖ ⥤ ChainComplex Aᵒᵖ ℕ :=
  ((evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A).op ⋙
    opFunctor A (ComplexShape.up ℕ)

/-- The functor `sectionsOpSingleFunctor` is additive. -/
private instance instAdditiveSectionsOpSingleFunctor (T : C) :
    (sectionsOpSingleFunctor (A := A) T).Additive :=
  inferInstanceAs (((evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A).op ⋙
    opFunctor A (ComplexShape.up ℕ)).Additive

/-- The bicomplex whose only nonzero column is the column `0`, the opposite of the complex of
sections `I⁰(T) ⟶ I¹(T) ⟶ ⋯` (up to the identification of a complex placed in degree `0` with
its term in degree `0`). It is the target of the augmentation of the Čech double complex. -/
private abbrev cechDoubleComplexTarget (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    HomologicalComplex₂ Aᵒᵖ (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip
    (((sectionsOpSingleFunctor (A := A) T).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (I.op : ChainComplex (Cᵒᵖ ⥤ A)ᵒᵖ ℕ))

/-- The map from the Čech double complex to the bicomplex with the single column `I(T)`, induced
by the augmentations `Iᵠ(T) ⟶ Č(U, Iᵠ)` of the rows. -/
private def cechDoubleComplexToTarget (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    presheafCechDoubleComplex U I ⟶ cechDoubleComplexTarget T I :=
  (HomologicalComplex₂.flipFunctor _ _ _).map
    ((NatTrans.mapHomologicalComplex (cechOpAugmentation U hT) (ComplexShape.down ℕ)).app
      (I.op : ChainComplex (Cᵒᵖ ⥤ A)ᵒᵖ ℕ))

/-- The row `q` of `cechDoubleComplexToTarget` is the opposite of the augmentation of the Čech
complex `Č(U, Iᵠ)`. -/
private lemma cechDoubleComplexToTarget_row (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (q : ℕ) :
    ((HomologicalComplex.eval Aᵒᵖ (ComplexShape.down ℕ) q).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (cechDoubleComplexToTarget U hT I) =
      (opFunctor A (ComplexShape.up ℕ)).map ((cechAugmentationNatTrans U hT).app (I.X q)).op :=
  (rfl)

/-- The component of `cechDoubleComplexToTarget` in bidegree `(0, q)` is the opposite of the
degree `0` component of the augmentation of the Čech complex `Č(U, Iᵠ)`. -/
private lemma cechDoubleComplexToTarget_f_zero_f (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (q : ℕ) :
    ((cechDoubleComplexToTarget U hT I).f 0).f q = ((cechAugmentation U hT (I.X q)).f 0).op := by
  rw [← cechAugmentationNatTrans_app]
  rfl

/-- The identification of the column `0` of `cechDoubleComplexTarget T I` with the opposite of the
complex of sections `I(T)`. -/
private def cechDoubleComplexTargetXZeroIso (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplexTarget T I).X 0 ≅ ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
      ((I.X q).obj (op T))).symm.op)
    (fun q q' _ ↦ by simp)

omit [HasFiniteProducts C] [HasProducts.{w} A] in
/-- The component of `cechDoubleComplexTargetXZeroIso T I` in degree `q` is the opposite of the
identification of the degree `0` term of the complex placed in degree `0`. -/
private lemma cechDoubleComplexTargetXZeroIso_hom_f (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (q : ℕ) : (cechDoubleComplexTargetXZeroIso T I).hom.f q =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((I.X q).obj (op T))).inv.op :=
  (rfl)

omit [HasFiniteProducts C] [HasProducts.{w} A] in
/-- The columns `p + 1` of `cechDoubleComplexTarget T I` vanish. -/
private lemma isZero_cechDoubleComplexTarget_X_X (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (p q : ℕ) : IsZero (((cechDoubleComplexTarget T I).X (p + 1)).X q) :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).op

omit [HasFiniteProducts C] [HasProducts.{w} A] in
/-- Any map out of the column `0` of `cechDoubleComplexTarget T I` vanishes after the horizontal
differential out of the column `1`. -/
private lemma cechDoubleComplexTarget_d_one_zero_comp (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    {E : ChainComplex Aᵒᵖ ℕ} (η : (cechDoubleComplexTarget T I).X 0 ⟶ E) :
    (cechDoubleComplexTarget T I).d 1 0 ≫ η = 0 := by
  have : (cechDoubleComplexTarget T I).d 1 0 = 0 :=
    HomologicalComplex.hom_ext _ _ fun q ↦
      (isZero_cechDoubleComplexTarget_X_X T I 0 q).eq_of_src _ _
  rw [this, zero_comp]

/-- The augmentation of the column `0` of the Čech double complex: in degree `q` it is the opposite
of the augmentation `Iᵠ(T) ⟶ Č⁰(U, Iᵠ)`, restricting a section over `T` to the members of `U`
(`presheafCechDoubleComplexAugmentation_f`). -/
def presheafCechDoubleComplexAugmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (presheafCechDoubleComplex U I).X 0 ⟶ ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  (cechDoubleComplexToTarget U hT I).f 0 ≫ (cechDoubleComplexTargetXZeroIso T I).hom

/-- In degree `q`, the augmentation of the column `0` of the Čech double complex is the opposite
of the degree `0` component of the augmentation `Iᵠ(T) ⟶ Č(U, Iᵠ)`. -/
@[simp]
lemma presheafCechDoubleComplexAugmentation_f (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (q : ℕ) :
    (presheafCechDoubleComplexAugmentation U hT I).f q =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((I.X q).obj (op T))).inv ≫
        (cechAugmentation U hT (I.X q)).f 0).op := by
  rw [presheafCechDoubleComplexAugmentation, HomologicalComplex.comp_f,
    cechDoubleComplexToTarget_f_zero_f, cechDoubleComplexTargetXZeroIso_hom_f, op_comp]
  -- the two sides differ only in how the degree `0` term of the single complex is written
  rfl

/-- The augmentation of the column `0` vanishes on the image of the horizontal differential. -/
@[reassoc (attr := simp)]
lemma presheafCechDoubleComplex_d_comp_augmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (presheafCechDoubleComplex U I).d 1 0 ≫ presheafCechDoubleComplexAugmentation U hT I = 0 := by
  rw [presheafCechDoubleComplexAugmentation, ← Category.assoc,
    ← (cechDoubleComplexToTarget U hT I).comm, Category.assoc,
    cechDoubleComplexTarget_d_one_zero_comp, comp_zero]

variable (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
  [(presheafCechDoubleComplex U I).HasTotal (ComplexShape.down ℕ)]

/-- **The augmentation of the total Čech complex.** The map from the total complex of the Čech
double complex of `I` to the opposite of the complex of sections `I(T)`, induced by the
augmentations of the Čech complexes `Č(U, Iᵠ)`: on the summand of Čech degree `0` it is the
augmentation (`ιTotal_presheafCechTotalAugmentation_f_zero`), and it vanishes on the other summands
(`ιTotal_presheafCechTotalAugmentation_f_succ`). -/
def presheafCechTotalAugmentation :
    (presheafCechDoubleComplex U I).total (ComplexShape.down ℕ) ⟶
      ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  (presheafCechDoubleComplex U I).totalAugmentation (presheafCechDoubleComplexAugmentation U hT I)
    (presheafCechDoubleComplex_d_comp_augmentation U hT I)

/-- On the summand `Č⁰(U, Iᵠ)` of the total complex, the augmentation of the total Čech complex
is the opposite of the augmentation `Iᵠ(T) ⟶ Č⁰(U, Iᵠ)`. -/
@[reassoc (attr := simp)]
lemma ιTotal_presheafCechTotalAugmentation_f_zero (q : ℕ) :
    (presheafCechDoubleComplex U I).ιTotal (ComplexShape.down ℕ) 0 q q (zero_add q) ≫
        (presheafCechTotalAugmentation U hT I).f q =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((I.X q).obj (op T))).inv ≫
        (cechAugmentation U hT (I.X q)).f 0).op := by
  rw [presheafCechTotalAugmentation, HomologicalComplex₂.ιTotal_totalAugmentation_f_zero,
    presheafCechDoubleComplexAugmentation_f]

/-- The augmentation of the total Čech complex vanishes on the summands of positive Čech
degree. -/
@[reassoc (attr := simp)]
lemma ιTotal_presheafCechTotalAugmentation_f_succ (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p + 1, q) = n) :
    (presheafCechDoubleComplex U I).ιTotal (ComplexShape.down ℕ) (p + 1) q n h ≫
      (presheafCechTotalAugmentation U hT I).f n = 0 := by
  rw [presheafCechTotalAugmentation, HomologicalComplex₂.ιTotal_totalAugmentation_f_succ]

/-- The augmentation of the total Čech complex factors through the total complex of the bicomplex
with the single column `I(T)`. -/
private lemma presheafCechTotalAugmentation_eq
    [(cechDoubleComplexTarget T I).HasTotal (ComplexShape.down ℕ)] :
    presheafCechTotalAugmentation U hT I =
      HomologicalComplex₂.total.map (cechDoubleComplexToTarget U hT I) (ComplexShape.down ℕ) ≫
        (cechDoubleComplexTarget T I).totalAugmentation (cechDoubleComplexTargetXZeroIso T I).hom
          (cechDoubleComplexTarget_d_one_zero_comp T I _) := by
  rw [presheafCechTotalAugmentation, HomologicalComplex₂.total_map_totalAugmentation]
  -- the two sides agree after unfolding `presheafCechDoubleComplexAugmentation`, which is the
  -- composite of `(cechDoubleComplexToTarget U hT I).f 0` and `cechDoubleComplexTargetXZeroIso`
  rfl

end Augmentation

end Preadditive

variable [Abelian A] [HasProducts.{w} A]

/-- **The total Čech complex computes the cohomology of the sections.** If the augmented Čech
complex `0 ⟶ Iᵠ(T) ⟶ Č(U, Iᵠ)` is exact for every `q`, then the augmentation of the total
complex of the Čech double complex is a quasi-isomorphism. -/
theorem quasiIso_presheafCechTotalAugmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (hI : ∀ q, QuasiIso (cechAugmentation U hT (I.X q))) :
    QuasiIso (presheafCechTotalAugmentation U hT I) := by
  have : QuasiIso (HomologicalComplex₂.total.map (cechDoubleComplexToTarget U hT I)
      (ComplexShape.down ℕ)) := by
    refine HomologicalComplex₂.quasiIso_total_map_of_rows _ fun q ↦ ?_
    rw [cechDoubleComplexToTarget_row, cechAugmentationNatTrans_app]
    exact (quasiIso_opFunctor_map_iff _).2 (hI q)
  have := HomologicalComplex₂.isIso_totalAugmentation_of_isZero (cechDoubleComplexTarget T I)
    (cechDoubleComplexTargetXZeroIso T I).hom (cechDoubleComplexTarget_d_one_zero_comp T I _)
    (isZero_cechDoubleComplexTarget_X_X T I)
  rw [presheafCechTotalAugmentation_eq]
  infer_instance

/-- With exact products of the shape of Čech degree `p`, the cohomology in degree `k` of the
column `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` is the object of Čech cochains of degree `p` in `A` of the
cohomology presheaf `Hᵏ(I)` of `I`. -/
def presheafCechColumnHomologyIso (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ)
    [HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) A] (k : ℕ) :
    (cechColumn U I p).homology k ≅ ((cechComplexFunctor U).obj (I.homology k)).X p :=
  (I.sc k).mapHomologyIso (cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p)

/-- `presheafCechColumnHomologyIso` is the comparison isomorphism
`ShortComplex.mapHomologyIso` for the functor taking a presheaf to its Čech cochains of degree
`p`, applied to the short complex of `I` at `k`. -/
lemma presheafCechColumnHomologyIso_eq (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ)
    [HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) A] (k : ℕ) :
    presheafCechColumnHomologyIso U I p k = (I.sc k).mapHomologyIso
      (cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p) :=
  (rfl)

/-- With exact products, under the identifications `presheafCechColumnHomologyIso` of the
cohomology of the columns of the Čech double complex with Čech cochains of the cohomology presheaf
of `I`, the map induced on cohomology by `cechColumnD U I p` is the Čech differential of the
presheaf `Hᵏ(I)`. -/
theorem presheafCechColumnHomologyIso_inv_comp_homologyMap_cechColumnD
    (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ)
    [HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) A]
    [HasExactLimitsOfShape (Discrete (Fin (p + 1 + 1) → ι)) A] (k : ℕ) :
    (presheafCechColumnHomologyIso U I p k).inv ≫ homologyMap (cechColumnD U I p) k ≫
      (presheafCechColumnHomologyIso U I (p + 1) k).hom =
    ((cechComplexFunctor U).obj (I.homology k)).d p (p + 1) := by
  rw [presheafCechColumnHomologyIso_eq, presheafCechColumnHomologyIso_eq]
  exact (NatTrans.app_homology (Functor.whiskerLeft (cechComplexFunctor U)
    (HomologicalComplex.dNatTrans A (ComplexShape.up ℕ) p (p + 1))) (I.sc k)).symm

end TauCeti.CategoryTheory
