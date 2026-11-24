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
(`TauCeti.CategoryTheory.cechDoubleComplex`), as Mathlib's Čech complex itself is.

The augmentations `Iᵠ(T) ⟶ Č(U, Iᵠ)` of the rows induce an augmentation of the total complex to
the complex of sections `I(T)` (`TauCeti.CategoryTheory.cechTotalAugmentation`, which needs a zero
object in `A` and the total complex). When `A` is abelian and the augmented rows are exact, it is a
quasi-isomorphism (`TauCeti.CategoryTheory.quasiIso_cechTotalAugmentation`). When `A` is abelian
and products of the shape of Čech degree `p` are exact, the cohomology of the column `p` is the
object of Čech cochains of degree `p` of the cohomology presheaves of `I`
(`TauCeti.CategoryTheory.cechColumnHomologyIso`).

## Main definitions

* `TauCeti.CategoryTheory.cechDoubleComplex U I`: the Čech double complex of a cochain complex of
  presheaves, in `Aᵒᵖ`, with the Čech degree as first index.
* `TauCeti.CategoryTheory.cechTotalAugmentation`: the augmentation of its total complex to the
  complex of sections `I(T)`.

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechTotalAugmentation`: the augmentation of the total complex
  is a quasi-isomorphism when the augmented rows are exact.
* `TauCeti.CategoryTheory.cechColumnHomologyIso`: with exact products, the cohomology of a column
  is the object of Čech cochains of the cohomology presheaf.
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
Čech cochains of degree `p` of the presheaf `Iᵠ` (`cechDoubleComplex_X_X`). The first index is
the Čech degree, so that the column `p` is the opposite of the complex
`Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯`, and the row `q` is the opposite of the Čech complex `Č(U, Iᵠ)`. It
lives in `Aᵒᵖ`, where the cochain complexes become the chain complexes to which the spectral
sequences of first-quadrant bicomplexes apply. Its body is exposed so that its terms unfold to
Čech cochains in statements. -/
@[expose] def cechDoubleComplex (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    HomologicalComplex₂ Aᵒᵖ (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip
    (((cechOpComplexFunctor (A := A) U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (I.op : ChainComplex (Cᵒᵖ ⥤ A)ᵒᵖ ℕ))

/-- The term of the Čech double complex in bidegree `(p, q)` is the opposite of `Čᵖ(U, Iᵠ)`. -/
lemma cechDoubleComplex_X_X (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p q : ℕ) :
    ((cechDoubleComplex U I).X p).X q = op (((cechComplexFunctor U).obj (I.X q)).X p) :=
  (rfl)

/-- The differential of the Čech double complex in the Čech direction is the opposite of the
Čech differential of `Č(U, Iᵠ)`. -/
@[simp]
lemma cechDoubleComplex_d_f (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p p' q : ℕ) :
    ((cechDoubleComplex U I).d p p').f q = (((cechComplexFunctor U).obj (I.X q)).d p' p).op :=
  (rfl)

/-- The differential of the Čech double complex in the direction of `I` is the opposite of the
map of Čech cochains induced by the differential of `I`. -/
@[simp]
lemma cechDoubleComplex_X_d (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p q q' : ℕ) :
    ((cechDoubleComplex U I).X p).d q q' = (((cechComplexFunctor U).map (I.d q' q)).f p).op :=
  (rfl)

/-- The complex of sections `I⁰(T) ⟶ I¹(T) ⟶ ⋯` of a cochain complex of presheaves over `T`. -/
abbrev sectionsCochainComplex (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) : CochainComplex A ℕ :=
  (((evaluation Cᵒᵖ A).obj (op T)).mapHomologicalComplex _).obj I

/-- The column `p` of the Čech double complex, before passing to `Aᵒᵖ`: the complex
`Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` of Čech cochains of degree `p`. -/
abbrev cechColumn (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ) : CochainComplex A ℕ :=
  ((cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I

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
    cechDoubleComplex U I ⟶ cechDoubleComplexTarget T I :=
  (HomologicalComplex₂.flipFunctor _ _ _).map
    ((NatTrans.mapHomologicalComplex (cechOpAugmentation U hT) (ComplexShape.down ℕ)).app
      (I.op : ChainComplex (Cᵒᵖ ⥤ A)ᵒᵖ ℕ))

/-- The row `q` of `cechDoubleComplexToTarget` is the opposite of the augmentation of the Čech
complex `Č(U, Iᵠ)`. -/
private lemma cechDoubleComplexToTarget_row (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (q : ℕ) :
    ((HomologicalComplex.eval Aᵒᵖ (ComplexShape.down ℕ) q).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (cechDoubleComplexToTarget U hT I) =
      (opFunctor A (ComplexShape.up ℕ)).map (cechAugmentation U hT (I.X q)).op :=
  (rfl)

/-- The identification of the column `0` of `cechDoubleComplexTarget T I` with the opposite of the
complex of sections `I(T)`. -/
private def cechDoubleComplexTargetXZeroIso (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplexTarget T I).X 0 ≅ ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
      ((I.X q).obj (op T))).symm.op)
    (fun q q' _ ↦ by simp)

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
(`cechDoubleComplexAugmentation_f`). -/
def cechDoubleComplexAugmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplex U I).X 0 ⟶ ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  (cechDoubleComplexToTarget U hT I).f 0 ≫ (cechDoubleComplexTargetXZeroIso T I).hom

/-- In degree `q`, the augmentation of the column `0` of the Čech double complex is the opposite
of the degree `0` component of the augmentation `Iᵠ(T) ⟶ Č(U, Iᵠ)`. -/
@[simp]
lemma cechDoubleComplexAugmentation_f (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (q : ℕ) :
    (cechDoubleComplexAugmentation U hT I).f q =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((I.X q).obj (op T))).inv ≫
        (cechAugmentation U hT (I.X q)).f 0).op := by
  simp only [op_X, Functor.mapHomologicalComplex_obj_X, evaluation_obj_obj,
    CochainComplex.single₀_obj_zero, CochainComplex.single₀ObjXSelf, Iso.refl_inv,
    Category.id_comp]
  exact Category.comp_id ((cechAugmentation U hT (I.X q)).f 0).op

/-- The augmentation of the column `0` vanishes on the image of the horizontal differential. -/
@[reassoc (attr := simp)]
lemma cechDoubleComplex_d_comp_augmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplex U I).d 1 0 ≫ cechDoubleComplexAugmentation U hT I = 0 := by
  rw [cechDoubleComplexAugmentation, ← Category.assoc, ← (cechDoubleComplexToTarget U hT I).comm,
    Category.assoc, cechDoubleComplexTarget_d_one_zero_comp, comp_zero]

variable (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) [(cechDoubleComplex U I).HasTotal (ComplexShape.down ℕ)]

/-- **The augmentation of the total Čech complex.** The map from the total complex of the Čech
double complex of `I` to the opposite of the complex of sections `I(T)`, induced by the
augmentations of the Čech complexes `Č(U, Iᵠ)`: on the summand of Čech degree `0` it is the
augmentation (`ιTotal_cechTotalAugmentation_f_zero`), and it vanishes on the other summands
(`ιTotal_cechTotalAugmentation_f_succ`). -/
def cechTotalAugmentation :
    (cechDoubleComplex U I).total (ComplexShape.down ℕ) ⟶
      ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  (cechDoubleComplex U I).totalAugmentation (cechDoubleComplexAugmentation U hT I)
    (cechDoubleComplex_d_comp_augmentation U hT I)

/-- On the summand `Č⁰(U, Iᵠ)` of the total complex, the augmentation of the total Čech complex
is the opposite of the augmentation `Iᵠ(T) ⟶ Č⁰(U, Iᵠ)`. -/
@[reassoc (attr := simp)]
lemma ιTotal_cechTotalAugmentation_f_zero (q : ℕ) :
    (cechDoubleComplex U I).ιTotal (ComplexShape.down ℕ) 0 q q (zero_add q) ≫
        (cechTotalAugmentation U hT I).f q =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((I.X q).obj (op T))).inv ≫
        (cechAugmentation U hT (I.X q)).f 0).op := by
  rw [cechTotalAugmentation, HomologicalComplex₂.ιTotal_totalAugmentation_f_zero,
    cechDoubleComplexAugmentation_f]

/-- The augmentation of the total Čech complex vanishes on the summands of positive Čech
degree. -/
@[reassoc (attr := simp)]
lemma ιTotal_cechTotalAugmentation_f_succ (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p + 1, q) = n) :
    (cechDoubleComplex U I).ιTotal (ComplexShape.down ℕ) (p + 1) q n h ≫
      (cechTotalAugmentation U hT I).f n = 0 := by
  rw [cechTotalAugmentation, HomologicalComplex₂.ιTotal_totalAugmentation_f_succ]

/-- The augmentation of the total Čech complex factors through the total complex of the bicomplex
with the single column `I(T)`. -/
private lemma cechTotalAugmentation_eq
    [(cechDoubleComplexTarget T I).HasTotal (ComplexShape.down ℕ)] :
    cechTotalAugmentation U hT I =
      HomologicalComplex₂.total.map (cechDoubleComplexToTarget U hT I) (ComplexShape.down ℕ) ≫
        (cechDoubleComplexTarget T I).totalAugmentation (cechDoubleComplexTargetXZeroIso T I).hom
          (cechDoubleComplexTarget_d_one_zero_comp T I _) := by
  rw [cechTotalAugmentation, HomologicalComplex₂.total_map_totalAugmentation]
  rfl

end Augmentation

end Preadditive

variable [Abelian A] [HasProducts.{w} A]

/-- **The total Čech complex computes the cohomology of the sections.** If the augmented Čech
complex `0 ⟶ Iᵠ(T) ⟶ Č(U, Iᵠ)` is exact for every `q`, then the augmentation of the total
complex of the Čech double complex is a quasi-isomorphism. -/
theorem quasiIso_cechTotalAugmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (hI : ∀ q, QuasiIso (cechAugmentation U hT (I.X q))) :
    QuasiIso (cechTotalAugmentation U hT I) := by
  have : QuasiIso (HomologicalComplex₂.total.map (cechDoubleComplexToTarget U hT I)
      (ComplexShape.down ℕ)) := by
    refine HomologicalComplex₂.quasiIso_total_map_of_rows _ fun q ↦ ?_
    rw [cechDoubleComplexToTarget_row]
    exact (quasiIso_opFunctor_map_iff _).2 (hI q)
  have := HomologicalComplex₂.isIso_totalAugmentation_of_isZero (cechDoubleComplexTarget T I)
    (cechDoubleComplexTargetXZeroIso T I).hom (cechDoubleComplexTarget_d_one_zero_comp T I _)
    (isZero_cechDoubleComplexTarget_X_X T I)
  rw [cechTotalAugmentation_eq]
  infer_instance

/-- With exact products of the shape of Čech degree `p`, the cohomology in degree `k` of the
column `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` is the object of Čech cochains of degree `p` in `A` of the
cohomology presheaf `Hᵏ(I)` of `I`. -/
def cechColumnHomologyIso (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ)
    [HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) A] (k : ℕ) :
    (cechColumn U I p).homology k ≅ ((cechComplexFunctor U).obj (I.homology k)).X p :=
  (I.sc k).mapHomologyIso (cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p)

end TauCeti.CategoryTheory
