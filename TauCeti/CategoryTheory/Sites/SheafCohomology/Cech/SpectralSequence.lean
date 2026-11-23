/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Basic
public import TauCeti.Algebra.Homology.TotalComplex.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.DegreeZero
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Injective
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal

/-!
# The Čech-to-cohomology spectral sequence of a covering of a site

Let `(C, J)` be a site with finite products and a terminal object `T`, let `U` be a family of
objects covering `T` (`CategoryTheory.GrothendieckTopology.CoversTop`), and let `F` be an abelian
sheaf with an injective resolution `0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯`. The Čech double complex `Čᵖ(U, Iᵠ)`
has two filtrations. Its rows `Č(U, Iᵠ)` are exact in positive degrees, since `Iᵠ` is injective
(`TauCeti.CategoryTheory.exactAt_cechComplexFunctor_obj_obj_of_injective`), and have `Iᵠ(T)` in
degree `0`, since `Iᵠ` is a sheaf; so its total complex computes the cohomology of the sections
`I(T)`, which is `Hⁿ(F)`. Its columns `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` are products of the complexes
of sections `I(U (a 0) × ⋯ × U (a p))`, so their cohomology is the group `Čᵖ(U, Hᵏ(F))` of Čech
cochains of the cohomology presheaf `V ↦ Hᵏ(V, F)`. Filtering by Čech degree gives the
Čech-to-cohomology spectral sequence, with first page `Čᵖ(U, Hᵏ(F))`, converging to `Hⁿ(F)`
(Stacks, Section 21.10 (03AV), Lemma 21.10.7).

The spectral sequences of first-quadrant bicomplexes in
`TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Basic` are those of chain complexes. The
double complex of cochain complexes is therefore formed in the opposite category `Aᵒᵖ`
(`TauCeti.CategoryTheory.cechDoubleComplex`), as Mathlib's Čech complex itself is, and every
object of the spectral sequence is the opposite of the expected group. The general part of the file
works with any cochain complex `I` of presheaves with values in an abelian category `A`, assuming
only that the augmented rows `0 ⟶ Iᵠ(T) ⟶ Č(U, Iᵠ)` are exact.

## Main definitions and results

* `TauCeti.CategoryTheory.cechDoubleComplex U I`: the Čech double complex of a cochain complex of
  presheaves, in `Aᵒᵖ`, with the Čech degree as first index.
* `TauCeti.CategoryTheory.cechTotalAugmentation`: the augmentation of its total complex to the
  complex of sections `I(T)`, a quasi-isomorphism when the augmented rows are exact
  (`TauCeti.CategoryTheory.quasiIso_cechTotalAugmentation`).
* `TauCeti.CategoryTheory.cechDoubleComplexSpectralSequence U I`: the spectral sequence of the
  filtration by Čech degree, with its first page
  (`TauCeti.CategoryTheory.cechDoubleComplexSpectralSequenceFirstPageXIso`, and
  `TauCeti.CategoryTheory.cechColumnHomologyIso` with exact products) and its abutment
  (`TauCeti.CategoryTheory.cechDoubleComplexAbutmentIso`).
* `TauCeti.CategoryTheory.cechToCohomologySpectralSequence U R`: the Čech-to-cohomology spectral
  sequence of an injective resolution `R` of an abelian sheaf `F`. Its object at `(-k - 2p, p)` on
  the first page (numbered `2`) is the opposite of `Čᵖ(U, Hᵏ(F))`
  (`TauCeti.CategoryTheory.cechToCohomologyFirstPageXIso`), and its abutment in degree `-n` is the
  opposite of `Hⁿ(F)` (`TauCeti.CategoryTheory.cechToCohomologyAbutmentIso`). Each object
  stabilizes after finitely many pages to a graded piece of the filtration of the abutment, by
  `HomologicalComplex₂.rowFiltrationSpectralSequencePageXIsoEInfty` for
  `(cechDoubleComplex U I).flip`.

The differential of the first page is not identified here with the Čech differential of the
presheaf `Hᵏ(F)`, so the second page is not identified with the Čech cohomology
`Hᵖ(U, Hᵏ(F))`.

## References

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech
  cohomology and cohomology, Lemma 21.10.7 for the spectral sequence.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w v u

namespace TauCeti.CategoryTheory

section General

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type*} [Category* A]
  [Abelian A] [HasProducts.{w} A] {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)

/-- The Čech complex functor of the family `U`, with values in chain complexes in `Aᵒᵖ`: it sends
a presheaf `P` to the opposite of its Čech complex `Č(U, P)`. -/
abbrev cechOpComplexFunctor : (Cᵒᵖ ⥤ A)ᵒᵖ ⥤ ChainComplex Aᵒᵖ ℕ :=
  (cechComplexFunctor U).op ⋙ opFunctor A (ComplexShape.up ℕ)

/-- The Čech complex functor with values in chain complexes in `Aᵒᵖ` is additive. -/
instance instAdditiveCechOpComplexFunctor : (cechOpComplexFunctor (A := A) U).Additive :=
  inferInstanceAs ((cechComplexFunctor U).op ⋙ opFunctor A (ComplexShape.up ℕ)).Additive

/-- The augmentation `P(T) ⟶ Č(U, P)` of the Čech complex (`cechAugmentation`), as a natural
transformation in the presheaf `P`, passed to chain complexes in `Aᵒᵖ`. -/
@[expose] def cechOpAugmentation : cechOpComplexFunctor U ⟶
    ((evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A).op ⋙
      opFunctor A (ComplexShape.up ℕ) :=
  Functor.whiskerRight (NatTrans.op
    { app := fun P ↦ cechAugmentation U hT P
      naturality := fun _ _ α ↦ (cechAugmentation_naturality U hT _ α).symm })
    (opFunctor A (ComplexShape.up ℕ))

/-- **The Čech double complex** of a cochain complex of presheaves `I` for the family `U`: the
first-quadrant bicomplex whose term in bidegree `(p, q)` is the opposite of `Čᵖ(U, Iᵠ)`, the
Čech cochains of degree `p` of the presheaf `Iᵠ`. The first index is the Čech degree, so that the
column `p` is the opposite of the complex `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯`, and the row `q` is the
opposite of the Čech complex `Č(U, Iᵠ)`. It lives in `Aᵒᵖ`, where the cochain complexes become
the chain complexes to which the spectral sequences of first-quadrant bicomplexes apply. -/
@[expose] def cechDoubleComplex (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    HomologicalComplex₂ Aᵒᵖ (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip
    (((cechOpComplexFunctor (A := A) U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (I.op : ChainComplex (Cᵒᵖ ⥤ A)ᵒᵖ ℕ))

/-- The complex of sections `I⁰(T) ⟶ I¹(T) ⟶ ⋯` of a cochain complex of presheaves over `T`. -/
abbrev sectionsCochainComplex (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) : CochainComplex A ℕ :=
  (((evaluation Cᵒᵖ A).obj (op T)).mapHomologicalComplex _).obj I

/-- The functor sending a presheaf `P` to `P(T)`, placed in degree `0` as a chain complex in
`Aᵒᵖ`: the target of `cechOpAugmentation`. -/
abbrev sectionsOpSingleFunctor (T : C) : (Cᵒᵖ ⥤ A)ᵒᵖ ⥤ ChainComplex Aᵒᵖ ℕ :=
  ((evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A).op ⋙
    opFunctor A (ComplexShape.up ℕ)

/-- The functor `sectionsOpSingleFunctor` is additive. -/
instance instAdditiveSectionsOpSingleFunctor (T : C) :
    (sectionsOpSingleFunctor (A := A) T).Additive :=
  inferInstanceAs (((evaluation Cᵒᵖ A).obj (op T) ⋙ CochainComplex.single₀ A).op ⋙
    opFunctor A (ComplexShape.up ℕ)).Additive

/-- The bicomplex whose only nonzero column is the column `0`, the opposite of the complex of
sections `I⁰(T) ⟶ I¹(T) ⟶ ⋯` (up to the identification of a complex placed in degree `0` with
its term in degree `0`). It is the target of the augmentation of the Čech double complex. -/
abbrev cechDoubleComplexTarget (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    HomologicalComplex₂ Aᵒᵖ (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip
    (((sectionsOpSingleFunctor (A := A) T).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (I.op : ChainComplex (Cᵒᵖ ⥤ A)ᵒᵖ ℕ))

/-- The map from the Čech double complex to the bicomplex with the single column `I(T)`, induced
by the augmentations `Iᵠ(T) ⟶ Č(U, Iᵠ)` of the rows. -/
@[expose] def cechDoubleComplexToTarget (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    cechDoubleComplex U I ⟶ cechDoubleComplexTarget T I :=
  (HomologicalComplex₂.flipFunctor _ _ _).map
    ((NatTrans.mapHomologicalComplex (cechOpAugmentation U hT) (ComplexShape.down ℕ)).app
      (I.op : ChainComplex (Cᵒᵖ ⥤ A)ᵒᵖ ℕ))

/-- The identification of the column `0` of `cechDoubleComplexTarget T I` with the opposite of the
complex of sections `I(T)`. -/
@[expose] def cechDoubleComplexTargetXZeroIso (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplexTarget T I).X 0 ≅ ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
      ((I.X q).obj (op T))).symm.op)
    (fun q q' _ ↦ by simp)

omit [HasFiniteProducts C] [HasProducts.{w} A] in
/-- The columns `p + 1` of `cechDoubleComplexTarget T I` vanish. -/
lemma isZero_cechDoubleComplexTarget_X_X (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p q : ℕ) :
    IsZero (((cechDoubleComplexTarget T I).X (p + 1)).X q) :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).op

omit [HasFiniteProducts C] [HasProducts.{w} A] in
/-- The horizontal differential out of the column `1` of `cechDoubleComplexTarget T I` vanishes. -/
lemma cechDoubleComplexTarget_d_one_zero (T : C) (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplexTarget T I).d 1 0 = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun q ↦ ?_
  exact (isZero_cechDoubleComplexTarget_X_X T I 0 q).eq_of_src _ _

/-- The augmentation of the column `0` of the Čech double complex: in degree `q` it is the opposite
of the augmentation `Iᵠ(T) ⟶ Č⁰(U, Iᵠ)`, restricting a section over `T` to the members of `U`. -/
@[expose] def cechDoubleComplexAugmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplex U I).X 0 ⟶ ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  (cechDoubleComplexToTarget U hT I).f 0 ≫ (cechDoubleComplexTargetXZeroIso T I).hom

/-- The augmentation of the column `0` vanishes on the image of the horizontal differential. -/
lemma cechDoubleComplex_d_comp_augmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplex U I).d 1 0 ≫ cechDoubleComplexAugmentation U hT I = 0 := by
  rw [cechDoubleComplexAugmentation, ← Category.assoc, ← (cechDoubleComplexToTarget U hT I).comm,
    cechDoubleComplexTarget_d_one_zero, comp_zero, zero_comp]

/-- **The augmentation of the total Čech complex.** The map from the total complex of the Čech
double complex of `I` to the opposite of the complex of sections `I(T)`, induced by the
augmentations of the Čech complexes `Č(U, Iᵠ)`. -/
@[expose] def cechTotalAugmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    (cechDoubleComplex U I).total (ComplexShape.down ℕ) ⟶
      ((sectionsCochainComplex T I).op : ChainComplex Aᵒᵖ ℕ) :=
  (cechDoubleComplex U I).totalAugmentation (cechDoubleComplexAugmentation U hT I)
    (cechDoubleComplex_d_comp_augmentation U hT I)

/-- **The total Čech complex computes the cohomology of the sections.** If the augmented Čech
complex `0 ⟶ Iᵠ(T) ⟶ Č(U, Iᵠ)` is exact for every `q`, then the augmentation of the total
complex of the Čech double complex is a quasi-isomorphism. -/
theorem quasiIso_cechTotalAugmentation (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (hI : ∀ q, QuasiIso (cechAugmentation U hT (I.X q))) :
    QuasiIso (cechTotalAugmentation U hT I) := by
  have : QuasiIso (HomologicalComplex₂.total.map (cechDoubleComplexToTarget U hT I)
      (ComplexShape.down ℕ)) := by
    refine HomologicalComplex₂.quasiIso_total_map_of_rows _ fun q ↦ ?_
    change QuasiIso ((opFunctor A (ComplexShape.up ℕ)).map (cechAugmentation U hT (I.X q)).op)
    rw [quasiIso_opFunctor_map_iff]
    exact hI q
  have := HomologicalComplex₂.isIso_totalAugmentation_of_isZero (cechDoubleComplexTarget T I)
    (cechDoubleComplexTargetXZeroIso T I).hom
    ((cechDoubleComplexTarget_d_one_zero T I).symm ▸ zero_comp)
    (isZero_cechDoubleComplexTarget_X_X T I)
  rw [show cechTotalAugmentation U hT I = _ from
    (HomologicalComplex₂.total_map_totalAugmentation _ (cechDoubleComplexToTarget U hT I) _
      ((cechDoubleComplexTarget_d_one_zero T I).symm ▸ zero_comp)).symm]
  infer_instance

/-- The column `p` of the Čech double complex, before passing to `Aᵒᵖ`: the complex
`Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` of Čech cochains of degree `p`. -/
abbrev cechColumn (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p : ℕ) : CochainComplex A ℕ :=
  ((cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I

/-- **The spectral sequence of the Čech double complex**, filtered by Čech degree. Its first page
is the cohomology of the columns `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯`
(`cechDoubleComplexSpectralSequenceFirstPageXIso`), and it converges to the cohomology of the
total complex, which is that of the sections `I(T)` when the rows are exact
(`cechDoubleComplexAbutmentIso`). It is a spectral sequence in `Aᵒᵖ`. -/
abbrev cechDoubleComplexSpectralSequence (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :=
  (cechDoubleComplex U I).columnFiltrationSpectralSequence

/-- The spectral object of the filtration of the total Čech complex by Čech degree, whose
abutment the spectral sequence `cechDoubleComplexSpectralSequence U I` converges to. -/
abbrev cechDoubleComplexSpectralObject (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :=
  (cechDoubleComplex U I).flip.rowFiltrationSpectralObject

/-- The object at `(-k - 2p, p)` on the first page (numbered `2`) of the spectral sequence of the
Čech double complex is the opposite of the cohomology in degree `k` of the column
`Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯`. -/
@[expose] def cechDoubleComplexSpectralSequenceFirstPageXIso (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (p k : ℕ) :
    ((cechDoubleComplexSpectralSequence U I).page 2).X (-(k : ℤ) - 2 * p, p) ≅
      op ((cechColumn U I p).homology k) :=
  (cechDoubleComplex U I).columnFiltrationSpectralSequenceFirstPageXIso p k ≪≫
    homologyOp (cechColumn U I p) k

/-- The abutment in degree `-n` of the spectral sequence of the Čech double complex is the
opposite of the cohomology in degree `n` of the complex of sections `I(T)`, when the augmented
rows `0 ⟶ Iᵠ(T) ⟶ Č(U, Iᵠ)` are exact. -/
@[expose] def cechDoubleComplexAbutmentIso (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (hI : ∀ q, QuasiIso (cechAugmentation U hT (I.X q))) (n : ℕ) :
    (cechDoubleComplexSpectralObject U I).abutment (-n) ≅
      op ((sectionsCochainComplex T I).homology n) :=
  have := quasiIso_cechTotalAugmentation U hT I hI
  (cechDoubleComplex U I).columnFiltrationAbutmentIso n ≪≫
    asIso (homologyMap (cechTotalAugmentation U hT I) n) ≪≫
    homologyOp (sectionsCochainComplex T I) n

section ExactProducts

variable [∀ n : ℕ, HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]

/-- With exact products, the cohomology of the column `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` in degree `k`
is the module of Čech cochains of degree `p` of the cohomology presheaf `Hᵏ(I)` of `I`. -/
@[expose] def cechColumnHomologyIso (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (p k : ℕ) :
    (cechColumn U I p).homology k ≅ ((cechComplexFunctor U).obj (I.homology k)).X p :=
  (I.sc k).mapHomologyIso (cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) p)

end ExactProducts

end General

section Sheaf

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] {ι : Type v} (U : ι → C) {T : C} (hT : IsTerminal T)
  (hU : J.CoversTop U) {F : Sheaf J AddCommGrpCat.{v}} (R : InjectiveResolution F)

/-- The cochain complex of presheaves underlying an injective resolution of an abelian sheaf. -/
abbrev resolutionPresheafComplex : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  ((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj R.cocomplex

include hU in
/-- For a covering family `U`, the augmented Čech complexes `0 ⟶ Iᵠ(T) ⟶ Č(U, Iᵠ)` of the terms
of an injective resolution are exact: the terms are sheaves, and injective. -/
theorem quasiIso_cechAugmentation_resolutionPresheafComplex_X (q : ℕ) :
    QuasiIso (cechAugmentation U hT ((resolutionPresheafComplex R).X q)) :=
  (quasiIso_cechAugmentation_iff U hT _).2
    ⟨isSheafFor_ofArrows_of_coversTop U hT hU (R.cocomplex.X q),
      exactAt_cechComplexFunctor_obj_obj_of_injective U (R.cocomplex.X q)⟩

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- The sections over the terminal object `T` of an injective resolution of `F` compute the
sheaf cohomology `Hⁿ(F)`. -/
@[expose] def sectionsCochainComplexHomologyIsoH (n : ℕ) :
    (sectionsCochainComplex T (resolutionPresheafComplex R)).homology n ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} F n) :=
  (_root_.CategoryTheory.Sheaf.H'.addEquivHomologyOfResolution (R.ι.f 0)
    R.ι_f_zero_comp_complex_d R.exact₀ R.cocomplex_exactAt_succ T
    (fun j k ↦ Abelian.Ext.subsingleton_of_injective _ (R.cocomplex.X j) k)
    n).toAddCommGrpIso.symm ≪≫ F.cohomologyPresheafObjIsoH n hT

/-- **The Čech-to-cohomology spectral sequence** of a covering family `U` and an abelian sheaf
`F`, built from an injective resolution `R` of `F`. Its first page is the cohomology of the
columns `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` of the Čech double complex of `R`, and it converges to the
sheaf cohomology `Hⁿ(F)` (`cechToCohomologyAbutmentIso`). -/
abbrev cechToCohomologySpectralSequence :=
  cechDoubleComplexSpectralSequence U (resolutionPresheafComplex R)

include hU in
/-- The abutment in degree `-n` of the Čech-to-cohomology spectral sequence is the opposite of the
sheaf cohomology `Hⁿ(F)`. -/
@[expose] def cechToCohomologyAbutmentIso (n : ℕ) :
    (cechDoubleComplexSpectralObject U (resolutionPresheafComplex R)).abutment (-n) ≅
      op (AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} F n)) :=
  cechDoubleComplexAbutmentIso U hT (resolutionPresheafComplex R)
    (quasiIso_cechAugmentation_resolutionPresheafComplex_X U hT hU R) n ≪≫
    (sectionsCochainComplexHomologyIsoH hT R n).symm.op

/-- **The first page of the Čech-to-cohomology spectral sequence.** Its object at `(-k - 2p, p)`
(the first page being numbered `2`) is the opposite of the group `Čᵖ(U, Hᵏ(F))` of Čech cochains
of degree `p` of the cohomology presheaf `V ↦ Hᵏ(V, F)`. -/
@[expose] def cechToCohomologyFirstPageXIso (p k : ℕ) :
    ((cechToCohomologySpectralSequence U R).page 2).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor U).obj (F.cohomologyPresheaf k)).X p) :=
  cechDoubleComplexSpectralSequenceFirstPageXIso U (resolutionPresheafComplex R) p k ≪≫
    (cechColumnHomologyIso U (resolutionPresheafComplex R) p k ≪≫
      (cechComplexFunctor U ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p).mapIso
        (_root_.CategoryTheory.Sheaf.H'.homologyIsoCohomologyPresheaf (R.ι.f 0)
          R.ι_f_zero_comp_complex_d R.exact₀ R.cocomplex_exactAt_succ
          (fun _ j k ↦ Abelian.Ext.subsingleton_of_injective _ (R.cocomplex.X j) k) k)).symm.op

end Sheaf

end TauCeti.CategoryTheory
