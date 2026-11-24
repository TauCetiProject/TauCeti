/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.DoubleComplex
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Injective
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal

/-!
# The Čech-to-cohomology spectral sequence of a covering of a site

Let `(C, J)` be a site with finite products and a terminal object `T`, let `U` be a family of
objects covering `T` (`CategoryTheory.GrothendieckTopology.CoversTop`), and let `F` be an abelian
sheaf with an injective resolution `0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯`. The Čech double complex `Čᵖ(U, Iᵠ)`
(`TauCeti.CategoryTheory.cechDoubleComplex`) has two filtrations. Its rows `Č(U, Iᵠ)` are exact
in positive degrees, since `Iᵠ` is injective, and have `Iᵠ(T)` in degree `0`, since `Iᵠ` is a
sheaf (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_injective`); so its total complex
computes the cohomology of the sections `I(T)`, which is `Hⁿ(F)`. Its columns
`Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` are products of the complexes of sections
`I(U (a 0) × ⋯ × U (a p))`, so their cohomology is the group `Čᵖ(U, Hᵏ(F))` of Čech cochains of
the cohomology presheaf `V ↦ Hᵏ(V, F)`. Filtering by Čech degree gives the Čech-to-cohomology
spectral sequence, with first page `Čᵖ(U, Hᵏ(F))`, converging to `Hⁿ(F)`
(Stacks, Section 21.10 (03AV), Lemma 21.10.6 (03AZ)).

The spectral sequences of first-quadrant bicomplexes are those of chain complexes, so the double
complex lives in the opposite category `Aᵒᵖ`, and every object of the spectral sequence is the
opposite of the expected group. The general part of the file works with any cochain complex `I`
of presheaves with values in an abelian category `A` with products. The spectral sequence and its
first page need nothing more; the identification of the abutment needs the augmented rows
`0 ⟶ Iᵠ(T) ⟶ Č(U, Iᵠ)` to be exact, and the identification of the objects of the first page with
Čech cochains of the cohomology presheaves needs exact products of the shapes
`Fin (p + 1) → ι`.

## Main definitions and results

* `TauCeti.CategoryTheory.cechDoubleComplexSpectralSequence U I`: the spectral sequence of the
  filtration by Čech degree of the Čech double complex, with its first page
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
  cohomology and cohomology, Lemma 21.10.6 (tag 03AZ) for the spectral sequence.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

universe w v u

namespace TauCeti.CategoryTheory

section General

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type*} [Category* A]
  [Abelian A] [HasProducts.{w} A] {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)

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
def cechDoubleComplexSpectralSequenceFirstPageXIso (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (p k : ℕ) :
    ((cechDoubleComplexSpectralSequence U I).page 2).X (-(k : ℤ) - 2 * p, p) ≅
      op ((cechColumn U I p).homology k) :=
  (cechDoubleComplex U I).columnFiltrationSpectralSequenceFirstPageXIso p k ≪≫
    homologyOp (cechColumn U I p) k

/-- The abutment in degree `-n` of the spectral sequence of the Čech double complex is the
opposite of the cohomology in degree `n` of the complex of sections `I(T)`, when the augmented
rows `0 ⟶ Iᵠ(T) ⟶ Č(U, Iᵠ)` are exact. -/
def cechDoubleComplexAbutmentIso (I : CochainComplex (Cᵒᵖ ⥤ A) ℕ)
    (hI : ∀ q, QuasiIso (cechAugmentation U hT (I.X q))) (n : ℕ) :
    (cechDoubleComplexSpectralObject U I).abutment (-n) ≅
      op ((sectionsCochainComplex T I).homology n) :=
  have := quasiIso_cechTotalAugmentation U hT I hI
  (cechDoubleComplex U I).columnFiltrationAbutmentIso n ≪≫
    asIso (homologyMap (cechTotalAugmentation U hT I) n) ≪≫
    homologyOp (sectionsCochainComplex T I) n

end General

end TauCeti.CategoryTheory

namespace CategoryTheory.Limits.IsTerminal

open TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] {T : C}
  (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{v}} (R : InjectiveResolution F)

/-- The sections over a terminal object `T` of an injective resolution of `F` compute the
sheaf cohomology `Hⁿ(F)`. -/
def sectionsCochainComplexHomologyIsoH (n : ℕ) :
    (sectionsCochainComplex T R.presheafComplex).homology n ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} F n) :=
  (_root_.CategoryTheory.Sheaf.H'.addEquivHomologyOfResolution (R.ι.f 0)
    R.ι_f_zero_comp_complex_d R.exact₀ R.cocomplex_exactAt_succ T
    (fun j k ↦ Abelian.Ext.subsingleton_of_injective _ (R.cocomplex.X j) k)
    n).toAddCommGrpIso.symm ≪≫ F.cohomologyPresheafObjIsoH n hT

end CategoryTheory.Limits.IsTerminal

namespace TauCeti.CategoryTheory

section Sheaf

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] {ι : Type v} (U : ι → C) {T : C} (hT : IsTerminal T)
  (hU : J.CoversTop U) {F : Sheaf J AddCommGrpCat.{v}} (R : InjectiveResolution F)

/-- **The Čech-to-cohomology spectral sequence** of a covering family `U` and an abelian sheaf
`F`, built from an injective resolution `R` of `F`. Its first page is the cohomology of the
columns `Čᵖ(U, I⁰) ⟶ Čᵖ(U, I¹) ⟶ ⋯` of the Čech double complex of `R`, and it converges to the
sheaf cohomology `Hⁿ(F)` (`cechToCohomologyAbutmentIso`). -/
abbrev cechToCohomologySpectralSequence :=
  cechDoubleComplexSpectralSequence U R.presheafComplex

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

include hU in
/-- The abutment in degree `-n` of the Čech-to-cohomology spectral sequence is the opposite of the
sheaf cohomology `Hⁿ(F)`. -/
def cechToCohomologyAbutmentIso (n : ℕ) :
    (cechDoubleComplexSpectralObject U R.presheafComplex).abutment (-n) ≅
      op (AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} F n)) :=
  cechDoubleComplexAbutmentIso U hT R.presheafComplex
    (fun q ↦ quasiIso_cechAugmentation_of_injective U hT hU (R.cocomplex.X q)) n ≪≫
    (hT.sectionsCochainComplexHomologyIsoH R n).symm.op

/-- **The first page of the Čech-to-cohomology spectral sequence.** Its object at `(-k - 2p, p)`
(the first page being numbered `2`) is the opposite of the group `Čᵖ(U, Hᵏ(F))` of Čech cochains
of degree `p` of the cohomology presheaf `V ↦ Hᵏ(V, F)`. -/
def cechToCohomologyFirstPageXIso (p k : ℕ) :
    ((cechToCohomologySpectralSequence U R).page 2).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor U).obj (F.cohomologyPresheaf k)).X p) :=
  cechDoubleComplexSpectralSequenceFirstPageXIso U R.presheafComplex p k ≪≫
    (cechColumnHomologyIso U R.presheafComplex p k ≪≫
      (cechComplexFunctor U ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p).mapIso
        (_root_.CategoryTheory.Sheaf.H'.homologyIsoCohomologyPresheaf (R.ι.f 0)
          R.ι_f_zero_comp_complex_d R.exact₀ R.cocomplex_exactAt_succ
          (fun _ j k ↦ Abelian.Ext.subsingleton_of_injective _ (R.cocomplex.X j) k) k)).symm.op

end Sheaf

end TauCeti.CategoryTheory
