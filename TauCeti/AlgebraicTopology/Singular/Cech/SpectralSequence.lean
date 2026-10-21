/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.AlgebraicTopology.Singular.Cech.OrderedQuasiIso

/-!
# The Čech--singular spectral sequence

The ordered Čech--singular double complex of a linearly ordered open cover has a spectral
sequence obtained by filtering its total complex by Čech degree. In the indexing used by
Mathlib's cohomological spectral objects, the usual term `E¹_{p,q}` occurs at
`(-q - 2p, p)` on the first page (which Mathlib numbers `2`). It is isomorphic to

`⨁_{|s| = p + 1} H_q(⋂ i ∈ s, U_i; R)`.

For a finite cover the first page vanishes in Čech degrees at least the cardinality of the
indexing type. The row-filtration convergence theorem therefore gives a bounded spectral
sequence: since `cechSpectralSequence` is an abbreviation, the stabilization of its pages is
`(cechDoubleComplex U R).flip.rowFiltrationSpectralSequencePageXIsoEInfty`. When the family
covers the ambient space, its abutment is singular homology, through the augmentation of the
total Čech--singular complex.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, §15.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Chapters 1--2.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology ComplexShape
open scoped Finset

universe w v u

namespace TauCeti

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  {X : TopCat.{w}} {ι : Type w} [LinearOrder ι] (U : ι → Opens X) (R : C)

/-- The Čech--singular spectral sequence, obtained by filtering the ordered double complex by
Čech degree. Mathlib numbers its first page `2`. -/
abbrev cechSpectralSequence :=
  (cechDoubleComplex U R).flip.rowFiltrationSpectralSequence

/-- The homology of a column of the Čech--singular double complex is the coproduct of the
singular homology of its intersections, provided coproducts over those intersections are exact. -/
def cechColumnHomologyIso (p q : ℕ)
    [HasExactColimitsOfShape (Discrete {s : Finset ι // #s = p + 1}) C] :
    ((cechDoubleComplex U R).X p).homology q ≅
      ∐ (fun s : {s : Finset ι // #s = p + 1} ↦
        (HomologicalComplex.homologyFunctor C (down ℕ) q).obj
          ((cechSingularChains U R).obj (op s.1)) :
          {s : Finset ι // #s = p + 1} → C) := by
  let F : {s : Finset ι // #s = p + 1} → ChainComplex C ℕ :=
    fun s ↦ (cechSingularChains U R).obj (op s.1)
  let H := HomologicalComplex.homologyFunctor C (down ℕ) q
  exact (isColimitCofanMkObjOfIsColimit H F _
    (isColimitCechDoubleComplexCofan U R p)).coconePointUniqueUpToIso
      (coproductIsCoproduct _)

/-- The column-homology comparison sends the homology map of each summand inclusion to the
corresponding coproduct inclusion. -/
@[reassoc (attr := simp)]
lemma homologyMap_cechDoubleComplexι_cechColumnHomologyIso_hom (p q : ℕ)
    [HasExactColimitsOfShape (Discrete {s : Finset ι // #s = p + 1}) C]
    (s : {s : Finset ι // #s = p + 1}) :
    HomologicalComplex.homologyMap (cechDoubleComplexι U R (p := p) s) q ≫
        (cechColumnHomologyIso U R p q).hom =
      Sigma.ι (fun s : {s : Finset ι // #s = p + 1} ↦
        (HomologicalComplex.homologyFunctor C (down ℕ) q).obj
          ((cechSingularChains U R).obj (op s.1))) s := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitCofanMkObjOfIsColimit (HomologicalComplex.homologyFunctor C (down ℕ) q)
      (fun s : {s : Finset ι // #s = p + 1} ↦
        (cechSingularChains U R).obj (op s.1)) _
      (isColimitCechDoubleComplexCofan U R p))
    (coproductIsCoproduct _) ⟨s⟩

/-- Composing a coproduct inclusion with the inverse column-homology comparison recovers the
homology map of the corresponding summand inclusion. -/
@[reassoc (attr := simp)]
lemma ι_cechColumnHomologyIso_inv (p q : ℕ)
    [HasExactColimitsOfShape (Discrete {s : Finset ι // #s = p + 1}) C]
    (s : {s : Finset ι // #s = p + 1}) :
    Sigma.ι (fun s : {s : Finset ι // #s = p + 1} ↦
        (HomologicalComplex.homologyFunctor C (down ℕ) q).obj
          ((cechSingularChains U R).obj (op s.1))) s ≫
        (cechColumnHomologyIso U R p q).inv =
      HomologicalComplex.homologyMap (cechDoubleComplexι U R (p := p) s) q := by
  exact IsColimit.comp_coconePointUniqueUpToIso_inv
    (isColimitCofanMkObjOfIsColimit (HomologicalComplex.homologyFunctor C (down ℕ) q)
      (fun s : {s : Finset ι // #s = p + 1} ↦
        (cechSingularChains U R).obj (op s.1)) _
      (isColimitCechDoubleComplexCofan U R p))
    (coproductIsCoproduct _) ⟨s⟩

/-- **The first page of the Čech--singular spectral sequence.** In conventional homological
coordinates, `E¹_{p,q}` is the coproduct of `H_q` of the `(p + 1)`-fold intersections. -/
def cechSpectralSequenceFirstPageXIso (p q : ℕ)
    [HasExactColimitsOfShape (Discrete {s : Finset ι // #s = p + 1}) C] :
    ((cechSpectralSequence U R).page 2).X (-(q : ℤ) - 2 * p, p) ≅
      ∐ (fun s : {s : Finset ι // #s = p + 1} ↦
        (HomologicalComplex.homologyFunctor C (down ℕ) q).obj
          ((cechSingularChains U R).obj (op s.1)) :
          {s : Finset ι // #s = p + 1} → C) :=
  (cechDoubleComplex U R).columnFiltrationSpectralSequenceFirstPageXIso p q ≪≫
    cechColumnHomologyIso U R p q

/-- For a finite cover, the first page vanishes in Čech degrees at least the number of cover
members. -/
lemma isZero_cechSpectralSequence_page_two_X [Fintype ι] {p : ℕ}
    (hp : Fintype.card ι ≤ p) (q : ℕ) :
    IsZero (((cechSpectralSequence U R).page 2).X (-(q : ℤ) - 2 * p, p)) := by
  have h : IsZero (((cechDoubleComplex U R).X p).homology q) :=
    (HomologicalComplex.homologyFunctor C (down ℕ) q).map_isZero
      (isZero_cechDoubleComplex_X U R hp)
  have h' := IsZero.of_iso h
    ((cechDoubleComplex U R).columnFiltrationSpectralSequenceFirstPageXIso p q)
  simpa only [cechSpectralSequence] using h'

/-- The abutment of the Čech--singular spectral sequence of an open cover is the singular homology
of the covered space. -/
def cechSpectralSequenceAbutmentIso (hU : ⋃ i, (U i : Set X) = Set.univ) (n : ℕ) :
    (CochainComplex.spectralObject
      (CochainComplex.filtrationFunctor (cechDoubleComplex U R).flip.rowFiltration
        (cechDoubleComplex U R).flip.monotone_rowFiltration)).abutment (-n) ≅
      ((singularHomologyFunctor C n).obj R).obj X := by
  haveI : QuasiIso (cechTotalAugmentation U R) := quasiIso_cechTotalAugmentation U R hU
  exact (cechDoubleComplex U R).columnFiltrationAbutmentIso n ≪≫
    isoOfQuasiIsoAt (cechTotalAugmentation U R) n

end TauCeti
