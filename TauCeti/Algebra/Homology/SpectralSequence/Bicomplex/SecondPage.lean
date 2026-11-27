/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.FirstDifferential
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Naturality
public import TauCeti.Algebra.Homology.SpectralSequence.SecondPage

/-!
# The second page of the column-filtration spectral sequence of a bicomplex

Let `K` be a first-quadrant bicomplex, with homological differentials, in an abelian category.
The first page (numbered `2`) of the spectral sequence of its column filtration
(`HomologicalComplex₂.columnFiltrationSpectralSequence`) has at `(-k - 2p, p)` the vertical
homology `H_k(K.X p)` of the column `p`, and its differential is, up to the sign `(-1)^k`, the map
induced by the horizontal differential
(`HomologicalComplex₂.columnFiltrationSpectralSequence_page_two_d`).
Hence the classical `E²` term, the page numbered `3`, is the iterated homology: its object at
`(-k - 2p, p)` is the horizontal homology `H_p(H_k^{II}(K))` in degree `p` of the complex
`t ↦ H_k(K.X t)` of vertical homologies
(`HomologicalComplex₂.columnFiltrationSpectralSequenceSecondPageXIso`). This complex is the image
of `K` under the functor induced on complexes by the homology functor in degree `k`.

The identification is described on classes of cycles of the first page
(`HomologicalComplex₂.homologyπ_columnFiltrationSpectralSequenceSecondPageXIso_hom`) and is natural
in the bicomplex
(`HomologicalComplex₂.columnFiltrationSpectralSequenceSecondPageXIso_hom_naturality`). It is an
instance of the computation of the second page of a spectral sequence from a model of its first
page, `CategoryTheory.SpectralSequence.pageThreeXIsoHomology`.

## References

* [Stacks: Lemma 12.25.1 (Tag 0130)](https://stacks.math.columbia.edu/tag/0130), in cohomological
  indexing.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.6 (the spectral sequences of a double complex).
-/

public section

noncomputable section

open CategoryTheory Limits ComplexShape

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C] (K : HomologicalComplex₂ C (down ℕ) (down ℕ))

/-- Along the line `(-k - 2p, p)`, the first differential of the spectral sequence of the column
filtration is `(-1)^k` times the differential of the complex `t ↦ H_k(K.X t)`. -/
private lemma columnFiltrationSpectralSequence_page_two_d_eq_smul (k p : ℕ) :
    (K.columnFiltrationSpectralSequenceFirstPageXIso (p + 1) k).inv ≫
      (K.columnFiltrationSpectralSequence.page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (K.columnFiltrationSpectralSequenceFirstPageXIso p k).hom =
    ((-1 : ℤˣ) ^ k) •
      (((HomologicalComplex.homologyFunctor C (down ℕ) k).mapHomologicalComplex (down ℕ)).obj K).d
        (p + 1) p := by
  rw [columnFiltrationSpectralSequence_page_two_d]
  simp [Units.smul_def]

/-- **The second page of the column-filtration spectral sequence** (Stacks, Lemma 12.25.1). The
object at `(-k - 2p, p)` of the page numbered `3`, the classical `E²` term, is the horizontal
homology `H_p(H_k^{II}(K))`: the homology in degree `p` of the complex `t ↦ H_k(K.X t)` of
vertical homologies, whose differential is induced by the horizontal differential of `K`. -/
def columnFiltrationSpectralSequenceSecondPageXIso (p k : ℕ) :
    (K.columnFiltrationSpectralSequence.page 3).X (-(k : ℤ) - 2 * p, p) ≅
      (((HomologicalComplex.homologyFunctor C (down ℕ) k).mapHomologicalComplex
        (down ℕ)).obj K).homology p :=
  SpectralSequence.pageThreeXIsoHomology K.columnFiltrationSpectralSequence _ k _
    (fun p ↦ K.columnFiltrationSpectralSequenceFirstPageXIso p k)
    (columnFiltrationSpectralSequence_page_two_d_eq_smul K k)
    -- the first page vanishes in the negative column
    (K.flip.isZero_rowFiltrationSpectralSequence_page_two_X_of_neg _ _ (by norm_num)) p

/-- A cycle of the first page of the column-filtration spectral sequence at `(-k - 2p, p)` is sent
by `HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso` to a cycle of the complex
`t ↦ H_k(K.X t)` of vertical homologies, whose differential is induced by that of `K`. -/
@[reassoc (attr := simp)]
lemma iCycles_columnFiltrationSpectralSequenceFirstPageXIso_hom_homologyMap_d (p k : ℕ) :
    (K.columnFiltrationSpectralSequence.page 2).iCycles (-(k : ℤ) - 2 * p, p) ≫
        (K.columnFiltrationSpectralSequenceFirstPageXIso p k).hom ≫
        HomologicalComplex.homologyMap (K.d p (p - 1)) k = 0 := by
  simpa using SpectralSequence.iCycles_pageTwo_comp_hom_d K.columnFiltrationSpectralSequence
    (((HomologicalComplex.homologyFunctor C (down ℕ) k).mapHomologicalComplex (down ℕ)).obj K) k
    ((-1 : ℤˣ) ^ k) (fun p ↦ K.columnFiltrationSpectralSequenceFirstPageXIso p k)
    (columnFiltrationSpectralSequence_page_two_d_eq_smul K k) p

/-- **The second page of the column-filtration spectral sequence on classes of cycles.** The class
on the page `3` of a cycle `z` of the first page at `(-k - 2p, p)` is sent by
`HomologicalComplex₂.columnFiltrationSpectralSequenceSecondPageXIso` to the class of the cycle
of `t ↦ H_k(K.X t)` that `z` corresponds to under
`HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso`. -/
@[reassoc]
lemma homologyπ_columnFiltrationSpectralSequenceSecondPageXIso_hom (p k : ℕ) :
    (K.columnFiltrationSpectralSequence.page 2).homologyπ (-(k : ℤ) - 2 * p, p) ≫
        (K.columnFiltrationSpectralSequence.iso 2 3 (-(k : ℤ) - 2 * p, p)).hom ≫
        (K.columnFiltrationSpectralSequenceSecondPageXIso p k).hom =
      HomologicalComplex.liftCycles _
          ((K.columnFiltrationSpectralSequence.page 2).iCycles (-(k : ℤ) - 2 * p, p) ≫
            (K.columnFiltrationSpectralSequenceFirstPageXIso p k).hom) (p - 1)
          (by cases p <;> simp)
          (by simp) ≫
        HomologicalComplex.homologyπ _ p :=
  SpectralSequence.homologyπ_pageThreeXIsoHomology_hom _ _ _ _ _ _ _ p

variable {K} in
/-- **Naturality of the second page of the column-filtration spectral sequence.** Under the
identifications `HomologicalComplex₂.columnFiltrationSpectralSequenceSecondPageXIso`, the morphism
of spectral sequences induced by a morphism `φ : K ⟶ L` of bicomplexes is, on the page `3`, the map
induced in homology by the morphism of complexes `t ↦ H_k(φ.f t)` of vertical homologies. -/
@[reassoc]
lemma columnFiltrationSpectralSequenceSecondPageXIso_hom_naturality
    {L : HomologicalComplex₂ C (down ℕ) (down ℕ)} (φ : K ⟶ L) (p k : ℕ) :
    ((columnFiltrationSpectralSequenceMap φ).hom 3).f (-(k : ℤ) - 2 * p, p) ≫
        (L.columnFiltrationSpectralSequenceSecondPageXIso p k).hom =
      (K.columnFiltrationSpectralSequenceSecondPageXIso p k).hom ≫
        HomologicalComplex.homologyMap
          (((HomologicalComplex.homologyFunctor C (down ℕ) k).mapHomologicalComplex
            (down ℕ)).map φ) p :=
  SpectralSequence.pageThreeXIsoHomology_hom_naturality _ _ _ _ _ _ _ _ _ p
    (columnFiltrationSpectralSequenceFirstPageXIso_hom_naturality φ p k)

end HomologicalComplex₂
