/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Basic
public import TauCeti.RepresentationTheory.Homological.CoinvariantsTensor

/-!
# Group hyperhomology

Let `C` be a chain complex of representations of a group `G` over a commutative ring `k`,
concentrated in degrees `≥ 0`, and let `P` be a projective resolution of the trivial
representation `k`. Applying the tensor-coinvariant bifunctor `(A, B) ↦ (A ⊗[k] B)_G` to `C` and
`P` gives a first-quadrant bicomplex with terms `(C_p ⊗ P_q)_G`, and the group hyperhomology
`H_n(G; C)` is the homology of its total complex. We take for `P` the bar resolution, so that for a
representation `A` placed in degree `0` this is the group homology `H_n(G, A)`, computed from the
inhomogeneous chains (`Rep.groupHyperhomologySingleIso`); any other projective resolution gives
canonically isomorphic groups (`HomologicalComplex.groupHyperhomologyIso`).

The groups `H_n(G; C)` are the abutment of a spectral sequence with first page
`E¹_(p,q) = H_q(G, C_p)`, from filtering by the degree of `C`
(`HomologicalComplex.groupHyperhomologySpectralSequence`). On the other hand the hyperhomology
only sees the homology of `C` in low degrees: if `C` is exact in all degrees `≤ n`, then
`H_n(G; C) = 0` (`HomologicalComplex.isZero_groupHyperhomology_of_exactAt`), since tensor
coinvariants with a projective representation are exact. This is how a group acting on a highly
acyclic complex, such as the complexes of unimodular frames in van der Kallen's proof of homology
stability for general linear groups, yields relations between the homology of the stabilisers of
the cells.

## Main definitions

* `HomologicalComplex.groupHyperhomology`: the group hyperhomology `H_n(G; C)`.
* `HomologicalComplex.groupHyperhomologyIso`: its computation from any projective resolution of
  the trivial representation.
* `Rep.groupHyperhomologySingleIso`: for `A` placed in degree `0`, `H_n(G; A[0]) ≅ H_n(G, A)`.
* `HomologicalComplex.groupHyperhomologySpectralSequence`: the spectral sequence of the filtration
  by the degree of `C`, with first page identified by
  `HomologicalComplex.groupHyperhomologySpectralSequenceFirstPageXIso` and abutment by
  `HomologicalComplex.groupHyperhomologySpectralSequenceAbutmentIso`.

## Main results

* `HomologicalComplex.exactAt_mapBifunctor_coinvariantsTensor`: for a degreewise projective
  complex `P`, the total complex of `(C_p ⊗ P_q)_G` is exact in degree `n` once `C` is exact in
  every degree `≤ n`.
* `HomologicalComplex.isZero_groupHyperhomology_of_exactAt`: `H_n(G; C) = 0` once `C` is exact
  in every degree `≤ n`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Section VII.5 (equivariant homology and its two spectral sequences).
* W. van der Kallen, *Homology stability for linear groups*, Invent. Math. 60 (1980), 269–295,
  proof of Proposition 3.7.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G]

namespace HomologicalComplex

/-- For a degreewise projective complex `P` of representations, the total complex of the bicomplex
`(C_p ⊗ P_q)_G` is exact in degree `n` as soon as `C` is exact in every degree `≤ n`: tensor
coinvariants with the projective representation `P_q` are exact, so the row `q` is exact in every
degree `≤ n`. -/
theorem exactAt_mapBifunctor_coinvariantsTensor (C P : ChainComplex (Rep.{u} k G) ℕ)
    [∀ q, Projective (P.X q)] (n : ℕ) (hC : ∀ p ≤ n, C.ExactAt p) :
    (mapBifunctor C P (Rep.coinvariantsTensor k G) (ComplexShape.down ℕ)).ExactAt n := by
  refine HomologicalComplex₂.exactAt_total_of_rows _ n fun p q hpq ↦ ?_
  have : ((Rep.coinvariantsTensor k G).flip.obj (P.X q)).PreservesHomology :=
    ((Functor.exact_tfae ((Rep.coinvariantsTensor k G).flip.obj (P.X q))).out 1 3).1
      fun _ hS ↦ ShortComplex.ShortExact.map_coinvariantsTensor_projective hS _
  exact (hC p (by omega)).map ((Rep.coinvariantsTensor k G).flip.obj (P.X q))

/-- The **group hyperhomology** `H_n(G; C)` of a chain complex `C` of representations of `G`: the
homology in degree `n` of the total complex of the bicomplex `(C_p ⊗ P_q)_G`, where `P` is the bar
resolution of the trivial representation `k`. -/
def groupHyperhomology (C : ChainComplex (Rep.{u} k G) ℕ) (n : ℕ) : ModuleCat.{u} k :=
  (mapBifunctor C (Rep.barComplex k G) (Rep.coinvariantsTensor k G)
    (ComplexShape.down ℕ)).homology n

/-- Group hyperhomology is the homology of the total complex of `(C_p ⊗ P_q)_G`, for `P` the bar
resolution. -/
lemma groupHyperhomology_def (C : ChainComplex (Rep.{u} k G) ℕ) (n : ℕ) :
    C.groupHyperhomology n = (mapBifunctor C (Rep.barComplex k G) (Rep.coinvariantsTensor k G)
      (ComplexShape.down ℕ)).homology n :=
  (rfl)

/-- Group hyperhomology can be computed from any projective resolution `P` of the trivial
representation, as the homology of the total complex of `(C_p ⊗ P_q)_G`. -/
def groupHyperhomologyIso (C : ChainComplex (Rep.{u} k G) ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) (n : ℕ) :
    C.groupHyperhomology n ≅
      (mapBifunctor C P.complex (Rep.coinvariantsTensor k G) (ComplexShape.down ℕ)).homology n :=
  (HomotopyEquiv.mapBifunctor (Rep.coinvariantsTensor k G) (ComplexShape.down ℕ)
    (HomotopyEquiv.refl C) ((Rep.barResolution k G).homotopyEquiv P)).toHomologyIso n

/-- **Group hyperhomology vanishes in degrees where the complex is acyclic.** If `C` is exact in
every degree `≤ n`, then `H_n(G; C) = 0`. -/
theorem isZero_groupHyperhomology_of_exactAt (C : ChainComplex (Rep.{u} k G) ℕ) (n : ℕ)
    (hC : ∀ p ≤ n, C.ExactAt p) : IsZero (C.groupHyperhomology n) :=
  (exactAt_mapBifunctor_coinvariantsTensor C (Rep.barComplex k G) n hC).isZero_homology

/-- The bicomplex `(C_p ⊗ P_q)_G` computing the group hyperhomology of `C`, with `P` the bar
resolution. -/
abbrev groupHyperhomologyBicomplex (C : ChainComplex (Rep.{u} k G) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} k) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (((Rep.coinvariantsTensor k G).mapBifunctorHomologicalComplex _ _).obj C).obj (Rep.barComplex k G)

/-- The column `p` of the bicomplex computing group hyperhomology is the complex `(C_p ⊗ P_•)_G`
computing the group homology of `C_p`. -/
def groupHyperhomologyBicomplexXIso (C : ChainComplex (Rep.{u} k G) ℕ) (p : ℕ) :
    C.groupHyperhomologyBicomplex.X p ≅ (Rep.barComplex k G).coinvariantsTensorObj (C.X p) :=
  Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by simp)

/-- The **spectral sequence of group hyperhomology** obtained by filtering by the degree of `C`.
In Mathlib's cohomological indexing, its object at `(-q - 2p, p)` on the first page (numbered `2`)
is `H_q(G, C_p)` (`HomologicalComplex.groupHyperhomologySpectralSequenceFirstPageXIso`), and it
converges to `H_(p+q)(G; C)` (`HomologicalComplex.groupHyperhomologySpectralSequenceAbutmentIso`).
-/
abbrev groupHyperhomologySpectralSequence (C : ChainComplex (Rep.{u} k G) ℕ) :=
  C.groupHyperhomologyBicomplex.columnFiltrationSpectralSequence

/-- The first page of the spectral sequence of group hyperhomology: `E¹_(p,q) = H_q(G, C_p)`, at
the position `(-q - 2p, p)` of Mathlib's cohomological indexing. -/
def groupHyperhomologySpectralSequenceFirstPageXIso (C : ChainComplex (Rep.{u} k G) ℕ)
    (p q : ℕ) :
    (C.groupHyperhomologySpectralSequence.page 2).X (-(q : ℤ) - 2 * p, p) ≅
      groupHomology (C.X p) q :=
  C.groupHyperhomologyBicomplex.columnFiltrationSpectralSequenceFirstPageXIso p q ≪≫
    homologyMapIso (C.groupHyperhomologyBicomplexXIso p) q ≪≫
    (homologyMapIso (groupHomology.inhomogeneousChainsIso (C.X p)) q).symm

/-- The abutment of the spectral sequence of group hyperhomology in degree `-n` is `H_n(G; C)`. -/
def groupHyperhomologySpectralSequenceAbutmentIso (C : ChainComplex (Rep.{u} k G) ℕ) (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
      C.groupHyperhomologyBicomplex.flip.rowFiltration
      C.groupHyperhomologyBicomplex.flip.monotone_rowFiltration)).abutment (-n) ≅
      C.groupHyperhomology n :=
  C.groupHyperhomologyBicomplex.columnFiltrationAbutmentIso n

end HomologicalComplex

namespace Rep

open HomologicalComplex

/-- For a representation `A` placed in degree `0`, the bicomplex computing its group
hyperhomology has zero horizontal differential out of the column `1`. -/
private lemma groupHyperhomologyBicomplex_single_d_one_zero (A : Rep.{u} k G) :
    ((single _ (ComplexShape.down ℕ) 0).obj A).groupHyperhomologyBicomplex.d 1 0 = 0 := by
  ext q : 1
  simp only [Functor.mapBifunctorHomologicalComplex_obj_obj_d_f, single_obj_d, Functor.map_zero,
    NatTrans.app_zero, zero_f]

/-- For a representation `A` placed in degree `0`, the bicomplex computing its group
hyperhomology has the single nonzero column `0`, so the augmentation of its total complex onto
that column is a quasi-isomorphism. -/
private lemma quasiIso_totalAugmentation_groupHyperhomologyBicomplex_single (A : Rep.{u} k G) :
    QuasiIso (HomologicalComplex₂.totalAugmentation
      ((single _ (ComplexShape.down ℕ) 0).obj A).groupHyperhomologyBicomplex (𝟙 _)
      (by simp [groupHyperhomologyBicomplex_single_d_one_zero])) := by
  let K := ((single _ (ComplexShape.down ℕ) 0).obj A).groupHyperhomologyBicomplex
  have hd : K.d 1 0 = 0 := groupHyperhomologyBicomplex_single_d_one_zero A
  let φ : K ⟶ (single _ (ComplexShape.down ℕ) 0).obj (K.X 0) :=
    mkHomToSingle (𝟙 _) fun i hi ↦ by
      obtain rfl : i = 1 := by simpa using hi.symm
      simp [hd]
  -- On each row, `φ` is the identity in degree `0` and a map between zero objects elsewhere.
  have hφ (q : ℕ) : QuasiIso (((eval _ _ q).mapHomologicalComplex _).map φ) := by
    have (p : ℕ) : IsIso ((((eval _ _ q).mapHomologicalComplex _).map φ).f p) := by
      rcases p with _ | p
      · simp only [Functor.mapHomologicalComplex_map_f, eval_map, φ, mkHomToSingle_f,
          Category.id_comp]
        infer_instance
      · refine isIso_of_source_target_iso_zero _ (IsZero.isoZero ?_) (IsZero.isoZero ?_)
        · exact ((Rep.coinvariantsTensor k G).map_isZero
            (isZero_single_obj_X _ 0 A (p + 1) (by simp))).obj _
        · exact (eval _ _ q).map_isZero (isZero_single_obj_X _ 0 _ (p + 1) (by simp))
    have := Hom.isIso_of_components (((eval _ _ q).mapHomologicalComplex _).map φ)
    infer_instance
  exact HomologicalComplex₂.quasiIso_totalAugmentation_of_rows_of_quasiIso φ hφ (𝟙 _)
    (by simp [hd]) (by simp [φ, K])

/-- **Group hyperhomology of a single representation.** For a representation `A` placed in degree
`0`, the group hyperhomology `H_n(G; A[0])` is the group homology `H_n(G, A)`. -/
def groupHyperhomologySingleIso (A : Rep.{u} k G) (n : ℕ) :
    ((single _ (ComplexShape.down ℕ) 0).obj A).groupHyperhomology n ≅ groupHomology A n :=
  have := quasiIso_totalAugmentation_groupHyperhomologyBicomplex_single A
  isoOfQuasiIsoAt (HomologicalComplex₂.totalAugmentation
      ((single _ (ComplexShape.down ℕ) 0).obj A).groupHyperhomologyBicomplex (𝟙 _)
      (by simp [groupHyperhomologyBicomplex_single_d_one_zero])) n ≪≫
    homologyMapIso (((single _ (ComplexShape.down ℕ) 0).obj A).groupHyperhomologyBicomplexXIso 0 ≪≫
      (Rep.barComplex k G).coinvariantsTensorFunctor.mapIso (singleObjXSelf _ 0 A) ≪≫
      (groupHomology.inhomogeneousChainsIso A).symm) n

end Rep
