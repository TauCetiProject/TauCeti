/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Skeleton

/-!
# The spectral sequence of the skeletal filtration of a CW complex

Let `B` be a CW complex and filter it by its skeleta, `B_q = B^(q)` (`TauCeti.preimageSkeleton` for
the identity of `B`). The spectral sequence of this filtered space
(`TauCeti.filteredSpaceSpectralSequence`) has at `(p, q)` on its first page (numbered `2`, singular
chains of degree `n` sitting in degree `-n`) the relative homology `Hₙ(B^(q+1), B^(q))` with
`p + q = -n`. Since the relative homology of consecutive skeleta is concentrated in the degree of
their cells, the first page lives on the line `n ↦ (1 - 2n, n - 1)`
(`TauCeti.skeletalLineEmbedding`), where the object is the cellular chain group
`Hₙ(Bⁿ, Bⁿ⁻¹)`, and the first differential is the connecting map of three consecutive skeleta,
which is the cellular differential. So the first page is the cellular chain complex of `B`,
placed on that line (`TauCeti.skeletalSpectralSequencePageTwoIso`).

Consequently the next page is cellular homology, which is singular homology: on the line it is
`Hₙ(B)`, provided the comparison map of the `(n + 1)`-skeleton with `B` is an isomorphism on
`Hₙ` (as for finite-dimensional complexes) (`TauCeti.skeletalSpectralSequencePageThreeXIso`), and
off it zero (`TauCeti.isZero_skeletalSpectralSequence_page_three_X`). The relative groups of the
first page are in general not yet these groups, because the first differential need not vanish:
for `RP²` it is multiplication by `2` from the cell of dimension `2` to the cell of dimension `1`.

## Main results

* `TauCeti.skeletalSpectralSequenceFirstPageXIso`: the first page at `(1 - 2n, n - 1)` is the
  cellular chain group in degree `n`.
* `TauCeti.skeletalSpectralSequence_page_two_d_eq`: under these identifications the first
  differential is the cellular differential.
* `TauCeti.isZero_skeletalSpectralSequence_page_two_X`: the first page vanishes off the line.
* `TauCeti.skeletalSpectralSequencePageTwoIso`: the first page is the cellular chain complex,
  extended along `TauCeti.skeletalLineEmbedding`.
* `TauCeti.skeletalSpectralSequencePageThreeXIso` and
  `TauCeti.isZero_skeletalSpectralSequence_page_three_X`: the second page is the singular homology
  of `B` on the line, when the skeleton comparison map is an isomorphism on homology, and zero off
  it.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Example 2.D, the spectral sequence of the skeletal filtration.
* A. Hatcher, *Algebraic Topology*, Section 2.2, cellular homology.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

/-- The embedding `n ↦ (1 - 2n, n - 1)` of the indices of a chain complex into the indices of the
first page of the spectral sequence of a filtered space, whose differential has bidegree
`(2, -1)`. The first page of the skeletal filtration of a CW complex lives on its image, with the
cellular chain group of degree `n` at `(1 - 2n, n - 1)`. -/
def skeletalLineEmbedding :
    ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up' ((2, -1) : ℤ × ℤ)) :=
  ComplexShape.Embedding.mk' _ _ (fun n ↦ (1 - 2 * (n : ℤ), (n : ℤ) - 1))
    (fun m n h ↦ by simpa using congrArg Prod.snd h)
    (fun i j ↦ by
      simp only [ComplexShape.down_Rel, ComplexShape.up'_Rel, Prod.mk_add_mk, Prod.mk.injEq]
      lia)

/-- The embedding `TauCeti.skeletalLineEmbedding` sends `n` to `(1 - 2n, n - 1)`. -/
@[simp]
lemma skeletalLineEmbedding_f (n : ℕ) :
    skeletalLineEmbedding.f n = (1 - 2 * (n : ℤ), (n : ℤ) - 1) := (rfl)

/-- The image of `TauCeti.skeletalLineEmbedding` contains the source of every differential into
it: the differential into `(1 - 2n, n - 1)` comes from `(-1 - 2n, n)`, the image of `n + 1`. -/
instance : skeletalLineEmbedding.IsTruncLE where
  rel' i j h := by
    simp only [ComplexShape.up'_Rel, skeletalLineEmbedding_f, Prod.mk_add_mk, Prod.mk.injEq] at h
    simp only [ComplexShape.down_Rel]
    lia
  mem_prev {i' j} h := ⟨j + 1, by
    simp only [ComplexShape.up'_Rel, skeletalLineEmbedding_f, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add] at h ⊢
    push_cast
    constructor <;> lia⟩

variable {B : Type w} [TopologicalSpace B] [T2Space B] [CWComplex (Set.univ : Set B)]
  {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{w} A] (R : A)

/-! The comparison is first carried out for an arbitrary family `X` of subsets of `B` given by the
skeleta, `X q = B^(q)`; the skeletal filtration is the case `X = preimageSkeleton _ id`. -/

section General

variable {X : ℤ → Set (TopCat.of B)} (hX : Monotone X)
  (hXs : ∀ q : ℤ, X q = skeletonLT (Set.univ : Set B) ((q + 1).toNat : ℕ∞))

include hXs in
private lemma eq_skeletonLT_of_add_one_eq {q : ℤ} {n : ℕ} (hq : q + 1 = n) :
    X q = skeletonLT (Set.univ : Set B) n := by
  rw [hXs, hq, Int.toNat_natCast]

include hXs in
/-- The first page at `(p, q)`, with `p + q = -n` and `q + 1 = n`, is the cellular chain group in
degree `n`. -/
private def firstPageXIsoAux (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n) (hq : pq.2 + 1 = n) :
    ((filteredSpaceSpectralSequence R hX).page 2).X pq ≅
      cellularChainGroup (Set.univ : Set B) R n :=
  filteredSpaceSpectralSequenceFirstPageXIso R hX pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hn ≪≫
    eqToIso (congrArg (TopPair.singularHomology · R n) (TopPair.ofInclusion_congr _ _
      (eq_skeletonLT_of_add_one_eq hXs hq)
      (eq_skeletonLT_of_add_one_eq hXs (by lia : pq.2 + 1 + 1 = (n + 1 : ℕ)))))

/-- The identifications of the first page with relative homology for two presentations of the
same indices differ by the transport along the equality of the pairs. -/
private lemma filteredSpaceSpectralSequenceFirstPageXIso_inv_congr {Y : TopCat.{w}} {X : ℤ → Set Y}
    (hX : Monotone X) (pq : ℤ × ℤ) (a b a' b' : ℤ) (ha : a = pq.2) (hb : b = pq.2 + 1)
    (ha' : a' = pq.2) (hb' : b' = pq.2 + 1) (m m' : ℤ) (hm : m = pq.1 + pq.2)
    (hm' : m' = pq.1 + pq.2) (n : ℕ) (hn : m = -n) (hn' : m' = -n) :
    (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn).inv =
      eqToHom (by subst ha hb ha' hb'; rfl) ≫
        (filteredSpaceSpectralSequenceFirstPageXIso R hX pq a' b' ha' hb' m' hm' n hn').inv := by
  subst ha hb ha' hb' hm hm'
  rw [eqToHom_refl, Category.id_comp]

/-- The connecting maps of two triples of subsets agree, up to transport, when the subsets do. -/
@[reassoc]
private lemma singularHomologyδ_ofInclusions_congr {Y : TopCat.{w}} {s t x s' t' x' : Set Y}
    (hst : s ⊆ t) (htx : t ⊆ x) (hst' : s' ⊆ t') (htx' : t' ⊆ x') (hs : s = s') (ht : t = t')
    (hx : x = x') (n : ℕ) {Z : A}
    (h : (TopTriple.innerPair.obj (TopTriple.ofInclusions hst htx)).singularHomology R n = Z)
    (h' : (TopTriple.innerPair.obj (TopTriple.ofInclusions hst' htx')).singularHomology R n = Z) :
    (TopTriple.ofInclusions hst htx).singularHomologyδ R (n + 1) n ≫ eqToHom h =
      eqToHom (by subst hs ht hx; rfl) ≫
        (TopTriple.ofInclusions hst' htx').singularHomologyδ R (n + 1) n ≫ eqToHom h' := by
  subst hs ht hx h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp]

include hXs in
/-- The first differential along the line is the cellular differential. -/
private theorem page_two_d_eq_aux (pq pq' : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -(n + 1 : ℕ))
    (hq : pq.2 + 1 = (n + 1 : ℕ)) (hn' : pq'.1 + pq'.2 = -n) (hq' : pq'.2 + 1 = n) :
    ((filteredSpaceSpectralSequence R hX).page 2).d pq pq' =
      (firstPageXIsoAux R hX hXs pq (n + 1) hn hq).hom ≫
        cellularDifferential (Set.univ : Set B) R n ≫
          (firstPageXIsoAux R hX hXs pq' n hn' hq').inv := by
  obtain ⟨p, q⟩ := pq
  obtain ⟨p', q'⟩ := pq'
  dsimp only at hn hq hn' hq'
  obtain rfl : p' = p + 2 := by lia
  obtain rfl : q' = q - 1 := by lia
  rw [filteredSpaceSpectralSequence_first_page_d_eq R _ q p n hn,
    cellularDifferential_eq_singularHomologyδ]
  simp only [firstPageXIsoAux, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    Category.assoc]
  rw [filteredSpaceSpectralSequenceFirstPageXIso_inv_congr R _ (p + 2, q - 1) (q - 1) q (q - 1)
    (q - 1 + 1) rfl (by lia) rfl rfl (p + q + 1) (p + 2 + (q - 1)) (by lia) rfl n (by lia) hn']
  congr 1
  exact singularHomologyδ_ofInclusions_congr_assoc R _ _
      (skeletonLT_subset_skeletonLT_succ (Set.univ : Set B) n)
      (skeletonLT_subset_skeletonLT_succ (Set.univ : Set B) (n + 1))
      (eq_skeletonLT_of_add_one_eq hXs hq')
      (eq_skeletonLT_of_add_one_eq hXs hq)
      (eq_skeletonLT_of_add_one_eq hXs (by lia : q + 1 + 1 = (n + 1 + 1 : ℕ))) n _ _ _

include hXs in
/-- Off the line `n ↦ (1 - 2n, n - 1)` the first page vanishes. -/
private lemma isZero_page_two_X_aux
    [∀ m, HasExactColimitsOfShape (Discrete (cell (Set.univ : Set B) m)) A] (pq : ℤ × ℤ)
    (h : ∀ n : ℕ, skeletalLineEmbedding.f n ≠ pq) :
    IsZero (((filteredSpaceSpectralSequence R hX).page 2).X pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X R hX pq hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  refine IsZero.of_iso ?_
    (filteredSpaceSpectralSequenceFirstPageXIso R hX pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hn)
  rcases lt_or_ge pq.2 (-1) with hq | hq
  · refine (TopPair.isZero_singularHomology_ofInclusion_congr R _ (subset_refl (X pq.2)) ?_ rfl
      n).2 (TopPair.isZero_singularHomology_ofInclusion_self R _ n)
    rw [hXs, hXs, Int.toNat_of_nonpos (by lia), Int.toNat_of_nonpos (by lia)]
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ pq.2 + 1)
    refine (TopPair.isZero_singularHomology_ofInclusion_congr R _
      (skeletonLT_subset_skeletonLT_succ (Set.univ : Set B) m)
      (eq_skeletonLT_of_add_one_eq hXs (by lia : pq.2 + 1 + 1 = (m + 1 : ℕ)))
      (eq_skeletonLT_of_add_one_eq hXs hm) n).2
      (isZero_singularHomology_skeletonPair_of_ne _ R fun hnm ↦ h n ?_)
    subst hnm
    ext <;> simp <;> lia

include hXs in
/-- The restriction of the first page to the line is the cellular chain complex. -/
private def restrictionIsoAux :
    ((filteredSpaceSpectralSequence R hX).page 2).restriction skeletalLineEmbedding ≅
      cellularChainComplex (Set.univ : Set B) R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((filteredSpaceSpectralSequence R hX).page 2).restrictionXIso
      skeletalLineEmbedding rfl ≪≫
      firstPageXIsoAux R hX hXs _ n (by simp; lia) (by simp) ≪≫
        eqToIso (cellularChainComplex_X _ R n).symm)
    (by
      rintro i j (rfl : j + 1 = i)
      rw [HomologicalComplex.restriction_d_eq _ _ rfl rfl, cellularChainComplex_d,
        page_two_d_eq_aux R hX hXs _ _ j (by simp; lia) (by simp) (by simp; lia) (by simp)]
      simp)

include hXs in
/-- The first page is the extension of the cellular chain complex along the line. -/
private def pageTwoIsoAux
    [∀ m, HasExactColimitsOfShape (Discrete (cell (Set.univ : Set B) m)) A] :
    (filteredSpaceSpectralSequence R hX).page 2 ≅
      (cellularChainComplex (Set.univ : Set B) R).extend skeletalLineEmbedding :=
  have : ((filteredSpaceSpectralSequence R hX).page 2).IsStrictlySupported
      skeletalLineEmbedding := ⟨fun pq h ↦ isZero_page_two_X_aux R hX hXs pq h⟩
  asIso (HomologicalComplex.πStupidTrunc ((filteredSpaceSpectralSequence R hX).page 2 le_rfl)
      skeletalLineEmbedding) ≪≫
    (skeletalLineEmbedding.extendFunctor A).mapIso (restrictionIsoAux R hX hXs)

include hXs in
/-- On the line, `pageTwoIsoAux` is the identification of the first page with cellular chains. -/
private lemma pageTwoIsoAux_hom_f
    [∀ m, HasExactColimitsOfShape (Discrete (cell (Set.univ : Set B) m)) A] (n : ℕ) :
    (pageTwoIsoAux R hX hXs).hom.f (skeletalLineEmbedding.f n) =
      (firstPageXIsoAux R hX hXs _ n (by simp; lia) (by simp)).hom ≫
        eqToHom (cellularChainComplex_X _ R n).symm ≫
          ((cellularChainComplex (Set.univ : Set B) R).extendXIso
            skeletalLineEmbedding rfl).inv := by
  -- `stupidTrunc` is by definition the extension of the restriction, so the composite in
  -- `pageTwoIsoAux` is split by unification rather than by rewriting.
  rw [pageTwoIsoAux]
  refine (HomologicalComplex.comp_f _ _ _).trans ?_
  rw [asIso_hom, HomologicalComplex.πStupidTrunc_f, HomologicalComplex.πStupidTruncf_eq,
    Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ rfl]
  simp [restrictionIsoAux, HomologicalComplex.restrictionXIso]

end General

/-! ### The skeletal filtration -/

variable (B) in
/-- **The skeletal spectral sequence** of a CW complex `B` with coefficients in `R`: the spectral
sequence of the filtration of `B` by its skeleta (`TauCeti.preimageSkeleton` for the identity of
`B`), in the indexing of `TauCeti.filteredSpaceSpectralSequence`. -/
abbrev skeletalSpectralSequence :=
  filteredSpaceSpectralSequence R
    (monotone_preimageSkeleton (C := (Set.univ : Set B)) (id : TopCat.of B → B))

/-- The skeletal filtration of a CW complex `B` is the filtration by the skeleta of `B`. -/
private lemma skeletalFiltration_eq (q : ℤ) :
    preimageSkeleton (Set.univ : Set B) (id : TopCat.of B → B) q =
      skeletonLT (Set.univ : Set B) ((q + 1).toNat : ℕ∞) := by
  rw [preimageSkeleton_def, Set.preimage_id]

/-- **The first page of the skeletal filtration.** The object at `(1 - 2n, n - 1)` on the first
page of the spectral sequence of the skeletal filtration of a CW complex `B` is the relative
homology `Hₙ(Bⁿ, Bⁿ⁻¹)`, the cellular chain group of `B` in degree `n`. It is the identification
`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso` of the first page with relative homology,
followed by the equality of the pair `(B^(n-1+1), B^(n-1))` of the filtration with the pair of
consecutive skeleta. -/
def skeletalSpectralSequenceFirstPageXIso (n : ℕ) :
    ((skeletalSpectralSequence B R).page 2).X (skeletalLineEmbedding.f n) ≅
      (cellularChainComplex (Set.univ : Set B) R).X n :=
  firstPageXIsoAux R _ skeletalFiltration_eq _ n (by simp; lia) (by simp) ≪≫
    eqToIso (cellularChainComplex_X _ R n).symm

/-- `TauCeti.skeletalSpectralSequenceFirstPageXIso` is the identification
`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso` of the first page with relative homology,
followed by the transport along the equality of the pair of the filtration with the pair of
consecutive skeleta. -/
lemma skeletalSpectralSequenceFirstPageXIso_hom (n : ℕ) :
    (skeletalSpectralSequenceFirstPageXIso R n).hom =
      (filteredSpaceSpectralSequenceFirstPageXIso R
          (monotone_preimageSkeleton (C := (Set.univ : Set B)) (id : TopCat.of B → B))
          (skeletalLineEmbedding.f n) _ _ rfl rfl _ rfl n (by simp; lia)).hom ≫
        eqToHom ((congrArg (TopPair.singularHomology · R n) (TopPair.ofInclusion_congr _ _
          (by simp [preimageSkeleton_def]) (by simp [preimageSkeleton_def]))).trans
          (cellularChainComplex_X _ R n).symm) := by
  simp [skeletalSpectralSequenceFirstPageXIso, firstPageXIsoAux]

/-- **The first differential of the skeletal filtration is the cellular differential.** Under the
identifications `TauCeti.skeletalSpectralSequenceFirstPageXIso` of the first page with cellular
chains, the differential from `(-1 - 2n, n)` to `(1 - 2n, n - 1)` is the cellular differential
`Hₙ₊₁(Bⁿ⁺¹, Bⁿ) ⟶ Hₙ(Bⁿ, Bⁿ⁻¹)`. -/
theorem skeletalSpectralSequence_page_two_d_eq (n : ℕ) :
    ((skeletalSpectralSequence B R).page 2).d (skeletalLineEmbedding.f (n + 1))
        (skeletalLineEmbedding.f n) =
      (skeletalSpectralSequenceFirstPageXIso R (n + 1)).hom ≫
        (cellularChainComplex (Set.univ : Set B) R).d (n + 1) n ≫
          (skeletalSpectralSequenceFirstPageXIso R n).inv := by
  rw [page_two_d_eq_aux R _ skeletalFiltration_eq _ _ n (by simp; lia) (by simp) (by simp; lia)
    (by simp), cellularChainComplex_d]
  simp [skeletalSpectralSequenceFirstPageXIso]

variable [∀ m, HasExactColimitsOfShape (Discrete (cell (Set.univ : Set B) m)) A]

/-- **The first page of the skeletal filtration vanishes off the line** `n ↦ (1 - 2n, n - 1)`: the
relative homology `Hₙ(B^(q+1), B^(q))` of consecutive skeleta vanishes unless `n = q + 1`. -/
theorem isZero_skeletalSpectralSequence_page_two_X (pq : ℤ × ℤ)
    (h : ∀ n : ℕ, skeletalLineEmbedding.f n ≠ pq) :
    IsZero (((skeletalSpectralSequence B R).page 2).X pq) :=
  isZero_page_two_X_aux R _ skeletalFiltration_eq pq h

/-- **The first page of the skeletal filtration is the cellular chain complex.** The first page of
the spectral sequence of the skeletal filtration of a CW complex `B` is isomorphic to the cellular
chain complex of `B`, placed on the line `n ↦ (1 - 2n, n - 1)` and extended by zero. -/
def skeletalSpectralSequencePageTwoIso :
    (skeletalSpectralSequence B R).page 2 ≅
      (cellularChainComplex (Set.univ : Set B) R).extend skeletalLineEmbedding :=
  pageTwoIsoAux R _ skeletalFiltration_eq

/-- On the line, `TauCeti.skeletalSpectralSequencePageTwoIso` is the identification
`TauCeti.skeletalSpectralSequenceFirstPageXIso` of the first page with cellular chains. -/
lemma skeletalSpectralSequencePageTwoIso_hom_f (n : ℕ) :
    (skeletalSpectralSequencePageTwoIso (B := B) R).hom.f (skeletalLineEmbedding.f n) =
      (skeletalSpectralSequenceFirstPageXIso R n).hom ≫
        ((cellularChainComplex (Set.univ : Set B) R).extendXIso skeletalLineEmbedding rfl).inv := by
  rw [skeletalSpectralSequencePageTwoIso, pageTwoIsoAux_hom_f,
    skeletalSpectralSequenceFirstPageXIso, Iso.trans_hom, eqToIso.hom, Category.assoc]

/-- **The second page of the skeletal filtration is singular homology.** The object at
`(1 - 2n, n - 1)` on the page after the first (numbered `3`) of the spectral sequence of the
skeletal filtration of a CW complex `B` is the singular homology `Hₙ(B)`, provided the comparison
map `Hₙ(Bⁿ⁺¹) ⟶ Hₙ(B)` of the `(n + 1)`-skeleton with `B` is an isomorphism (as for
finite-dimensional complexes): it is the cellular homology of `B`, which is singular homology by
`TauCeti.cellularSingularHomologyIsoUniv`. -/
def skeletalSpectralSequencePageThreeXIso (n : ℕ)
    [IsIso ((skeletonBasePair (Set.univ : Set B) (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex (Set.univ : Set B) (n + 1)) R n)] :
    ((skeletalSpectralSequence B R).page 3).X (skeletalLineEmbedding.f n) ≅
      ((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of B) :=
  ((skeletalSpectralSequence B R).iso 2 3 _).symm ≪≫
    HomologicalComplex.homologyMapIso (skeletalSpectralSequencePageTwoIso R) _ ≪≫
      HomologicalComplex.extendHomologyIso _ _ rfl ≪≫ cellularSingularHomologyIsoUniv R n

/-- **The second page of the skeletal filtration vanishes off the line** `n ↦ (1 - 2n, n - 1)`,
since the first page does. -/
theorem isZero_skeletalSpectralSequence_page_three_X (pq : ℤ × ℤ)
    (h : ∀ n : ℕ, skeletalLineEmbedding.f n ≠ pq) :
    IsZero (((skeletalSpectralSequence B R).page 3).X pq) :=
  IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _
      (isZero_skeletalSpectralSequence_page_two_X R pq h))
    ((skeletalSpectralSequence B R).iso 2 3 pq).symm

end TauCeti
