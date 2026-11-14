/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.QuasiIso
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject
-- The comparison with the simplicial filtration unfolds its stages and its first-page
-- identification, and the quotient map `TopPair.singularRelπ` onto relative simplicial chains,
-- whose definitions are not exposed.
import all TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
import all TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic

/-!
# The cubical spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a fibration. The normalized cubical chains of
the `X q` form an increasing filtration of the normalized cubical chains of `Y`
(`TauCeti.cubicalChainFiltration`), since the push-forward along a subspace inclusion is injective
on normalized cubical chains. This file studies the spectral sequence of that filtered complex
(`TauCeti.filteredSpaceCubicalSpectralSequence`), the cubical counterpart of the spectral sequence
`TauCeti.filteredSpaceSpectralSequence` of the filtration of simplicial singular chains, and
compares the two.

* **Graded pieces.** The quotient `F_b / F_a` of two stages is the relative normalized cubical
  chain complex of the pair `(X b, X a)` (`TauCeti.cubicalChainFiltrationCokernelIso`).
* **First page.** The object at `(p, q)` on the first page (numbered `2`) is the relative cubical
  homology `Hₙ(X (q + 1), X q)` with `p + q = -n`
  (`TauCeti.filteredSpaceCubicalSpectralSequenceFirstPageXIso`).
* **Abutment and convergence.** The abutment in degree `-n` is the cubical homology `Hₙ(Y)`
  (`TauCeti.filteredSpaceCubicalAbutmentIso`), and the spectral sequence of a finite filtration
  converges strongly (`TauCeti.filteredSpaceCubicalSpectralSequencePageXIsoGradedOfFinite`).
* **Comparison.** The natural comparison map `TauCeti.cubicalToSingular` from normalized cubical
  to simplicial singular chains carries the chains of each `X q` into those of `X q`, so it is a
  morphism of filtered complexes (`TauCeti.filteredSpaceCubicalToSingular`). It is a
  quasi-isomorphism on every stage of the filtration, hence induces an isomorphism of spectral
  objects, and so an isomorphism between the cubical and the simplicial spectral sequences of the
  filtered space, on every page (`TauCeti.filteredSpaceCubicalSpectralSequenceIso`). No
  boundedness or exhaustiveness assumption on the filtration is needed. Under the identifications
  of the first pages with relative homology, this isomorphism is the map in homology of the
  relative comparison map `TopPair.cubicalToSingularRel`
  (`TauCeti.filteredSpaceCubicalSpectralSequenceIso_hom_two_f_comp`), and on the abutments the
  comparison is the map in homology of `TauCeti.cubicalToSingular`
  (`TauCeti.spectralObjectMap_filteredSpaceCubicalToSingular_abutment_comp`).

Applied to the filtration of the total space of a fibration by the preimages of the skeleta of the
base, this transports the Serre spectral sequence of simplicial singular chains to normalized
cubical chains, the chains on which twisted complexes with coefficients in DG local systems are
built.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II, where the spectral sequence of a fibration is built on cubical chains.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian.SpectralObject

universe u

namespace TauCeti

variable (k : Type u) [Ring k] {Y : TopCat.{u}} (X : ℤ → Set Y)

/-- The inclusion of the normalized cubical chains of `X q` into those of `Y`, with both chain
complexes reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def cubicalChainFiltrationι (q : ℤ) :
    ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset (X q)).snd).extend
        ComplexShape.embeddingDownNat ⟶
      ((normalizedCubicalChainComplex k).obj Y).extend ComplexShape.embeddingDownNat :=
  extendMap ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (X q)).map) _

/-- The normalized cubical chains of `X q` form a subcomplex of those of `Y`, also after
reindexing. -/
instance (q : ℤ) : Mono (cubicalChainFiltrationι k X q) :=
  HomologicalComplex.mono_extendMap _ _

/-- The filtration of the normalized cubical chains of `Y` by the normalized cubical chains of the
subsets `X q`, with the chain complexes reindexed as cochain complexes in nonpositive degrees
along `n ↦ -n`. -/
def cubicalChainFiltration (q : ℤ) :
    Subobject (((normalizedCubicalChainComplex k).obj Y).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (cubicalChainFiltrationι k X q)

/-- The `q`-th stage of the cubical filtration is the reindexed normalized cubical chain complex
of `X q`. -/
def cubicalChainFiltrationIso (q : ℤ) :
    (cubicalChainFiltration k X q : CochainComplex (ModuleCat.{u} k) ℤ) ≅
      ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset (X q)).snd).extend
        ComplexShape.embeddingDownNat :=
  Subobject.underlyingIso (cubicalChainFiltrationι k X q)

/-- The identification of the `q`-th stage of the cubical filtration with the cubical chains of
`X q` is compatible with the inclusions into the cubical chains of `Y`. -/
@[reassoc (attr := simp)]
lemma cubicalChainFiltrationIso_hom_comp_cubicalChainFiltrationι (q : ℤ) :
    (cubicalChainFiltrationIso k X q).hom ≫ cubicalChainFiltrationι k X q =
      (cubicalChainFiltration k X q).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {X}

/-- For `X a ⊆ X b`, the inclusion of the cubical chains of `X a` into those of `Y` factors
through the inclusion of the pair `(X b, X a)`. -/
@[simp, reassoc]
lemma extendMap_comp_cubicalChainFiltrationι {a b : ℤ} (hab : X a ⊆ X b) :
    extendMap ((normalizedCubicalChainComplex k).map (TopPair.ofInclusion hab).map)
        ComplexShape.embeddingDownNat ≫ cubicalChainFiltrationι k X b =
      cubicalChainFiltrationι k X a := by
  -- The ambient space of the pair `(X b, X a)` is the subspace `X b` of `Y` only up to
  -- definitional unfolding, so the composites are formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) <|
    ((normalizedCubicalChainComplex k).map_comp _ _).symm

/-- The cubical filtration is monotone in the subsets. -/
lemma cubicalChainFiltration_mono {a b : ℤ} (hab : X a ⊆ X b) :
    cubicalChainFiltration k X a ≤ cubicalChainFiltration k X b :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_cubicalChainFiltrationι k hab)

/-- Under the identifications of the stages of the cubical filtration with cubical chain
complexes, the inclusion `F_a ⟶ F_b` is induced by the inclusion `X a ⊆ X b`. -/
@[reassoc]
lemma ofLE_comp_cubicalChainFiltrationIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    Subobject.ofLE _ _ (cubicalChainFiltration_mono k hab) ≫
        (cubicalChainFiltrationIso k X b).hom =
      (cubicalChainFiltrationIso k X a).hom ≫
        extendMap ((normalizedCubicalChainComplex k).map (TopPair.ofInclusion hab).map)
          ComplexShape.embeddingDownNat :=
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := cubicalChainFiltrationι k X a) (f₂ := cubicalChainFiltrationι k X b) _
    (extendMap_comp_cubicalChainFiltrationι k hab)).trans (Category.assoc _ _ _).symm

/-- An increasing family of subsets gives an increasing filtration of cubical chains. -/
lemma monotone_cubicalChainFiltration (hX : Monotone X) :
    Monotone (cubicalChainFiltration k X) :=
  fun _ _ h ↦ cubicalChainFiltration_mono k (hX h)

/-- The stage of the cubical filtration at an empty subset is zero. -/
@[simp]
lemma cubicalChainFiltration_eq_bot {a : ℤ} (ha : X a = ∅) :
    cubicalChainFiltration k X a = ⊥ := by
  have : IsEmpty (TopPair.ofSubset (X a)).snd := by
    rw [ha]
    exact Set.isEmpty_coe_sort.2 rfl
  -- There are no singular cubes in the empty space `X a`, so its cubical chains vanish.
  have hz : IsZero ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset (X a)).snd) := by
    rw [IsZero.iff_id_eq_zero]
    ext n : 1
    have : IsEmpty (SingularCube (TopPair.ofSubset (X a)).snd n) :=
      ⟨fun c ↦ isEmptyElim (c fun _ ↦ 0)⟩
    have :
        Subsingleton (((normalizedCubicalChainComplex k).obj (TopPair.ofSubset (X a)).snd).X n) :=
      (normalizedCubicalChainComplexXEquiv (R := k) _ n).toEquiv.subsingleton_congr.2
        (Submodule.Quotient.mk_surjective _).subsingleton
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _
  exact Subobject.mk_eq_bot_iff_zero.2
    (((ComplexShape.embeddingDownNat.extendFunctor _).map_isZero hz).eq_of_src _ _)

/-- The stage of the cubical filtration at the whole space is everything. -/
@[simp]
lemma cubicalChainFiltration_eq_top {b : ℤ} (hb : X b = Set.univ) :
    cubicalChainFiltration k X b = ⊤ := by
  have : IsIso (TopPair.ofSubset (X b)).map := by
    refine TopCat.isIso_of_bijective_of_isOpenMap _ ⟨Subtype.val_injective, fun y ↦ ?_⟩
      (hb ▸ isOpen_univ : IsOpen (X b)).isOpenEmbedding_subtypeVal.isOpenMap
    exact ⟨⟨y, hb ▸ Set.mem_univ y⟩, rfl⟩
  have : IsIso (cubicalChainFiltrationι k X b) := by
    rw [cubicalChainFiltrationι]
    exact Functor.map_isIso (ComplexShape.embeddingDownNat.extendFunctor _) _
  exact Subobject.mk_eq_top_of_isIso _

/-- The quotient `F_b / F_a` of two stages of the cubical filtration is the relative normalized
cubical chain complex of the pair `(X b, X a)`, reindexed along `n ↦ -n`. The isomorphism is
induced by the quotient map from the cubical chains of `X b`
(`TauCeti.π_cubicalChainFiltrationCokernelIso_hom`). -/
def cubicalChainFiltrationCokernelIso {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel (Subobject.ofLE _ _ (cubicalChainFiltration_mono k hab)) ≅
      ((TopPair.ofInclusion hab).cubicalChainComplex k).extend ComplexShape.embeddingDownNat :=
  have hS := ((TopPair.ofInclusion hab).shortExact_cubicalChainComplexShortComplex k).extend
    ComplexShape.embeddingDownNat
  cokernel.mapIso _
      (extendMap ((normalizedCubicalChainComplex k).map (TopPair.ofInclusion hab).map)
        ComplexShape.embeddingDownNat)
      (cubicalChainFiltrationIso k X a) (cubicalChainFiltrationIso k X b)
      (ofLE_comp_cubicalChainFiltrationIso_hom k hab) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hS.gIsCokernel

/-- The identification of `F_b / F_a` with relative cubical chains is induced by the quotient map
from the cubical chains of `X b` to those of the pair `(X b, X a)`. -/
@[reassoc (attr := simp)]
lemma π_cubicalChainFiltrationCokernelIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel.π _ ≫ (cubicalChainFiltrationCokernelIso k hab).hom =
      (cubicalChainFiltrationIso k X b).hom ≫
        extendMap (cokernel.π ((normalizedCubicalChainComplex k).map (TopPair.ofInclusion hab).map))
          ComplexShape.embeddingDownNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

variable (hX : Monotone X)

/-- The quotient of two stages of the cubical filtration, as the cokernel of a transition map of
its filtration functor, is the reindexed relative cubical chain complex of the corresponding
pair. -/
private def cubicalCokernelFiltrationFunctorMapIso {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel ((CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX)).map f) ≅
      ((TopPair.ofInclusion (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).cubicalChainComplex
        k).extend ComplexShape.embeddingDownNat :=
  cokernel.mapIso _ _
      (CochainComplex.filtrationFunctorObjIso _ _ a ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ a))
      (CochainComplex.filtrationFunctorObjIso _ _ b ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ b))
      (by simp only [Iso.trans_hom, Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE,
        reassoc_of% CochainComplex.filtrationFunctor_map_comp_objIso_hom, Category.assoc]) ≪≫
    cubicalChainFiltrationCokernelIso k _

/-- The identification of the cokernel of a transition map of the filtration functor with
relative cubical chains is induced by the quotient map from the cubical chains of the larger
subset. -/
@[reassoc]
private lemma π_cubicalCokernelFiltrationFunctorMapIso_hom {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.π _ ≫ (cubicalCokernelFiltrationFunctorMapIso k hX f).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (cubicalChainFiltrationIso k X b).hom ≫
            extendMap (cokernel.π ((normalizedCubicalChainComplex k).map
              (TopPair.ofInclusion (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).map))
              ComplexShape.embeddingDownNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ _ ≫ ·) (π_cubicalChainFiltrationCokernelIso_hom k _)

/-- **The cubical spectral sequence of a filtered space.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the filtration of the
normalized cubical chains of `Y` by the normalized cubical chains of the `X q`, in the
cohomological indexing of `CochainComplex.spectralSequence`: chains in degree `n` sit in degree
`-n`. -/
abbrev filteredSpaceCubicalSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX))

/-- **The first page of the cubical spectral sequence of a filtered space.** The object at
`(p, q)` on the first page (numbered `2`, as in `CochainComplex.spectralSequence`) is the relative
cubical homology `Hₙ(X (q + 1), X q)`, where `p + q = -n`. The indices `q`, `q + 1` and `p + q`
are given as `a`, `b` and `m` together with equations, for flexibility. -/
def filteredSpaceCubicalSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((filteredSpaceCubicalSpectralSequence k hX).page 2).X pq ≅
      ((TopPair.ofInclusion (hX (by lia : a ≤ b))).cubicalChainComplex k).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq a b ha hb m hm ≪≫
    (homologyFunctor _ _ _).mapIso (cubicalCokernelFiltrationFunctorMapIso k hX _) ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat hn.symm

/-- **The abutment of the cubical spectral sequence of a filtered space** in degree `-n` is the
cubical homology `Hₙ(Y)`. -/
def filteredSpaceCubicalAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX))).abutment
        (-n) ≅
      ((normalizedCubicalChainComplex k).obj Y).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

/-- **Strong convergence of the cubical spectral sequence of a finite filtration of a space.** If
`X a = ∅` and `X b` is all of `Y`, then on every page `r ≥ 2` with `q - r + 2 ≤ a` and
`b ≤ q + r - 1`, the object at `(p, q)` is the graded piece `F_{q+1} H / F_q H` of the filtration of
the abutment in degree `p + q`, which is the cubical homology `H_{-(p+q)}(Y)` by
`TauCeti.filteredSpaceCubicalAbutmentIso`. -/
def filteredSpaceCubicalSpectralSequencePageXIsoGradedOfFinite {a b : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((filteredSpaceCubicalSpectralSequence k hX).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_cubicalChainFiltration k hX))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (cubicalChainFiltration_eq_bot k ha) (cubicalChainFiltration_eq_top k hb) r hr pq hra hrb

/-! ### Comparison with the simplicial spectral sequence -/

/-- The comparison map from normalized cubical to simplicial singular chains of a space `Z`,
reindexed along `n ↦ -n`, with its target written as in `TauCeti.singularChainFiltration`. -/
private abbrev cubicalToSingularExtend (Z : TopCat.{u}) :
    ((normalizedCubicalChainComplex k).obj Z).extend ComplexShape.embeddingDownNat ⟶
      ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of k k)).extend
        ComplexShape.embeddingDownNat :=
  extendMap ((cubicalToSingular k).app Z) ComplexShape.embeddingDownNat

private instance (Z : TopCat.{u}) : QuasiIso (cubicalToSingularExtend k Z) :=
  inferInstanceAs (QuasiIso (extendMap ((cubicalToSingular k).app Z) _))

/-- The comparison maps are natural in the space. -/
private lemma cubicalToSingularExtend_naturality {Z Z' : TopCat.{u}} (g : Z ⟶ Z') :
    extendMap ((normalizedCubicalChainComplex k).map g) ComplexShape.embeddingDownNat ≫
        cubicalToSingularExtend k Z' =
      cubicalToSingularExtend k Z ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of k k))
          ComplexShape.embeddingDownNat :=
  -- The target of `cubicalToSingular` is `singularChains k`, which is the simplicial chain
  -- complex of the singular set only up to unfolding, so the composites are formed with terms.
  (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · _) ((cubicalToSingular k).naturality g)).trans (extendMap_comp _ _ _)

variable (X) in
/-- The comparison maps carry the inclusion of the cubical chains of `X n` into those of `Y` to
the inclusion of the simplicial chains. -/
private lemma cubicalChainFiltrationι_comp_cubicalToSingularExtend (n : ℤ) :
    cubicalChainFiltrationι k X n ≫ cubicalToSingularExtend k Y =
      cubicalToSingularExtend k _ ≫ singularChainFiltrationι (ModuleCat.of k k) X n := by
  rw [singularChainFiltrationι_def]
  exact cubicalToSingularExtend_naturality k _

variable (X) in
/-- The comparison map from normalized cubical to simplicial singular chains carries the cubical
chains of `X n` into the simplicial chains of `X n`. -/
private lemma cubicalToSingular_factors_singularChainFiltration (n : ℤ) :
    (singularChainFiltration (ModuleCat.of k k) X n).Factors
      ((cubicalChainFiltration k X n).arrow ≫ cubicalToSingularExtend k Y) := by
  have e : (cubicalChainFiltration k X n).arrow ≫ cubicalToSingularExtend k Y =
      ((cubicalChainFiltrationIso k X n).hom ≫ cubicalToSingularExtend k _ ≫
        (singularChainFiltrationIso (ModuleCat.of k k) X n).inv) ≫
          (singularChainFiltration (ModuleCat.of k k) X n).arrow := by
    rw [Category.assoc, Category.assoc,
      ← singularChainFiltrationIso_hom_comp_singularChainFiltrationι, Iso.inv_hom_id_assoc,
      ← cubicalChainFiltrationι_comp_cubicalToSingularExtend, ← Category.assoc,
      cubicalChainFiltrationIso_hom_comp_cubicalChainFiltrationι]
  rw [e]
  exact Subobject.factors_comp_arrow _

/-- **The comparison of the cubical and simplicial filtrations of a filtered space**: the
morphism of filtration functors induced by the natural comparison map `TauCeti.cubicalToSingular`
from normalized cubical to simplicial singular chains, which carries the cubical chains of each
`X q` into the simplicial chains of `X q`. -/
def filteredSpaceCubicalToSingular :
    CochainComplex.filtrationFunctor _ (monotone_cubicalChainFiltration k hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_singularChainFiltration (ModuleCat.of k k) hX) :=
  CochainComplex.filtrationFunctorMap _ _ (cubicalToSingularExtend k Y)
    (cubicalToSingular_factors_singularChainFiltration k X)

/-- The comparison of the cubical and simplicial filtrations is the restriction of the comparison
map `TauCeti.cubicalToSingular` of `Y` to the stages of the filtrations. -/
@[reassoc]
lemma filteredSpaceCubicalToSingular_app_comp (a : EInt) :
    (filteredSpaceCubicalToSingular k hX).app a ≫
        CochainComplex.filtrationFunctorArrow _
          (monotone_singularChainFiltration (ModuleCat.of k k) hX) a =
      CochainComplex.filtrationFunctorArrow _ (monotone_cubicalChainFiltration k hX) a ≫
        extendMap ((cubicalToSingular k).app Y) ComplexShape.embeddingDownNat :=
  (CochainComplex.filtrationFunctorMap_app_comp
    (hF := monotone_cubicalChainFiltration k hX)
    (hG := monotone_singularChainFiltration (ModuleCat.of k k) hX) _
    (cubicalToSingular_factors_singularChainFiltration k X) a).trans (Category.assoc _ _ _).symm

/-- On the `n`-th stage, the comparison of the cubical and simplicial filtrations is the
comparison map `TauCeti.cubicalToSingular` of `X n`, under the identifications of the stages with
the chains of `X n`. -/
private lemma filteredSpaceCubicalToSingular_app_comp_filtrationFunctorObjIsoOfEqMk_hom (n : ℤ) :
    (filteredSpaceCubicalToSingular k hX).app n ≫
        (CochainComplex.filtrationFunctorObjIsoOfEqMk _
          (monotone_singularChainFiltration (ModuleCat.of k k) hX)
          (singularChainFiltrationι (ModuleCat.of k k) X)
          (fun _ ↦ by rw [singularChainFiltration]) n).hom =
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (monotone_cubicalChainFiltration k hX)
          (cubicalChainFiltrationι k X)
          (fun _ ↦ by rw [cubicalChainFiltration]) n).hom ≫ cubicalToSingularExtend k _ := by
  rw [← cancel_mono (singularChainFiltrationι (ModuleCat.of k k) X n), Category.assoc,
    Category.assoc, ← cubicalChainFiltrationι_comp_cubicalToSingularExtend]
  simp only [CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp,
    CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp_assoc]
  exact filteredSpaceCubicalToSingular_app_comp k hX n

/-- The comparison of the cubical and simplicial filtrations is a quasi-isomorphism on every
stage, including the zero stage `⊥` and the whole complex `⊤`. -/
instance quasiIso_filteredSpaceCubicalToSingular_app (a : EInt) :
    QuasiIso ((filteredSpaceCubicalToSingular k hX).app a) := by
  refine CochainComplex.quasiIso_filtrationFunctorMap_app _ _ _ _ (fun n ↦ ?_) a
  have h : QuasiIso ((filteredSpaceCubicalToSingular k hX).app n ≫
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _
        (monotone_singularChainFiltration (ModuleCat.of k k) hX)
        (singularChainFiltrationι (ModuleCat.of k k) X)
        (fun _ ↦ by rw [singularChainFiltration]) n).hom) := by
    rw [filteredSpaceCubicalToSingular_app_comp_filtrationFunctorObjIsoOfEqMk_hom]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).1 h

/-- **The cubical and simplicial spectral objects of a filtered space are isomorphic** through the
comparison map `TauCeti.cubicalToSingular`. -/
instance isIso_spectralObjectMap_filteredSpaceCubicalToSingular :
    IsIso (CochainComplex.spectralObjectMap (filteredSpaceCubicalToSingular k hX)) :=
  CochainComplex.isIso_spectralObjectMap_of_quasiIso _

/-- **The cubical and simplicial spectral sequences of a filtered space are isomorphic.** The
natural comparison map `TauCeti.cubicalToSingular` from normalized cubical to simplicial singular
chains induces an isomorphism, on every page, between the spectral sequence of the filtration of
the normalized cubical chains of `Y` by those of the `X q` and the spectral sequence of the
filtration of the simplicial singular chains of `Y` by those of the `X q`. -/
def filteredSpaceCubicalSpectralSequenceIso :
    filteredSpaceCubicalSpectralSequence k hX ≅
      filteredSpaceSpectralSequence (ModuleCat.of k k) hX :=
  asIso (spectralSequenceMap coreE₂Cohomological
    (CochainComplex.spectralObjectMap (filteredSpaceCubicalToSingular k hX)))

/-- The isomorphism between the cubical and simplicial spectral sequences of a filtered space is
the morphism of spectral sequences induced by the comparison of the filtrations. -/
@[simp]
lemma filteredSpaceCubicalSpectralSequenceIso_hom :
    (filteredSpaceCubicalSpectralSequenceIso k hX).hom =
      spectralSequenceMap coreE₂Cohomological
        (CochainComplex.spectralObjectMap (filteredSpaceCubicalToSingular k hX)) :=
  (rfl)

/-- On the graded pieces of the filtrations, the comparison of the cubical and simplicial
filtrations is the relative comparison map `TopPair.cubicalToSingularRel`. -/
private lemma cokernel_map_filteredSpaceCubicalToSingular_comp {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.map _ _ _ _ ((filteredSpaceCubicalToSingular k hX).naturality f) ≫
        (cokernelFiltrationFunctorMapIso (ModuleCat.of k k) hX f).hom =
      (cubicalCokernelFiltrationFunctorMapIso k hX f).hom ≫
        extendMap (TopPair.cubicalToSingularRel k _) ComplexShape.embeddingDownNat := by
  have hι : (filteredSpaceCubicalToSingular k hX).app b ≫
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (singularChainFiltrationIso (ModuleCat.of k k) X b).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (cubicalChainFiltrationIso k X b).hom ≫ cubicalToSingularExtend k _ := by
    rw [← cancel_mono (singularChainFiltrationι (ModuleCat.of k k) X b)]
    simp only [Category.assoc, ← cubicalChainFiltrationι_comp_cubicalToSingularExtend,
      singularChainFiltrationIso_hom_comp_singularChainFiltrationι,
      cubicalChainFiltrationIso_hom_comp_cubicalChainFiltrationι_assoc, Subobject.ofLE_arrow,
      Subobject.ofLE_arrow_assoc]
    exact filteredSpaceCubicalToSingular_app_comp k hX b
  have hπ (hab : X a ⊆ X b) :
      extendMap (cokernel.π ((normalizedCubicalChainComplex k).map (TopPair.ofInclusion hab).map))
          ComplexShape.embeddingDownNat ≫
        extendMap (TopPair.cubicalToSingularRel k (TopPair.ofInclusion hab))
          ComplexShape.embeddingDownNat =
      cubicalToSingularExtend k _ ≫
        extendMap ((TopPair.ofInclusion hab).singularChainComplexπ (ModuleCat.of k k))
          ComplexShape.embeddingDownNat :=
    (extendMap_comp _ _ _).symm.trans <|
      (congrArg (extendMap · _) (TopPair.π_cubicalToSingularRel k _)).trans (extendMap_comp _ _ _)
  refine (cancel_epi (cokernel.π _)).1 ?_
  -- The ambient space of the pair `(X b, X a)` is the subspace `X b` of `Y` only up to
  -- definitional unfolding, so the composites are formed with terms rather than `rw`.
  exact (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (π_cokernelFiltrationFunctorMapIso_hom _ hX f)).trans <|
    ((reassoc_of% hι) _).trans <| (congrArg (_ ≫ _ ≫ ·)
      ((congrArg (_ ≫ ·) (hπ _).symm).trans (Category.assoc _ _ _).symm)).trans
        (π_cubicalCokernelFiltrationFunctorMapIso_hom_assoc k hX f _).symm

/-- **The comparison of the cubical and simplicial spectral sequences on the first page.** Under
the identifications of the objects of the first pages with relative cubical and relative
simplicial homology, the isomorphism `TauCeti.filteredSpaceCubicalSpectralSequenceIso` is the map
in homology of the relative comparison map `TopPair.cubicalToSingularRel`, an isomorphism by
`TopPair.quasiIso_cubicalToSingularRel`. -/
@[reassoc]
lemma filteredSpaceCubicalSpectralSequenceIso_hom_two_f_comp (pq : ℤ × ℤ) (a b : ℤ)
    (ha : a = pq.2) (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((filteredSpaceCubicalSpectralSequenceIso k hX).hom.hom 2 le_rfl).f pq ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of k k) hX pq a b ha hb m hm n
          hn).hom =
      (filteredSpaceCubicalSpectralSequenceFirstPageXIso k hX pq a b ha hb m hm n hn).hom ≫
        homologyMap (TopPair.cubicalToSingularRel k (TopPair.ofInclusion (hX (by lia : a ≤ b))))
          n := by
  have h := (homologyMap_comp _ _ m).symm.trans <| (congrArg (homologyMap · m)
    (cokernel_map_filteredSpaceCubicalToSingular_comp k hX
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one ha hb)))).trans (homologyMap_comp _ _ m)
  -- The first-page identifications are composites of isomorphisms whose types mention the pair
  -- `(X b, X a)` only up to definitional unfolding, so they are composed with terms.
  have e := CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality
    (filteredSpaceCubicalToSingular k hX) pq a b ha hb m hm
  exact ((reassoc_of% e) _).trans <|
    (congrArg (_ ≫ ·) <| ((reassoc_of% h) _).trans <|
      congrArg (_ ≫ ·) (extendHomologyIso_hom_naturality _ _ _)).trans <|
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

/-- **The comparison of the cubical and simplicial abutments.** Under the identifications of the
abutments in degree `-n` with the cubical and the simplicial homology `Hₙ(Y)`, the morphism of
spectral objects induced by the comparison of the filtrations is the map in homology of the
comparison map `TauCeti.cubicalToSingular` of `Y`. -/
@[reassoc]
lemma spectralObjectMap_filteredSpaceCubicalToSingular_abutment_comp (n : ℕ) :
    ((CochainComplex.spectralObjectMap (filteredSpaceCubicalToSingular k hX)).hom (-n)).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (filteredSpaceAbutmentIso (ModuleCat.of k k) hX n).hom =
      (filteredSpaceCubicalAbutmentIso k hX n).hom ≫ homologyMap ((cubicalToSingular k).app Y) n :=
  ((CochainComplex.spectralObjectMap_filtrationFunctorMap_abutment_comp_assoc _ _ _ _ _ _).trans
    (congrArg (_ ≫ ·) (extendHomologyIso_hom_naturality _ _ _))).trans (Category.assoc _ _ _).symm

end TauCeti
