/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.TopColumn
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.Topology.Category.TopPair
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Category.ModuleCat.Range
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The spectral sequence of a filtered space for a chain functor

Let `F : TopCat ⥤ ChainComplex A ℕ` be a functor sending inclusions of subspaces to
monomorphisms, such as simplicial singular chains or normalized cubical chains, and let
`X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`. The chains
`F (X q)` form an increasing filtration of `F Y` (`TauCeti.chainFiltration`), and this file
studies the spectral sequence of that filtered complex
(`TauCeti.chainFiltrationSpectralSequence`). It is the spectral sequence of a filtered complex
from `TauCeti.Algebra.Homology.SpectralSequence.Filtered`, which uses cochain complexes indexed by
`ℤ`, so chains in degree `n` are placed in degree `-n` along `ComplexShape.embeddingDownNat`.

* **Stages.** The identification of the stages with the chains of the `X q`
  (`TauCeti.chainFiltrationIso`) and the extreme stages (`TauCeti.chainFiltration_eq_bot_of_isZero`,
  `TauCeti.chainFiltration_eq_bot`, `TauCeti.chainFiltration_eq_top`).
* **Graded pieces.** The quotient `F_b / F_a` of two stages of the filtration is the cokernel of
  the map `F (X a) ⟶ F (X b)` (`TauCeti.chainFiltrationCokernelIso`), so its cohomology
  vanishes where the homology of that cokernel does
  (`TauCeti.isZero_homology_cokernel_chainFiltration`).
* **First page.** The object at `(p, q)` on the first page (numbered `2` in the indexing of
  `CochainComplex.spectralSequence`) is the homology in degree `n` of that cokernel for the pair
  `(X (q + 1), X q)`, with `p + q = -n` (`TauCeti.chainFiltrationSpectralSequenceFirstPageXIso`).
* **Convergence.** The abutment in degree `-n` is `Hₙ(F Y)`
  (`TauCeti.chainFiltrationAbutmentIso`), and the `q`th piece of its filtration is the image of
  `Hₙ(F (X q)) ⟶ Hₙ(F Y)`
  (`TauCeti.chainFiltrationToAbutmentFiltration_comp_chainFiltrationAbutmentIso_hom`,
  `TauCeti.range_abutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom`). When
  `X (q + 1) = Y`, the projection of `Hₙ(F Y)` onto the limit object `E∞` at `q`
  (`TauCeti.chainFiltrationToTopColumnEInfty`) vanishes exactly on the image of `Hₙ(F (X q))`
  (`TauCeti.chainFiltrationToTopColumnEInfty_eq_zero_iff`). When
  `X a = ∅`, `F` vanishes on empty spaces and `X b = Y`, the filtration is finite and the
  spectral sequence converges strongly
  (`TauCeti.chainFiltrationSpectralSequencePageXIsoGradedOfFinite`).
* **Maps.** A natural transformation `α : F ⟶ G` together with a map of filtered spaces induces a
  morphism of filtrations (`TauCeti.chainFiltrationMap`), functorial in both
  (`TauCeti.chainFiltrationMap_id`, `TauCeti.chainFiltrationMap_comp`), which is a
  quasi-isomorphism on every stage when `α` is one on every space
  (`TauCeti.quasiIso_chainFiltrationMap_app`). On the abutment the induced morphism is the map in
  homology induced by `F.map g ≫ α.app Y'` (`TauCeti.chainFiltrationAbutmentIso_hom_naturality`).
  For the identity of `Y`, on the first page and on the abutment the induced morphism is the map in
  homology induced by `α` (`TauCeti.spectralSequenceMap_chainFiltrationMap_two_f_comp` and
  `TauCeti.spectralObjectMap_chainFiltrationMap_abutment_comp`).

The simplicial singular instance is `TauCeti.filteredSpaceSpectralSequence`, and the normalized
cubical instance is compared with it in `TauCeti.AlgebraicTopology.Singular.Cubical.FilteredSpace`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex, and Chapter 5, its application to the
  filtration of a total space by the preimages of the skeleta of the base.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian.SpectralObject

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [Abelian A] {Y : TopCat.{w}}

section ChainFunctor

variable (F : TopCat.{w} ⥤ ChainComplex A ℕ) (X : ℤ → Set Y)

/-- The inclusion of the chains `F (X q)` of `X q` into the chains `F Y` of `Y`, for a functor `F`
from spaces to chain complexes such as singular or cubical chains, with both chain complexes
reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def chainFiltrationι (q : ℤ) :
    (F.obj (TopPair.ofSubset (X q)).snd).extend ComplexShape.embeddingDownNat ⟶
      (F.obj Y).extend ComplexShape.embeddingDownNat :=
  extendMap (F.map (TopPair.ofSubset (X q)).map) _

/-- The inclusion of the chains of `X q` into those of `Y` is induced by the inclusion of the
subspace `X q`. -/
lemma chainFiltrationι_def (q : ℤ) :
    chainFiltrationι F X q =
      extendMap (F.map (TopPair.ofSubset (X q)).map) ComplexShape.embeddingDownNat :=
  (rfl)

variable [∀ P : TopPair.{w}, Mono (F.map P.map)]

/-- When `F` sends subspace inclusions to monomorphisms, the chains of `X q` form a subcomplex of
those of `Y`, also after reindexing. -/
instance (q : ℤ) : Mono (chainFiltrationι F X q) := by
  rw [chainFiltrationι_def]
  exact HomologicalComplex.mono_extendMap _ _

/-- The filtration of the chains `F Y` of `Y` by the chains `F (X q)` of the subsets `X q`, with
the chain complexes reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def chainFiltration (q : ℤ) : Subobject ((F.obj Y).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (chainFiltrationι F X q)

/-- The `q`-th stage of the filtration is the subobject given by the inclusion of the chains of
`X q`. -/
lemma chainFiltration_def (q : ℤ) : chainFiltration F X q = Subobject.mk (chainFiltrationι F X q) :=
  (rfl)

/-- The `q`-th stage of the filtration is the reindexed chain complex of `X q`. -/
def chainFiltrationIso (q : ℤ) :
    (chainFiltration F X q : CochainComplex A ℤ) ≅
      (F.obj (TopPair.ofSubset (X q)).snd).extend ComplexShape.embeddingDownNat :=
  Subobject.underlyingIso (chainFiltrationι F X q)

/-- The identification of the `q`-th stage of the filtration with the chains of `X q` is
compatible with the inclusions into the chains of `Y`. -/
@[reassoc (attr := simp)]
lemma chainFiltrationIso_hom_comp_chainFiltrationι (q : ℤ) :
    (chainFiltrationIso F X q).hom ≫ chainFiltrationι F X q = (chainFiltration F X q).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {X}

omit [∀ P : TopPair.{w}, Mono (F.map P.map)] in
/-- For `X a ⊆ X b`, the inclusion of the chains of `X a` into those of `Y` factors through the
inclusion of the pair `(X b, X a)`. -/
@[simp, reassoc]
lemma extendMap_comp_chainFiltrationι {a b : ℤ} (hab : X a ⊆ X b) :
    extendMap (F.map (TopPair.ofInclusion hab).map) ComplexShape.embeddingDownNat ≫
        chainFiltrationι F X b =
      chainFiltrationι F X a :=
  -- The composite of the inclusions `X a ⊆ X b ⊆ Y` is the inclusion of `X a` by definition.
  (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) (Functor.map_comp _ _ _).symm

/-- The filtration of chains is monotone in the subsets. -/
lemma chainFiltration_mono {a b : ℤ} (hab : X a ⊆ X b) :
    chainFiltration F X a ≤ chainFiltration F X b :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_chainFiltrationι F hab)

/-- Under the identifications of the stages of the filtration with chain complexes, the inclusion
`F_a ⟶ F_b` is induced by the inclusion `X a ⊆ X b`. -/
@[reassoc]
lemma ofLE_comp_chainFiltrationIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    Subobject.ofLE _ _ (chainFiltration_mono F hab) ≫ (chainFiltrationIso F X b).hom =
      (chainFiltrationIso F X a).hom ≫
        extendMap (F.map (TopPair.ofInclusion hab).map) ComplexShape.embeddingDownNat :=
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := chainFiltrationι F X a) (f₂ := chainFiltrationι F X b) _
    (extendMap_comp_chainFiltrationι F hab)).trans (Category.assoc _ _ _).symm

/-- An increasing family of subsets gives an increasing filtration of chains. -/
lemma monotone_chainFiltration (hX : Monotone X) : Monotone (chainFiltration F X) :=
  fun _ _ h ↦ chainFiltration_mono F (hX h)

/-- The stage of the filtration at a subset with zero chains is zero. -/
lemma chainFiltration_eq_bot_of_isZero {a : ℤ}
    (ha : IsZero (F.obj (TopPair.ofSubset (X a)).snd)) : chainFiltration F X a = ⊥ :=
  Subobject.mk_eq_bot_iff_zero.2 <|
    ((ComplexShape.embeddingDownNat.extendFunctor A).map_isZero ha).eq_of_src _ _

/-- The stage of the filtration at an empty subset is zero, when `F` has zero chains on empty
spaces. -/
lemma chainFiltration_eq_bot (hF : ∀ Z : TopCat.{w}, IsEmpty Z → IsZero (F.obj Z)) {a : ℤ}
    (ha : X a = ∅) : chainFiltration F X a = ⊥ :=
  chainFiltration_eq_bot_of_isZero F (hF _ (by rw [ha]; exact Set.isEmpty_coe_sort.2 rfl))

/-- The stage of the filtration at the whole space is everything. -/
@[simp]
lemma chainFiltration_eq_top {b : ℤ} (hb : X b = Set.univ) : chainFiltration F X b = ⊤ := by
  have := TopPair.isIso_ofSubset_map_of_eq_univ hb
  have : IsIso (chainFiltrationι F X b) := by
    rw [chainFiltrationι]
    exact Functor.map_isIso (ComplexShape.embeddingDownNat.extendFunctor A) _
  exact Subobject.mk_eq_top_of_isIso _

/-- **The abutment of the spectral sequence of a filtered space** in degree `-n` is the homology
`Hₙ(F Y)` of the chains of `Y`; for singular chains, this is the singular homology of `Y`. -/
def chainFiltrationAbutmentIso (hX : Monotone X) (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_chainFiltration F hX))).abutment (-n) ≅
      (F.obj Y).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

/-- The quotient `F_b / F_a` of two stages of the filtration is the cokernel of the map
`F (X a) ⟶ F (X b)`, reindexed along `n ↦ -n`. The isomorphism is induced by the quotient map
from `F (X b)` (`TauCeti.π_chainFiltrationCokernelIso_hom`). -/
def chainFiltrationCokernelIso {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel (Subobject.ofLE _ _ (chainFiltration_mono F hab)) ≅
      (cokernel (F.map (TopPair.ofInclusion hab).map)).extend ComplexShape.embeddingDownNat :=
  cokernel.mapIso _
      (extendMap (F.map (TopPair.ofInclusion hab).map) ComplexShape.embeddingDownNat)
      (chainFiltrationIso F X a) (chainFiltrationIso F X b)
      (ofLE_comp_chainFiltrationIso_hom F hab) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      ((cokernelSequence_shortExact (F.map (TopPair.ofInclusion hab).map)).extend
        ComplexShape.embeddingDownNat).gIsCokernel

/-- The identification of `F_b / F_a` with the cokernel of `F (X a) ⟶ F (X b)` is induced by the
quotient map from `F (X b)`. -/
@[reassoc (attr := simp)]
lemma π_chainFiltrationCokernelIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel.π _ ≫ (chainFiltrationCokernelIso F hab).hom =
      (chainFiltrationIso F X b).hom ≫
        extendMap (cokernel.π (F.map (TopPair.ofInclusion hab).map))
          ComplexShape.embeddingDownNat :=
  -- The first factor is `cokernel.map`, which is `cokernel.desc` of the composite with the
  -- quotient map, and the second sends that quotient map to the cokernel cofork's map.
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

/-- The quotient `F_b / F_a` of two stages of the filtration has vanishing cohomology in degree
`m` when the homology in degree `n` of the cokernel of `F (X a) ⟶ F (X b)` vanishes for `m = -n`.
In positive degrees `m` there is nothing to check. -/
lemma isZero_homology_cokernel_chainFiltration {a b : ℤ} (hab : X a ⊆ X b) (m : ℤ)
    (h : ∀ n : ℕ, m = -n → IsZero ((cokernel (F.map (TopPair.ofInclusion hab).map)).homology n)) :
    IsZero ((cokernel (Subobject.ofLE _ _ (chainFiltration_mono F hab))).homology m) := by
  refine IsZero.of_iso ?_ ((homologyFunctor A _ m).mapIso (chainFiltrationCokernelIso F hab))
  by_cases hm : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = m
  · obtain ⟨n, hn⟩ := hm
    exact (h n hn.symm).of_iso (extendHomologyIso _ _ hn)
  · push Not at hm
    exact (extend_exactAt _ _ m hm).isZero_homology

variable (hX : Monotone X)

/-- The quotient of two stages of the filtration, as the cokernel of a transition map of the
functor `CochainComplex.filtrationFunctor` of the filtration, is the reindexed cokernel of the map
of chains induced by the corresponding pair. -/
def chainFiltrationCokernelFiltrationFunctorMapIso {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel ((CochainComplex.filtrationFunctor _ (monotone_chainFiltration F hX)).map f) ≅
      (cokernel (F.map (TopPair.ofInclusion
        (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).map)).extend ComplexShape.embeddingDownNat :=
  cokernel.mapIso _ _
      (CochainComplex.filtrationFunctorObjIso _ _ a ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ a))
      (CochainComplex.filtrationFunctorObjIso _ _ b ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ b))
      (by simp only [Iso.trans_hom, Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE,
        reassoc_of% CochainComplex.filtrationFunctor_map_comp_objIso_hom, Category.assoc]) ≪≫
    chainFiltrationCokernelIso F _

/-- The identification of the cokernel of a transition map of the filtration functor with the
cokernel of the map of chains of the pair is induced by the quotient map from the chains of the
larger subset. -/
@[reassoc (attr := simp)]
lemma π_chainFiltrationCokernelFiltrationFunctorMapIso_hom {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.π _ ≫ (chainFiltrationCokernelFiltrationFunctorMapIso F hX f).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (chainFiltrationIso F X b).hom ≫
            extendMap (cokernel.π (F.map (TopPair.ofInclusion
              (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).map))
              ComplexShape.embeddingDownNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ _ ≫ ·) (π_chainFiltrationCokernelIso_hom F _)

/-- **The spectral sequence of a filtered space for a chain functor `F`.** For an increasing
family `X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the filtration
of the chains `F Y` by the chains `F (X q)`, in the cohomological indexing of
`CochainComplex.spectralSequence`: chains in degree `n` sit in degree `-n`. -/
abbrev chainFiltrationSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _ (monotone_chainFiltration F hX))

/-- **The first page of the spectral sequence of a filtered space.** The object at `(p, q)` on the
first page (numbered `2`, as in `CochainComplex.spectralSequence`) is the homology in degree `n` of
the cokernel of `F (X q) ⟶ F (X (q + 1))`, where `p + q = -n`. The indices `q`, `q + 1` and
`p + q` are given as `a`, `b` and `m` together with equations, for flexibility. -/
def chainFiltrationSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((chainFiltrationSpectralSequence F hX).page 2).X pq ≅
      (cokernel (F.map (TopPair.ofInclusion (hX (by lia : a ≤ b))).map)).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq a b ha hb m hm ≪≫
    (homologyFunctor A _ _).mapIso (chainFiltrationCokernelFiltrationFunctorMapIso F hX _) ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat hn.symm

/-- The identification of the first page is the identification
`CochainComplex.spectralSequenceFirstPageXIsoCokernel` of the first page with the homology of a
graded piece, followed by the identification of that graded piece with the cokernel of the map of
chains of the pair. -/
lemma chainFiltrationSpectralSequenceFirstPageXIso_eq (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    chainFiltrationSpectralSequenceFirstPageXIso F hX pq a b ha hb m hm n hn =
      CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq a b ha hb m hm ≪≫
        (homologyFunctor A _ _).mapIso (chainFiltrationCokernelFiltrationFunctorMapIso F hX _) ≪≫
        extendHomologyIso _ ComplexShape.embeddingDownNat hn.symm :=
  (rfl)

/-- The first page of the spectral sequence of a filtered space vanishes in positive total
degree `p + q`, since chains are concentrated in nonpositive cohomological degrees. -/
lemma isZero_chainFiltrationSpectralSequence_page_two_X (pq : ℤ × ℤ) (h : 0 < pq.1 + pq.2) :
    IsZero (((chainFiltrationSpectralSequence F hX).page 2).X pq) :=
  IsZero.of_iso ((extend_exactAt _ ComplexShape.embeddingDownNat _ fun n hn ↦ by
      have : -(n : ℤ) = pq.1 + pq.2 := hn
      lia).isZero_homology)
    (CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
      (homologyFunctor A _ _).mapIso (chainFiltrationCokernelFiltrationFunctorMapIso F hX _))

/-- The identification of the abutment is the identification
`CochainComplex.filtrationAbutmentIso` of the abutment with the cohomology of the filtered
complex, followed by the identification of the cohomology of the reindexed complex `F Y` with its
homology. -/
lemma chainFiltrationAbutmentIso_eq (n : ℕ) :
    chainFiltrationAbutmentIso F hX n =
      CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
        extendHomologyIso _ ComplexShape.embeddingDownNat rfl :=
  (rfl)

/-- The epimorphism from the homology `Hₙ(F (X q))` of the chains of `X q` onto the `q`th piece of
the filtration of the abutment in degree `-n`. Through `TauCeti.chainFiltrationAbutmentIso` it is
the map `Hₙ(F (X q)) ⟶ Hₙ(F Y)` induced by the inclusion of `X q`
(`TauCeti.chainFiltrationToAbutmentFiltration_comp_chainFiltrationAbutmentIso_hom`),
so that piece is the image of this map. -/
def chainFiltrationToAbutmentFiltration (q : ℤ) (n : ℕ) :
    (F.obj (TopPair.ofSubset (X q)).snd).homology n ⟶
      (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_chainFiltration F hX))).abutmentFiltration q (-n) :=
  (extendHomologyIso _ ComplexShape.embeddingDownNat rfl).inv ≫
    homologyMap (chainFiltrationIso F X q).inv (-n) ≫
      CochainComplex.toFiltrationAbutmentFiltration _ (monotone_chainFiltration F hX) q (-n)

instance (q : ℤ) (n : ℕ) : Epi (chainFiltrationToAbutmentFiltration F hX q n) := by
  rw [chainFiltrationToAbutmentFiltration]
  infer_instance

/-- **The filtration of the abutment of a filtered space is the image filtration.** Under the
identification `TauCeti.chainFiltrationAbutmentIso` of the abutment in degree `-n` with `Hₙ(F Y)`,
the embedding of the `q`th piece of its filtration, precomposed with the epimorphism
`TauCeti.chainFiltrationToAbutmentFiltration`, is the map `Hₙ(F (X q)) ⟶ Hₙ(F Y)` induced by the
inclusion of `X q`. -/
@[reassoc (attr := simp)]
theorem chainFiltrationToAbutmentFiltration_comp_chainFiltrationAbutmentIso_hom
    (q : ℤ) (n : ℕ) :
    chainFiltrationToAbutmentFiltration F hX q n ≫
        (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
          (monotone_chainFiltration F hX))).abutmentFiltrationι q (-n) ≫
          (chainFiltrationAbutmentIso F hX n).hom =
      homologyMap (F.map (TopPair.ofSubset (X q)).map) n := by
  have h := extendHomologyIso_hom_naturality (F.map (TopPair.ofSubset (X q)).map)
    ComplexShape.embeddingDownNat (j := n) rfl
  rw [← Iso.inv_comp_eq, ← chainFiltrationι_def] at h
  have h₂ := CochainComplex.toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom
    (chainFiltration F X) (monotone_chainFiltration F hX) q (-n)
  rw [chainFiltrationToAbutmentFiltration, chainFiltrationAbutmentIso_eq, Iso.trans_hom]
  simp only [Category.assoc]
  -- `chainFiltrationAbutmentIso` indexes the abutment by `ComplexShape.embeddingDownNat.f n`,
  -- which is `-n` only up to unfolding, so `h₂` is rewritten up to that unfolding.
  erw [reassoc_of% h₂]
  rw [← homologyMap_comp_assoc, ← chainFiltrationIso_hom_comp_chainFiltrationι,
    Iso.inv_hom_id_assoc]
  -- The codomain of the map induced by the inclusion is `Y` only up to unfolding
  -- `TopPair.ofSubset`, which `exact` performs.
  exact h

section TopColumn

variable {q : ℤ} (hq : X (q + 1) = Set.univ)

include hq in
/-- **The projection onto the top column of the spectral sequence of a filtered space.** If
`X (q + 1)` is all of `Y`, then `Hₙ(F Y)` is the piece `F_{q+1}` of the filtration of the abutment
in degree `-n`, and this is its projection onto the graded piece `F_{q+1} / F_q`, the limit object
`E∞` at `q` in degree `-n`. It is `CochainComplex.filtrationToTopColumnEInfty` for the filtration
of chains, after identifying `Hₙ(F Y)` with the cohomology of the reindexed complex. -/
def chainFiltrationToTopColumnEInfty (n : ℕ) :
    (F.obj Y).homology n ⟶ (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_chainFiltration F hX))).EInfty q (-n) :=
  (extendHomologyIso _ ComplexShape.embeddingDownNat rfl).inv ≫
    CochainComplex.filtrationToTopColumnEInfty _ _ (chainFiltration_eq_top F hq) (-n)

open CochainComplex in
/-- **The defining property of the projection onto the top column.** On the piece `F_{q+1}` of the
filtration of the abutment, identified with `Hₙ(F Y)`, the projection is the quotient map onto the
cokernel of `F_q ⟶ F_{q+1}`, identified with `E∞`. -/
@[reassoc]
lemma abutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom_comp_chainFiltrationToTopColumnEInfty
    (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_chainFiltration F hX))).abutmentFiltrationι (q + 1) (-n) ≫
        (chainFiltrationAbutmentIso F hX n).hom ≫ chainFiltrationToTopColumnEInfty F hX hq n =
      cokernel.π ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
          (monotone_chainFiltration F hX))).abutmentFiltrationMap q (-n)) ≫
        ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
          (monotone_chainFiltration F hX))).EInftyIsoCokernel q (-n)).inv := by
  rw [chainFiltrationAbutmentIso_eq, chainFiltrationToTopColumnEInfty, Iso.trans_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact abutmentFiltrationι_comp_filtrationAbutmentIso_hom_comp_filtrationToTopColumnEInfty _ _ _ _

instance (n : ℕ) : Epi (chainFiltrationToTopColumnEInfty F hX hq n) := by
  rw [chainFiltrationToTopColumnEInfty]
  infer_instance

end TopColumn

/-- **Strong convergence of the spectral sequence of a finite filtration of a space.** If `F`
vanishes on empty spaces, `X a = ∅` and `X b` is all of `Y`, then on every page `r ≥ 2` with
`q - r + 2 ≤ a` and `b ≤ q + r - 1`, the object at `(p, q)` is the graded piece `F_{q+1} H / F_q H`
of the filtration of the abutment in degree `p + q`, which is `H_{-(p+q)}(F Y)` by
`TauCeti.chainFiltrationAbutmentIso`. -/
def chainFiltrationSpectralSequencePageXIsoGradedOfFinite
    (hF : ∀ Z : TopCat.{w}, IsEmpty Z → IsZero (F.obj Z)) {a b : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((chainFiltrationSpectralSequence F hX).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_chainFiltration F hX))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (chainFiltration_eq_bot F hF ha) (chainFiltration_eq_top F hb) r hr pq hra hrb

end ChainFunctor

section ImageFiltration

variable {k : Type u} [Ring k] (F : TopCat.{w} ⥤ ChainComplex (ModuleCat.{v} k) ℕ)
  [∀ P : TopPair.{w}, Mono (F.map P.map)] {X : ℤ → Set Y} (hX : Monotone X)

/-- **The filtration of the abutment of a filtered space is the image filtration.** Under the
identification `TauCeti.chainFiltrationAbutmentIso` of the abutment in degree `-n` with `Hₙ(F Y)`,
the `q`th piece of its filtration is the image of the map `Hₙ(F (X q)) ⟶ Hₙ(F Y)` induced by the
inclusion of `X q`. -/
theorem range_abutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom (q : ℤ) (n : ℕ) :
    LinearMap.range ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_chainFiltration F hX))).abutmentFiltrationι q (-n) ≫
        (chainFiltrationAbutmentIso F hX n).hom).hom =
      LinearMap.range (homologyMap (F.map (TopPair.ofSubset (X q)).map) n).hom := by
  have h := congrArg (fun f ↦ LinearMap.range (ModuleCat.Hom.hom f))
    (chainFiltrationToAbutmentFiltration_comp_chainFiltrationAbutmentIso_hom F hX q n)
  simp only [ModuleCat.hom_comp] at h
  rw [LinearMap.range_comp_of_range_eq_top _
    ((ModuleCat.epi_iff_range_eq_top _).1 inferInstance)] at h
  -- The codomain of the map induced by the inclusion is `Y` only up to unfolding
  -- `TopPair.ofSubset`, which `exact` performs.
  exact h

/-- The projection onto the top column vanishes on a class `α ∈ Hₙ(F Y)` exactly when `α` comes
from the homology of the chains of `X q`. -/
theorem chainFiltrationToTopColumnEInfty_eq_zero_iff {q : ℤ} (hq : X (q + 1) = Set.univ) {n : ℕ}
    (α : (F.obj Y).homology n) :
    (chainFiltrationToTopColumnEInfty F hX hq n).hom α = 0 ↔
      α ∈ LinearMap.range (homologyMap (F.map (TopPair.ofSubset (X q)).map) n).hom := by
  set e := extendHomologyIso (F.obj Y) ComplexShape.embeddingDownNat (j := n) (j' := -n) rfl
  set ι := (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
    (monotone_chainFiltration F hX))).abutmentFiltrationι q (-n) ≫
      (CochainComplex.filtrationAbutmentIso _ (monotone_chainFiltration F hX) (-n)).hom
  -- By the generic statement, the projection vanishes exactly on the image filtration of the
  -- reindexed complex, which `e` carries to that of `Hₙ(F Y)`.
  rw [chainFiltrationToTopColumnEInfty, ModuleCat.hom_comp, LinearMap.comp_apply,
    CochainComplex.filtrationToTopColumnEInfty_eq_zero_iff,
    ← CochainComplex.range_abutmentFiltrationι_comp_filtrationAbutmentIso_hom _
      (monotone_chainFiltration F hX), ← ModuleCat.mem_range_comp_iso_hom ι e]
  have hι : ι ≫ e.hom = (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_chainFiltration F hX))).abutmentFiltrationι q (-n) ≫
        (chainFiltrationAbutmentIso F hX n).hom := by
    -- `chainFiltrationAbutmentIso` indexes the abutment by `ComplexShape.embeddingDownNat.f n`,
    -- which is `-n` only up to unfolding, so the composites agree up to that unfolding.
    rw [chainFiltrationAbutmentIso_eq, Iso.trans_hom]
    exact Category.assoc _ _ _
  rw [hι]
  -- The codomain of the map induced by the inclusion is `Y` only up to unfolding
  -- `TopPair.ofSubset`, which `exact` performs.
  exact SetLike.ext_iff.1 (range_abutmentFiltrationι_comp_chainFiltrationAbutmentIso_hom F hX q n) α

end ImageFiltration

section ChainFunctorMap

variable {F G H : TopCat.{w} ⥤ ChainComplex A ℕ} (α : F ⟶ G) {Y' Y'' : TopCat.{w}}
  {X : ℤ → Set Y} {X' : ℤ → Set Y'} {X'' : ℤ → Set Y''} (hX : Monotone X) (hX' : Monotone X')
  (hX'' : Monotone X'') (g : Y ⟶ Y') (hg : ∀ q, Set.MapsTo g (X q) (X' q))

/-- A natural transformation `α : F ⟶ G` and a map `g` carrying `X q` into `X' q` carry the chains
`F (X q)` of `X q` into the chains `G (X' q)` of `X' q`. -/
@[reassoc]
lemma chainFiltrationι_comp_extendMap (q : ℤ) :
    chainFiltrationι F X q ≫ extendMap (F.map g ≫ α.app Y') ComplexShape.embeddingDownNat =
      extendMap (F.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q))) ≫ α.app _)
          ComplexShape.embeddingDownNat ≫
        chainFiltrationι G X' q := by
  -- The map of pairs `(Y, X q) ⟶ (Y', X' q)` induced by `g` commutes with the inclusions; push
  -- this square through `F` and use the naturality of `α`.
  have h : F.map (TopPair.ofSubset (X q)).map ≫ F.map g ≫ α.app Y' =
      (F.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q))) ≫ α.app _) ≫
        G.map (TopPair.ofSubset (X' q)).map := by
    simp only [Category.assoc, ← α.naturality, ← F.map_comp_assoc, TopPair.Hom.w,
      TopPair.ofSubsetMap_fst]
    exact (F.map_comp_assoc _ _ _).symm
  -- The ambient space of the pair `(Y, X q)` is `Y` only up to definitional unfolding, which
  -- blocks `simp` and `rw` with `extendMap_comp`; apply it on both sides of `h` explicitly.
  exact (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · _) h).trans (extendMap_comp _ _ _)

variable [∀ P : TopPair.{w}, Mono (F.map P.map)] [∀ P : TopPair.{w}, Mono (G.map P.map)]

include hg in
/-- A natural transformation `α : F ⟶ G` and a map `g` carrying each `X q` into `X' q` carry each
stage of the filtration of `F Y` into the same stage of the filtration of `G Y'`. -/
lemma factors_chainFiltration (q : ℤ) :
    (chainFiltration G X' q).Factors
      ((chainFiltration F X q).arrow ≫
        extendMap (F.map g ≫ α.app Y') ComplexShape.embeddingDownNat) :=
  (Subobject.mk_factors_iff _ _).2
    ⟨(chainFiltrationIso F X q).hom ≫
      extendMap (F.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q))) ≫ α.app _)
        ComplexShape.embeddingDownNat,
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (chainFiltrationι_comp_extendMap α g hg q).symm).trans
        (chainFiltrationIso_hom_comp_chainFiltrationι_assoc _ X q _)⟩

include g hg in
/-- **The morphism of filtrations of chains induced by a map of filtered spaces.** A natural
transformation `α : F ⟶ G` of functors from spaces to chain complexes and a continuous map
`g : Y ⟶ Y'` carrying each `X q` into `X' q` induce a morphism from the filtration of `F Y` by the
`F (X q)` to the filtration of `G Y'` by the `G (X' q)`. For `α` the identity this is the
functoriality of the filtration in maps of filtered spaces, and for `g` the identity it compares
two kinds of chains, such as simplicial and cubical chains, on one filtered space. -/
def chainFiltrationMap :
    CochainComplex.filtrationFunctor _ (monotone_chainFiltration F hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_chainFiltration G hX') :=
  CochainComplex.filtrationFunctorMap _ _ _ (factors_chainFiltration α g hg)

/-- `TauCeti.chainFiltrationMap` is the morphism of filtration functors given by the chain map
`F Y ⟶ G Y'` induced by `g` and `α`. -/
lemma chainFiltrationMap_def :
    chainFiltrationMap α hX hX' g hg =
      CochainComplex.filtrationFunctorMap _ _ _ (factors_chainFiltration α g hg) :=
  (rfl)

/-- The components of `TauCeti.chainFiltrationMap` are the restrictions of the chain map
`F Y ⟶ G Y'` induced by `g` and `α`. -/
@[reassoc (attr := simp)]
lemma chainFiltrationMap_app_comp (a : EInt) :
    (chainFiltrationMap α hX hX' g hg).app a ≫
        CochainComplex.filtrationFunctorArrow _ (monotone_chainFiltration G hX') a =
      CochainComplex.filtrationFunctorArrow _ (monotone_chainFiltration F hX) a ≫
        extendMap (F.map g ≫ α.app Y') ComplexShape.embeddingDownNat :=
  (CochainComplex.filtrationFunctorMap_app_comp _ _ a).trans (Category.assoc _ _ _).symm

/-- On the stage `F_q`, identified with the chains of `X q`, the morphism of filtrations induced
by `g` and `α` is the chain map induced by the restriction of `g` to `X q` and by `α`. -/
@[reassoc]
lemma chainFiltrationMap_app_comp_filtrationFunctorObjIsoOfEqMk_hom (q : ℤ) :
    (chainFiltrationMap α hX hX' g hg).app q ≫
        (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (monotone_chainFiltration G hX')
          (chainFiltrationι G X' q) (chainFiltration_def G X' q)).hom =
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (monotone_chainFiltration F hX)
          (chainFiltrationι F X q) (chainFiltration_def F X q)).hom ≫
        extendMap (F.map (TopPair.Hom.snd (TopPair.ofSubsetMap g (hg q))) ≫ α.app _)
          ComplexShape.embeddingDownNat := by
  refine (cancel_mono (chainFiltrationι G X' q)).1 ?_
  simp only [Category.assoc, CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp,
    ← chainFiltrationι_comp_extendMap, CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp_assoc]
  exact (chainFiltrationMap_app_comp α hX hX' g hg q).trans (Category.assoc _ _ _)

/-- If `α` is a quasi-isomorphism on every subset `X q`, for instance on every space, then on every
stage of the filtrations of a filtered space the morphism of filtrations induced by `α` is a
quasi-isomorphism. -/
instance quasiIso_chainFiltrationMap_app [∀ q, QuasiIso (α.app (TopPair.ofSubset (X q)).snd)]
    (q : ℤ) :
    QuasiIso ((chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx).app q) := by
  -- On the stages at `q`, identified with the chains of `X q`, the morphism is `α` at `X q`.
  have := chainFiltrationMap_app_comp_filtrationFunctorObjIsoOfEqMk_hom α hX hX (𝟙 Y)
    (fun _ _ hx ↦ hx) q
  have hs : TopPair.Hom.snd (TopPair.ofSubsetMap (𝟙 Y) fun _ hx ↦ hx :
      TopPair.ofSubset (X q) ⟶ TopPair.ofSubset (X q)) = 𝟙 _ := by
    ext x
    exact Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ x)
  rw [hs, CategoryTheory.Functor.map_id, Category.id_comp, ← Iso.eq_comp_inv] at this
  rw [this]
  infer_instance

/-- The identity of a filtered space induces the identity of its filtered chains. -/
@[simp]
lemma chainFiltrationMap_id (h : ∀ q, Set.MapsTo (𝟙 Y : Y ⟶ Y) (X q) (X q)) :
    chainFiltrationMap (𝟙 F) hX hX (𝟙 Y) h = 𝟙 _ := by
  rw [chainFiltrationMap, CochainComplex.filtrationFunctorMap_congr (f' := 𝟙 _) (by simp),
    CochainComplex.filtrationFunctorMap_id]

/-- Composites of natural transformations and of maps of filtered spaces induce the composite of
the morphisms of filtered chains. -/
@[reassoc]
lemma chainFiltrationMap_comp [∀ P : TopPair.{w}, Mono (H.map P.map)] (β : G ⟶ H) (g' : Y' ⟶ Y'')
    (hg' : ∀ q, Set.MapsTo g' (X' q) (X'' q)) (hgg' : ∀ q, Set.MapsTo (g ≫ g') (X q) (X'' q)) :
    chainFiltrationMap (α ≫ β) hX hX'' (g ≫ g') hgg' =
      chainFiltrationMap α hX hX' g hg ≫ chainFiltrationMap β hX' hX'' g' hg' := by
  rw [chainFiltrationMap, chainFiltrationMap, chainFiltrationMap,
    CochainComplex.filtrationFunctorMap_congr
      (f' := extendMap (F.map g ≫ α.app Y') _ ≫ extendMap (G.map g' ≫ β.app Y'') _)
      (by rw [← extendMap_comp]; simp),
    CochainComplex.filtrationFunctorMap_comp _ _ (factors_chainFiltration α g hg)
      (factors_chainFiltration β g' hg')]

/-- **The morphism of spectral objects of filtered spaces on the abutment.** Under the
identifications `TauCeti.chainFiltrationAbutmentIso` of the abutments in degree `-n` with the
homology `Hₙ(F Y)` and `Hₙ(G Y')`, the morphism of spectral objects induced by `α` and `g` is the
map `Hₙ(F Y) ⟶ Hₙ(G Y')` induced by `F.map g ≫ α.app Y'`; for singular chains and `α` the
identity, this is the map `Hₙ(g)` in singular homology. -/
@[reassoc]
theorem chainFiltrationAbutmentIso_hom_naturality (n : ℕ) :
    ((CochainComplex.spectralObjectMap (chainFiltrationMap α hX hX' g hg)).hom (-n)).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (chainFiltrationAbutmentIso G hX' n).hom =
      (chainFiltrationAbutmentIso F hX n).hom ≫
        HomologicalComplex.homologyMap (F.map g ≫ α.app Y') n := by
  rw [chainFiltrationAbutmentIso, chainFiltrationAbutmentIso, chainFiltrationMap]
  -- The homology objects of the extended complexes carry `HasHomology` instances that `rw` does
  -- not identify, so the square is assembled as a term.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
    (CochainComplex.spectralObjectMap_filtrationFunctorMap_hom_app_comp_filtrationAbutmentIso_hom
      _ _ _)).trans <| (Category.assoc _ _ _).trans <| (congrArg
      ((CochainComplex.filtrationAbutmentIso _ (monotone_chainFiltration F hX) _).hom ≫ ·)
      (extendHomologyIso_hom_naturality _ _ _)).trans (Category.assoc _ _ _).symm

end ChainFunctorMap

/-! ### Comparison along a natural transformation of chain functors -/

section Comparison

variable {F G : TopCat.{w} ⥤ ChainComplex A ℕ} (α : F ⟶ G) {X : ℤ → Set Y}

variable (X) in
/-- A natural transformation of chain functors carries the inclusion of `F (X n)` into `F Y` to
the inclusion of `G (X n)` into `G Y`. -/
private lemma chainFiltrationι_comp_extendMap_app (n : ℤ) :
    chainFiltrationι F X n ≫ extendMap (α.app Y) ComplexShape.embeddingDownNat =
      extendMap (α.app _) ComplexShape.embeddingDownNat ≫ chainFiltrationι G X n :=
  (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · _) (α.naturality _)).trans (extendMap_comp _ _ _)

variable [∀ P : TopPair.{w}, Mono (F.map P.map)] [∀ P : TopPair.{w}, Mono (G.map P.map)]
  (hX : Monotone X)

/-- On the `n`-th stage, the morphism of filtrations induced by `α` on a single filtered space is
`α` on `X n`, under the identifications of the stages with the chains of `X n`. -/
@[reassoc]
lemma chainFiltrationMap_app_comp_filtrationFunctorObjIso_hom (n : ℤ) :
    (chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx).app n ≫
        (CochainComplex.filtrationFunctorObjIso _ _ n).hom ≫
          Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ n).le ≫
            (chainFiltrationIso G X n).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ n).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ n).le ≫
          (chainFiltrationIso F X n).hom ≫
            extendMap (α.app _) ComplexShape.embeddingDownNat := by
  rw [← cancel_mono (chainFiltrationι G X n)]
  simp only [Category.assoc, ← chainFiltrationι_comp_extendMap_app,
    chainFiltrationIso_hom_comp_chainFiltrationι,
    chainFiltrationIso_hom_comp_chainFiltrationι_assoc, Subobject.ofLE_arrow,
    Subobject.ofLE_arrow_assoc]
  have h := chainFiltrationMap_app_comp α hX hX (𝟙 Y) (fun _ _ hx ↦ hx) n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h.trans (Category.assoc _ _ _)

/-- On the graded pieces of the filtrations, the morphism of filtrations induced by `α` on a single
filtered space is the map of cokernels induced by `α`. -/
@[reassoc]
lemma cokernel_map_chainFiltrationMap_comp {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.map _ _ _ _ ((chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx).naturality f).symm ≫
        (chainFiltrationCokernelFiltrationFunctorMapIso G hX f).hom =
      (chainFiltrationCokernelFiltrationFunctorMapIso F hX f).hom ≫
        extendMap (cokernel.map _ _ (α.app _) (α.app _) (α.naturality _).symm)
          ComplexShape.embeddingDownNat := by
  refine (cancel_epi (cokernel.π _)).1 ?_
  -- The ambient space of the pair `(X b, X a)` is the subspace `X b` of `Y` only up to
  -- definitional unfolding, so the composites are formed with terms rather than `rw`.
  exact (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (π_chainFiltrationCokernelFiltrationFunctorMapIso_hom G hX f)).trans <|
    (chainFiltrationMap_app_comp_filtrationFunctorObjIso_hom_assoc α hX b _).trans <|
      (congrArg (_ ≫ _ ≫ ·)
      ((congrArg (_ ≫ ·) ((extendMap_comp _ _ _).symm.trans <|
        (congrArg (extendMap · _) (cokernel.π_desc _ _ _).symm).trans
          (extendMap_comp _ _ _))).trans (Category.assoc _ _ _).symm)).trans
        (π_chainFiltrationCokernelFiltrationFunctorMapIso_hom_assoc F hX f _).symm

/-- **The comparison of the spectral sequences of a filtered space on the first page.** Under the
identifications of the objects of the first pages with the homology of the cokernels of the maps
of chains of pairs, the morphism of spectral sequences induced by `α` is the map in homology of
the map of cokernels induced by `α`. -/
@[reassoc]
lemma spectralSequenceMap_chainFiltrationMap_two_f_comp (pq : ℤ × ℤ) (a b : ℤ)
    (ha : a = pq.2) (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((spectralSequenceMap coreE₂Cohomological (CochainComplex.spectralObjectMap
          (chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx))).hom 2 le_rfl).f pq ≫
        (chainFiltrationSpectralSequenceFirstPageXIso G hX pq a b ha hb m hm n hn).hom =
      (chainFiltrationSpectralSequenceFirstPageXIso F hX pq a b ha hb m hm n hn).hom ≫
        homologyMap (cokernel.map _ _ (α.app _) (α.app _) (α.naturality _).symm) n := by
  have h := (homologyMap_comp _ _ m).symm.trans <| (congrArg (homologyMap · m)
    (cokernel_map_chainFiltrationMap_comp α hX
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one ha hb)))).trans (homologyMap_comp _ _ m)
  -- The first-page identifications are composites of isomorphisms whose types mention the pair
  -- `(X b, X a)` only up to definitional unfolding, so they are composed with terms.
  have e := CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality
    (chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx) pq a b ha hb m hm
  exact ((reassoc_of% e) _).trans <|
    (congrArg (_ ≫ ·) <| ((reassoc_of% h) _).trans <|
      congrArg (_ ≫ ·) (extendHomologyIso_hom_naturality _ _ _)).trans <|
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

/-- **The comparison of the abutments of a filtered space.** Under the identifications of the
abutments in degree `-n` with `Hₙ(F Y)` and `Hₙ(G Y)`, the morphism of spectral objects induced by
the morphism of filtrations induced by `α` is the map in homology of `α` on `Y`. -/
@[reassoc]
lemma spectralObjectMap_chainFiltrationMap_abutment_comp (n : ℕ) :
    ((CochainComplex.spectralObjectMap (chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx)).hom
        (-n)).app (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (chainFiltrationAbutmentIso G hX n).hom =
      (chainFiltrationAbutmentIso F hX n).hom ≫ homologyMap (α.app Y) n := by
  have h : ((CochainComplex.spectralObjectMap
      (chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx)).hom (-n)).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (chainFiltrationAbutmentIso G hX n).hom =
      (chainFiltrationAbutmentIso F hX n).hom ≫ homologyMap (F.map (𝟙 Y) ≫ α.app Y) n :=
    chainFiltrationAbutmentIso_hom_naturality α hX hX (𝟙 Y) (fun _ _ hx ↦ hx) n
  rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h

end Comparison

end TauCeti
