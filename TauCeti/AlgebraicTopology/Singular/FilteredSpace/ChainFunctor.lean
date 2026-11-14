/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.QuasiIso
public import TauCeti.Topology.Category.TopPair
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The spectral sequence of a filtered space for a chain functor

Let `F : TopCat ⥤ ChainComplex A ℕ` be a functor sending inclusions of subspaces to
monomorphisms, such as simplicial singular chains or normalized cubical chains, and let
`X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`. The chains
`F (X q)` form an increasing filtration of `F Y` (`TauCeti.subspaceChainFiltration`), and this file
studies the spectral sequence of that filtered complex (`TauCeti.subspaceChainSpectralSequence`).
It is the spectral sequence of a filtered complex from
`TauCeti.Algebra.Homology.SpectralSequence.Filtered`, which uses cochain complexes indexed by
`ℤ`, so chains in degree `n` are placed in degree `-n` along `ComplexShape.embeddingDownNat`.

* **Graded pieces.** The quotient `F_b / F_a` of two stages of the filtration is the cokernel of
  the map `F (X a) ⟶ F (X b)` (`TauCeti.subspaceChainFiltrationCokernelIso`).
* **First page.** The object at `(p, q)` on the first page (numbered `2` in the indexing of
  `CochainComplex.spectralSequence`) is the homology in degree `n` of that cokernel for the pair
  `(X (q + 1), X q)`, with `p + q = -n` (`TauCeti.subspaceChainSpectralSequenceFirstPageXIso`).
* **Convergence.** The abutment in degree `-n` is `Hₙ(F Y)` (`TauCeti.subspaceChainAbutmentIso`).
  When `X a = ∅`, `F` vanishes on empty spaces and `X b = Y`, the filtration is finite and the
  spectral sequence converges strongly
  (`TauCeti.subspaceChainSpectralSequencePageXIsoGradedOfFinite`).
* **Comparison.** A natural transformation `φ : F ⟶ G` carries the filtration of `F Y` into that
  of `G Y` (`TauCeti.subspaceChainFiltrationMap`). If every component of `φ` is a
  quasi-isomorphism, it induces an isomorphism of spectral sequences on every page
  (`TauCeti.subspaceChainSpectralSequenceIso`), with no boundedness or exhaustiveness assumption
  on the filtration. On the first page and on the abutment it is the map in homology induced by
  `φ` (`TauCeti.spectralSequenceMap_subspaceChainFiltrationMap_two_f_comp` and
  `TauCeti.spectralObjectMap_subspaceChainFiltrationMap_abutment_comp`).

The simplicial singular instance is `TauCeti.filteredSpaceSpectralSequence`, and the normalized
cubical instance is compared with it in
`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Cubical`.

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

variable {A : Type u} [Category.{v} A] [Abelian A] (F : TopCat.{w} ⥤ ChainComplex A ℕ)
  [∀ P : TopPair.{w}, Mono (F.map P.map)] {Y : TopCat.{w}}

variable (X : ℤ → Set Y)

/-- The inclusion of the chains `F (X q)` into `F Y`, with both chain complexes reindexed as
cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def subspaceChainFiltrationι (q : ℤ) :
    (F.obj (TopPair.ofSubset (X q)).snd).extend ComplexShape.embeddingDownNat ⟶
      (F.obj Y).extend ComplexShape.embeddingDownNat :=
  extendMap (F.map (TopPair.ofSubset (X q)).map) _

omit [∀ P : TopPair.{w}, Mono (F.map P.map)] in
/-- The inclusion of the chains `F (X q)` into `F Y` is induced by the inclusion of the subspace
`X q`. -/
lemma subspaceChainFiltrationι_def (q : ℤ) :
    subspaceChainFiltrationι F X q =
      extendMap (F.map (TopPair.ofSubset (X q)).map) ComplexShape.embeddingDownNat := by
  rw [subspaceChainFiltrationι]

/-- The chains `F (X q)` form a subcomplex of `F Y`, also after reindexing. -/
instance (q : ℤ) : Mono (subspaceChainFiltrationι F X q) :=
  HomologicalComplex.mono_extendMap _ _

/-- The filtration of the chains `F Y` by the chains `F (X q)` of the subsets `X q`, with the
chain complexes reindexed as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def subspaceChainFiltration (q : ℤ) :
    Subobject ((F.obj Y).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (subspaceChainFiltrationι F X q)

/-- The `q`-th stage of the filtration is the subobject given by the inclusion of `F (X q)`. -/
lemma subspaceChainFiltration_def (q : ℤ) :
    subspaceChainFiltration F X q = Subobject.mk (subspaceChainFiltrationι F X q) := by
  rw [subspaceChainFiltration]

/-- The `q`-th stage of the filtration is the reindexed chain complex `F (X q)`. -/
def subspaceChainFiltrationIso (q : ℤ) :
    (subspaceChainFiltration F X q : CochainComplex A ℤ) ≅
      (F.obj (TopPair.ofSubset (X q)).snd).extend ComplexShape.embeddingDownNat :=
  Subobject.underlyingIso (subspaceChainFiltrationι F X q)

/-- The identification of the `q`-th stage of the filtration with `F (X q)` is compatible with
the inclusions into `F Y`. -/
@[reassoc (attr := simp)]
lemma subspaceChainFiltrationIso_hom_comp_subspaceChainFiltrationι (q : ℤ) :
    (subspaceChainFiltrationIso F X q).hom ≫ subspaceChainFiltrationι F X q =
      (subspaceChainFiltration F X q).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {X}

omit [∀ P : TopPair.{w}, Mono (F.map P.map)] in
/-- For `X a ⊆ X b`, the inclusion of `F (X a)` into `F Y` factors through the inclusion of the
pair `(X b, X a)`. -/
@[simp, reassoc]
lemma extendMap_comp_subspaceChainFiltrationι {a b : ℤ} (hab : X a ⊆ X b) :
    extendMap (F.map (TopPair.ofInclusion hab).map) ComplexShape.embeddingDownNat ≫
        subspaceChainFiltrationι F X b =
      subspaceChainFiltrationι F X a := by
  -- The ambient space of the pair `(X b, X a)` is the subspace `X b` of `Y` only up to
  -- definitional unfolding, so the composites are formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) (F.map_comp _ _).symm

/-- The filtration is monotone in the subsets. -/
lemma subspaceChainFiltration_mono {a b : ℤ} (hab : X a ⊆ X b) :
    subspaceChainFiltration F X a ≤ subspaceChainFiltration F X b :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_subspaceChainFiltrationι F hab)

/-- Under the identifications of the stages of the filtration with the chains of the subsets, the
inclusion `F_a ⟶ F_b` is induced by the inclusion `X a ⊆ X b`. -/
@[reassoc]
lemma ofLE_comp_subspaceChainFiltrationIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    Subobject.ofLE _ _ (subspaceChainFiltration_mono F hab) ≫
        (subspaceChainFiltrationIso F X b).hom =
      (subspaceChainFiltrationIso F X a).hom ≫
        extendMap (F.map (TopPair.ofInclusion hab).map) ComplexShape.embeddingDownNat :=
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := subspaceChainFiltrationι F X a) (f₂ := subspaceChainFiltrationι F X b) _
    (extendMap_comp_subspaceChainFiltrationι F hab)).trans (Category.assoc _ _ _).symm

/-- An increasing family of subsets gives an increasing filtration of chains. -/
lemma monotone_subspaceChainFiltration (hX : Monotone X) :
    Monotone (subspaceChainFiltration F X) :=
  fun _ _ h ↦ subspaceChainFiltration_mono F (hX h)

/-- The stage of the filtration at an empty subset is zero, when `F` vanishes on empty spaces. -/
lemma subspaceChainFiltration_eq_bot (hF : ∀ Z : TopCat.{w}, IsEmpty Z → IsZero (F.obj Z))
    {a : ℤ} (ha : X a = ∅) :
    subspaceChainFiltration F X a = ⊥ := by
  have : IsEmpty (TopPair.ofSubset (X a)).snd := by
    rw [ha]
    exact Set.isEmpty_coe_sort.2 rfl
  exact Subobject.mk_eq_bot_iff_zero.2
    (((ComplexShape.embeddingDownNat.extendFunctor A).map_isZero (hF _ this)).eq_of_src _ _)

/-- The stage of the filtration at the whole space is everything. -/
@[simp]
lemma subspaceChainFiltration_eq_top {b : ℤ} (hb : X b = Set.univ) :
    subspaceChainFiltration F X b = ⊤ := by
  have : IsIso (TopPair.ofSubset (X b)).map := by
    refine TopCat.isIso_of_bijective_of_isOpenMap _ ⟨Subtype.val_injective, fun y ↦ ?_⟩
      (hb ▸ isOpen_univ : IsOpen (X b)).isOpenEmbedding_subtypeVal.isOpenMap
    exact ⟨⟨y, hb ▸ Set.mem_univ y⟩, rfl⟩
  have : IsIso (subspaceChainFiltrationι F X b) := by
    rw [subspaceChainFiltrationι]
    exact Functor.map_isIso (ComplexShape.embeddingDownNat.extendFunctor A) _
  exact Subobject.mk_eq_top_of_isIso _

/-- The quotient `F_b / F_a` of two stages of the filtration is the cokernel of the map
`F (X a) ⟶ F (X b)`, reindexed along `n ↦ -n`. The isomorphism is induced by the quotient map
from `F (X b)` (`TauCeti.π_subspaceChainFiltrationCokernelIso_hom`). -/
def subspaceChainFiltrationCokernelIso {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel (Subobject.ofLE _ _ (subspaceChainFiltration_mono F hab)) ≅
      (cokernel (F.map (TopPair.ofInclusion hab).map)).extend ComplexShape.embeddingDownNat :=
  have hS : (ShortComplex.mk _ _
      (cokernel.condition (F.map (TopPair.ofInclusion hab).map))).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      inferInstance (inferInstanceAs (Epi (cokernel.π _)))
  cokernel.mapIso _
      (extendMap (F.map (TopPair.ofInclusion hab).map) ComplexShape.embeddingDownNat)
      (subspaceChainFiltrationIso F X a) (subspaceChainFiltrationIso F X b)
      (ofLE_comp_subspaceChainFiltrationIso_hom F hab) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (hS.extend ComplexShape.embeddingDownNat).gIsCokernel

/-- The identification of `F_b / F_a` with the cokernel of `F (X a) ⟶ F (X b)` is induced by the
quotient map from `F (X b)`. -/
@[reassoc (attr := simp)]
lemma π_subspaceChainFiltrationCokernelIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel.π _ ≫ (subspaceChainFiltrationCokernelIso F hab).hom =
      (subspaceChainFiltrationIso F X b).hom ≫
        extendMap (cokernel.π (F.map (TopPair.ofInclusion hab).map))
          ComplexShape.embeddingDownNat :=
  -- The first factor is `cokernel.map`, which is `cokernel.desc` of the composite with the
  -- quotient map, and the second sends that quotient map to the cokernel cofork's map.
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

variable (hX : Monotone X)

/-- The quotient of two stages of the filtration, as the cokernel of a transition map of the
functor `CochainComplex.filtrationFunctor` of the filtration, is the reindexed cokernel of the map
of chains induced by the corresponding pair. -/
def subspaceChainCokernelFiltrationFunctorMapIso {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel ((CochainComplex.filtrationFunctor _ (monotone_subspaceChainFiltration F hX)).map f) ≅
      (cokernel (F.map (TopPair.ofInclusion
        (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).map)).extend ComplexShape.embeddingDownNat :=
  cokernel.mapIso _ _
      (CochainComplex.filtrationFunctorObjIso _ _ a ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ a))
      (CochainComplex.filtrationFunctorObjIso _ _ b ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ b))
      (by simp only [Iso.trans_hom, Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE,
        reassoc_of% CochainComplex.filtrationFunctor_map_comp_objIso_hom, Category.assoc]) ≪≫
    subspaceChainFiltrationCokernelIso F _

/-- The identification of the cokernel of a transition map of the filtration functor with the
cokernel of the map of chains of the pair is induced by the quotient map from the chains of the
larger subset. -/
@[reassoc]
lemma π_subspaceChainCokernelFiltrationFunctorMapIso_hom {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.π _ ≫ (subspaceChainCokernelFiltrationFunctorMapIso F hX f).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (subspaceChainFiltrationIso F X b).hom ≫
            extendMap (cokernel.π (F.map (TopPair.ofInclusion
              (hX (WithBotTop.coe_le_coe.mp (leOfHom f)))).map))
              ComplexShape.embeddingDownNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ _ ≫ ·) (π_subspaceChainFiltrationCokernelIso_hom F _)

/-- **The spectral sequence of a filtered space for a chain functor `F`.** For an increasing
family `X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the filtration
of the chains `F Y` by the chains `F (X q)`, in the cohomological indexing of
`CochainComplex.spectralSequence`: chains in degree `n` sit in degree `-n`. -/
abbrev subspaceChainSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _ (monotone_subspaceChainFiltration F hX))

/-- **The first page of the spectral sequence of a filtered space.** The object at `(p, q)` on the
first page (numbered `2`, as in `CochainComplex.spectralSequence`) is the homology in degree `n` of
the cokernel of `F (X q) ⟶ F (X (q + 1))`, where `p + q = -n`. The indices `q`, `q + 1` and
`p + q` are given as `a`, `b` and `m` together with equations, for flexibility. -/
def subspaceChainSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((subspaceChainSpectralSequence F hX).page 2).X pq ≅
      (cokernel (F.map (TopPair.ofInclusion (hX (by lia : a ≤ b))).map)).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq a b ha hb m hm ≪≫
    (homologyFunctor A _ _).mapIso (subspaceChainCokernelFiltrationFunctorMapIso F hX _) ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat hn.symm

/-- The identification of the first page is the identification
`CochainComplex.spectralSequenceFirstPageXIsoCokernel` of the first page with the homology of a
graded piece, followed by the identification of that graded piece with the cokernel of the map of
chains of the pair. -/
lemma subspaceChainSpectralSequenceFirstPageXIso_eq (pq : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    subspaceChainSpectralSequenceFirstPageXIso F hX pq a b ha hb m hm n hn =
      CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq a b ha hb m hm ≪≫
        (homologyFunctor A _ _).mapIso (subspaceChainCokernelFiltrationFunctorMapIso F hX _) ≪≫
        extendHomologyIso _ ComplexShape.embeddingDownNat hn.symm :=
  (rfl)

/-- The first page of the spectral sequence of a filtered space vanishes in positive total
degree `p + q`, since chains are concentrated in nonpositive cohomological degrees. -/
lemma isZero_subspaceChainSpectralSequence_page_two_X (pq : ℤ × ℤ) (h : 0 < pq.1 + pq.2) :
    IsZero (((subspaceChainSpectralSequence F hX).page 2).X pq) :=
  IsZero.of_iso ((extend_exactAt _ ComplexShape.embeddingDownNat _ fun n hn ↦ by
      have : -(n : ℤ) = pq.1 + pq.2 := hn
      lia).isZero_homology)
    (CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
      (homologyFunctor A _ _).mapIso (subspaceChainCokernelFiltrationFunctorMapIso F hX _))

/-- **The abutment of the spectral sequence of a filtered space** in degree `-n` is the homology
`Hₙ(F Y)`. -/
def subspaceChainAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_subspaceChainFiltration F hX))).abutment
        (-n) ≅
      (F.obj Y).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

/-- **Strong convergence of the spectral sequence of a finite filtration of a space.** If `F`
vanishes on empty spaces, `X a = ∅` and `X b` is all of `Y`, then on every page `r ≥ 2` with
`q - r + 2 ≤ a` and `b ≤ q + r - 1`, the object at `(p, q)` is the graded piece `F_{q+1} H / F_q H`
of the filtration of the abutment in degree `p + q`, which is `H_{-(p+q)}(F Y)` by
`TauCeti.subspaceChainAbutmentIso`. -/
def subspaceChainSpectralSequencePageXIsoGradedOfFinite
    (hF : ∀ Z : TopCat.{w}, IsEmpty Z → IsZero (F.obj Z)) {a b : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((subspaceChainSpectralSequence F hX).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_subspaceChainFiltration F hX))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (subspaceChainFiltration_eq_bot F hF ha) (subspaceChainFiltration_eq_top F hb) r hr pq hra hrb

/-! ### Comparison along a natural transformation of chain functors -/

section Comparison

variable {F} {G : TopCat.{w} ⥤ ChainComplex A ℕ} [∀ P : TopPair.{w}, Mono (G.map P.map)]
  (φ : F ⟶ G)

omit [∀ P : TopPair.{w}, Mono (F.map P.map)] [∀ P : TopPair.{w}, Mono (G.map P.map)] in
variable (X) in
/-- A natural transformation of chain functors carries the inclusion of `F (X n)` into `F Y` to
the inclusion of `G (X n)` into `G Y`. -/
private lemma subspaceChainFiltrationι_comp_extendMap_app (n : ℤ) :
    subspaceChainFiltrationι F X n ≫ extendMap (φ.app Y) ComplexShape.embeddingDownNat =
      extendMap (φ.app _) ComplexShape.embeddingDownNat ≫ subspaceChainFiltrationι G X n :=
  (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · _) (φ.naturality _)).trans (extendMap_comp _ _ _)

variable (X) in
/-- A natural transformation of chain functors carries `F (X n)` into `G (X n)`. -/
private lemma factors_subspaceChainFiltration (n : ℤ) :
    (subspaceChainFiltration G X n).Factors
      ((subspaceChainFiltration F X n).arrow ≫
        extendMap (φ.app Y) ComplexShape.embeddingDownNat) := by
  have e : (subspaceChainFiltration F X n).arrow ≫
      extendMap (φ.app Y) ComplexShape.embeddingDownNat =
      ((subspaceChainFiltrationIso F X n).hom ≫ extendMap (φ.app _) _ ≫
        (subspaceChainFiltrationIso G X n).inv) ≫ (subspaceChainFiltration G X n).arrow := by
    rw [Category.assoc, Category.assoc,
      ← subspaceChainFiltrationIso_hom_comp_subspaceChainFiltrationι G, Iso.inv_hom_id_assoc,
      ← subspaceChainFiltrationι_comp_extendMap_app, ← Category.assoc,
      subspaceChainFiltrationIso_hom_comp_subspaceChainFiltrationι]
  rw [e]
  exact Subobject.factors_comp_arrow _

/-- **The comparison of the filtrations of a filtered space along a natural transformation**
`φ : F ⟶ G` of chain functors: the morphism of filtration functors induced by `φ` on `Y`, which
carries `F (X q)` into `G (X q)`. -/
def subspaceChainFiltrationMap :
    CochainComplex.filtrationFunctor _ (monotone_subspaceChainFiltration F hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_subspaceChainFiltration G hX) :=
  CochainComplex.filtrationFunctorMap _ _ (extendMap (φ.app Y) ComplexShape.embeddingDownNat)
    (factors_subspaceChainFiltration X φ)

/-- The comparison of the filtrations is the restriction of `φ` on `Y` to the stages of the
filtrations. -/
@[reassoc]
lemma subspaceChainFiltrationMap_app_comp (a : EInt) :
    (subspaceChainFiltrationMap hX φ).app a ≫
        CochainComplex.filtrationFunctorArrow _ (monotone_subspaceChainFiltration G hX) a =
      CochainComplex.filtrationFunctorArrow _ (monotone_subspaceChainFiltration F hX) a ≫
        extendMap (φ.app Y) ComplexShape.embeddingDownNat :=
  (CochainComplex.filtrationFunctorMap_app_comp
    (hF := monotone_subspaceChainFiltration F hX)
    (hG := monotone_subspaceChainFiltration G hX) _
    (factors_subspaceChainFiltration X φ) a).trans (Category.assoc _ _ _).symm

/-- On the `n`-th stage, the comparison of the filtrations is `φ` on `X n`, under the
identifications of the stages with the chains of `X n`. -/
private lemma subspaceChainFiltrationMap_app_comp_filtrationFunctorObjIsoOfEqMk_hom (n : ℤ) :
    (subspaceChainFiltrationMap hX φ).app n ≫
        (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (monotone_subspaceChainFiltration G hX)
          (subspaceChainFiltrationι G X) (subspaceChainFiltration_def G X) n).hom =
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (monotone_subspaceChainFiltration F hX)
          (subspaceChainFiltrationι F X) (subspaceChainFiltration_def F X) n).hom ≫
        extendMap (φ.app _) ComplexShape.embeddingDownNat := by
  rw [← cancel_mono (subspaceChainFiltrationι G X n), Category.assoc, Category.assoc,
    ← subspaceChainFiltrationι_comp_extendMap_app]
  simp only [CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp,
    CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp_assoc]
  exact (subspaceChainFiltrationMap_app_comp hX φ n).trans (Category.assoc _ _ _)

variable [∀ Z : TopCat.{w}, QuasiIso (φ.app Z)]

/-- If every component of `φ` is a quasi-isomorphism, the comparison of the filtrations is a
quasi-isomorphism on every stage, including the zero stage `⊥` and the whole complex `⊤`. -/
instance quasiIso_subspaceChainFiltrationMap_app (a : EInt) :
    QuasiIso ((subspaceChainFiltrationMap hX φ).app a) := by
  refine CochainComplex.quasiIso_filtrationFunctorMap_app _ _ _ _ (fun n ↦ ?_) a
  have h : QuasiIso ((subspaceChainFiltrationMap hX φ).app n ≫
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (monotone_subspaceChainFiltration G hX)
        (subspaceChainFiltrationι G X) (subspaceChainFiltration_def G X) n).hom) := by
    rw [subspaceChainFiltrationMap_app_comp_filtrationFunctorObjIsoOfEqMk_hom]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).1 h

/-- **Natural quasi-isomorphisms of chain functors induce isomorphisms of the spectral objects of
a filtered space.** -/
instance isIso_spectralObjectMap_subspaceChainFiltrationMap :
    IsIso (CochainComplex.spectralObjectMap (subspaceChainFiltrationMap hX φ)) :=
  CochainComplex.isIso_spectralObjectMap_of_quasiIso _

/-- **Natural quasi-isomorphisms of chain functors induce isomorphisms of the spectral sequences
of a filtered space.** If every component of `φ : F ⟶ G` is a quasi-isomorphism, the comparison
of the filtrations induces an isomorphism, on every page, between the spectral sequences of the
filtrations of `F Y` and of `G Y` by the chains of the `X q`. -/
def subspaceChainSpectralSequenceIso :
    subspaceChainSpectralSequence F hX ≅ subspaceChainSpectralSequence G hX :=
  asIso (spectralSequenceMap coreE₂Cohomological
    (CochainComplex.spectralObjectMap (subspaceChainFiltrationMap hX φ)))

/-- The isomorphism between the spectral sequences of a filtered space is the morphism of
spectral sequences induced by the comparison of the filtrations. -/
@[simp]
lemma subspaceChainSpectralSequenceIso_hom :
    (subspaceChainSpectralSequenceIso hX φ).hom =
      spectralSequenceMap coreE₂Cohomological
        (CochainComplex.spectralObjectMap (subspaceChainFiltrationMap hX φ)) :=
  (rfl)

omit [∀ Z : TopCat.{w}, QuasiIso (φ.app Z)] in
/-- On the graded pieces of the filtrations, the comparison of the filtrations is the map of
cokernels induced by `φ`. -/
private lemma cokernel_map_subspaceChainFiltrationMap_comp {a b : ℤ} (f : (a : EInt) ⟶ b) :
    cokernel.map _ _ _ _ ((subspaceChainFiltrationMap hX φ).naturality f) ≫
        (subspaceChainCokernelFiltrationFunctorMapIso G hX f).hom =
      (subspaceChainCokernelFiltrationFunctorMapIso F hX f).hom ≫
        extendMap (cokernel.map _ _ (φ.app _) (φ.app _) (φ.naturality _))
          ComplexShape.embeddingDownNat := by
  have hι : (subspaceChainFiltrationMap hX φ).app b ≫
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (subspaceChainFiltrationIso G X b).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ b).hom ≫
        Subobject.ofLE _ _ (CochainComplex.filtrationEInt_coe _ b).le ≫
          (subspaceChainFiltrationIso F X b).hom ≫
            extendMap (φ.app _) ComplexShape.embeddingDownNat := by
    rw [← cancel_mono (subspaceChainFiltrationι G X b)]
    simp only [Category.assoc, ← subspaceChainFiltrationι_comp_extendMap_app,
      subspaceChainFiltrationIso_hom_comp_subspaceChainFiltrationι,
      subspaceChainFiltrationIso_hom_comp_subspaceChainFiltrationι_assoc, Subobject.ofLE_arrow,
      Subobject.ofLE_arrow_assoc]
    exact (subspaceChainFiltrationMap_app_comp hX φ b).trans (Category.assoc _ _ _)
  refine (cancel_epi (cokernel.π _)).1 ?_
  -- The ambient space of the pair `(X b, X a)` is the subspace `X b` of `Y` only up to
  -- definitional unfolding, so the composites are formed with terms rather than `rw`.
  exact (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (π_subspaceChainCokernelFiltrationFunctorMapIso_hom G hX f)).trans <|
    ((reassoc_of% hι) _).trans <| (congrArg (_ ≫ _ ≫ ·)
      ((congrArg (_ ≫ ·) ((extendMap_comp _ _ _).symm.trans <|
        (congrArg (extendMap · _) (cokernel.π_desc _ _ _).symm).trans
          (extendMap_comp _ _ _))).trans (Category.assoc _ _ _).symm)).trans
        (π_subspaceChainCokernelFiltrationFunctorMapIso_hom_assoc F hX f _).symm

omit [∀ Z : TopCat.{w}, QuasiIso (φ.app Z)] in
/-- **The comparison of the spectral sequences of a filtered space on the first page.** Under the
identifications of the objects of the first pages with the homology of the cokernels of the maps
of chains of pairs, the morphism of spectral sequences induced by `φ` is the map in homology of
the map of cokernels induced by `φ`. -/
@[reassoc]
lemma spectralSequenceMap_subspaceChainFiltrationMap_two_f_comp (pq : ℤ × ℤ) (a b : ℤ)
    (ha : a = pq.2) (hb : b = pq.2 + 1) (m : ℤ) (hm : m = pq.1 + pq.2) (n : ℕ) (hn : m = -n) :
    ((spectralSequenceMap coreE₂Cohomological
          (CochainComplex.spectralObjectMap (subspaceChainFiltrationMap hX φ))).hom 2 le_rfl).f
          pq ≫
        (subspaceChainSpectralSequenceFirstPageXIso G hX pq a b ha hb m hm n hn).hom =
      (subspaceChainSpectralSequenceFirstPageXIso F hX pq a b ha hb m hm n hn).hom ≫
        homologyMap (cokernel.map _ _ (φ.app _) (φ.app _) (φ.naturality _)) n := by
  have h := (homologyMap_comp _ _ m).symm.trans <| (congrArg (homologyMap · m)
    (cokernel_map_subspaceChainFiltrationMap_comp hX φ
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one ha hb)))).trans (homologyMap_comp _ _ m)
  -- The first-page identifications are composites of isomorphisms whose types mention the pair
  -- `(X b, X a)` only up to definitional unfolding, so they are composed with terms.
  have e := CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality
    (subspaceChainFiltrationMap hX φ) pq a b ha hb m hm
  exact ((reassoc_of% e) _).trans <|
    (congrArg (_ ≫ ·) <| ((reassoc_of% h) _).trans <|
      congrArg (_ ≫ ·) (extendHomologyIso_hom_naturality _ _ _)).trans <|
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

omit [∀ Z : TopCat.{w}, QuasiIso (φ.app Z)] in
/-- **The comparison of the abutments of a filtered space.** Under the identifications of the
abutments in degree `-n` with `Hₙ(F Y)` and `Hₙ(G Y)`, the morphism of spectral objects induced by
the comparison of the filtrations is the map in homology of `φ` on `Y`. -/
@[reassoc]
lemma spectralObjectMap_subspaceChainFiltrationMap_abutment_comp (n : ℕ) :
    ((CochainComplex.spectralObjectMap (subspaceChainFiltrationMap hX φ)).hom (-n)).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (subspaceChainAbutmentIso G hX n).hom =
      (subspaceChainAbutmentIso F hX n).hom ≫ homologyMap (φ.app Y) n :=
  ((CochainComplex.spectralObjectMap_filtrationFunctorMap_abutment_comp_assoc _ _ _ _ _ _).trans
    (congrArg (_ ≫ ·) (extendHomologyIso_hom_naturality _ _ _))).trans (Category.assoc _ _ _).symm

end Comparison

end TauCeti
