/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.Embedding.ExtendSubobject
public import TauCeti.CategoryTheory.Subobject.Cokernel
public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative

/-!
# The cohomological spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a map to it. The singular cochains of `Y`
vanishing on `X (p - 1)` form a decreasing filtration `F^p` of the singular cochains of `Y`
(`TauCeti.singularCochainFiltration`), and this file studies the spectral sequence of that filtered
complex (`TauCeti.filteredSpaceCohomologySpectralSequence`). It is the spectral sequence of a
decreasing filtration from `TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing`, in the
classical cohomological indexing, for cochain complexes indexed by `ℤ`; singular cochains, indexed
by `ℕ`, are reindexed along `ComplexShape.embeddingUpNat`. Coefficients are those of
`TopCat.singularCochainComplex`: morphisms from singular chains with coefficients in an object `R`
of an abelian category to an object `M`, forming `k`-modules.

* **Cochains vanishing on a subspace.** The cochains of `Y` vanishing on `S` are the relative
  cochains of the pair `(Y, S)` (`TauCeti.singularCochainSubobject`). For `S ⊆ T` the quotient of
  the cochains vanishing on `S` by those vanishing on `T` is the relative cochain complex of the
  pair `(T, S)` (`TauCeti.singularCochainSubobjectCokernelIso`), by the short exact cochain
  sequence of the triple `(Y, T, S)`. A cochain vanishes on `S` exactly when it vanishes on every
  singular simplex with image in `S`
  (`TauCeti.mem_range_singularCochainSubobject_arrow_f_iff`).
* **First page.** `E₁^{p,q}` is the relative singular cohomology `H^{p+q}(X p, X (p - 1))`
  (`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`); it vanishes when `p + q < 0`.
* **Abutment.** The abutment in degree `n` is `Hⁿ(Y)`
  (`TauCeti.filteredSpaceCohomologyAbutmentIso`).
* **Convergence.** When `X (b - 1) = ∅` and `X (a - 1) = Y`, the filtration is finite and the
  spectral sequence converges strongly
  (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFinite`). When instead every
  compact subset of `Y` lies in some `X q`, the filtration is complete and separated in each degree
  (`TauCeti.isCompleteFiltration_singularCochainFiltration`), although no stage need vanish; if
  moreover `X (-1) = ∅` and `Hⁿ(X j, X (j - 1)) = 0` for `n < j`, as for the skeletal filtration
  of a CW complex, the spectral sequence converges strongly to the graded pieces of a finite
  filtration of `Hⁿ(Y)`
  (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFirstQuadrant`), by Weibel's
  Complete Convergence Theorem.

Filtering the total space of a Serre fibration by the preimages of the skeleta of a CW base gives
the cohomological Serre spectral sequence. The homological counterpart of this file is
`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex, and Chapter 5, its application to the
  filtration of a total space by the preimages of the skeleta of the base.
* C. A. Weibel, *An introduction to homological algebra*, Cambridge University Press, 1994,
  Theorem 5.5.10, the Complete Convergence Theorem.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {Y : TopCat.{w}}

/-! ### Cochains vanishing on a subspace -/

/-- The inclusion of the singular cochains of `Y` vanishing on `S`, the relative cochains of the
pair `(Y, S)`, into all singular cochains of `Y`, with both cochain complexes reindexed along
`ℕ ⊆ ℤ`. -/
def singularCochainSubobjectι (S : Set Y) :
    ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat ⟶
      (Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  extendMap ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f _

/-- The inclusion of the cochains vanishing on `S` is the reindexed map from relative to absolute
cochains, induced by the quotient map from the chains of `Y` to the relative chains of `(Y, S)`. -/
lemma singularCochainSubobjectι_def (S : Set Y) :
    singularCochainSubobjectι R k M S =
      extendMap ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f
        ComplexShape.embeddingUpNat := (rfl)

/-- The relative cochains of `(Y, S)` form a subcomplex of the cochains of `Y`, also after
reindexing. -/
instance (S : Set Y) : Mono (singularCochainSubobjectι R k M S) := by
  have := ((TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex R k M).mono_f
  exact HomologicalComplex.mono_extendMap _ _

/-- The subcomplex of the singular cochains of `Y`, reindexed along `ℕ ⊆ ℤ`, consisting of the
cochains vanishing on `S`. -/
def singularCochainSubobject (S : Set Y) :
    Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat) :=
  Subobject.mk (singularCochainSubobjectι R k M S)

/-- The subcomplex of cochains vanishing on `S` is the reindexed relative cochain complex of the
pair `(Y, S)`. -/
def singularCochainSubobjectIso (S : Set Y) :
    (singularCochainSubobject R k M S : CochainComplex (ModuleCat.{v} k) ℤ) ≅
      ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  Subobject.underlyingIso (singularCochainSubobjectι R k M S)

@[reassoc (attr := simp)]
lemma singularCochainSubobjectIso_hom_comp_singularCochainSubobjectι (S : Set Y) :
    (singularCochainSubobjectIso R k M S).hom ≫ singularCochainSubobjectι R k M S =
      (singularCochainSubobject R k M S).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {R k M}

/-- For `S ⊆ T`, the inclusion of the cochains vanishing on `T` into all cochains factors through
the cochains vanishing on `S`. -/
@[simp, reassoc]
lemma extendMap_comp_singularCochainSubobjectι {S T : Set Y} (h : S ⊆ T) :
    extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.totalToOuter.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat ≫
      singularCochainSubobjectι R k M S = singularCochainSubobjectι R k M T :=
  (extendMap_comp _ _ _).symm.trans <|
    congrArg (extendMap · _) ((TopTriple.ofSubset h).singularCochainComplexMap_totalToOuter_comp_f
      R k M)

variable (R k M)

/-- Cochains vanishing on a larger subspace vanish on a smaller one. -/
lemma singularCochainSubobject_anti {S T : Set Y} (h : S ⊆ T) :
    singularCochainSubobject R k M T ≤ singularCochainSubobject R k M S :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_singularCochainSubobjectι h)

/-- Under the identifications of the subcomplexes with relative cochain complexes, the inclusion
of the cochains vanishing on `T` into those vanishing on `S ⊆ T` is induced by the map of pairs
`(Y, S) ⟶ (Y, T)`. -/
@[reassoc]
lemma ofLE_comp_singularCochainSubobjectIso_hom {S T : Set Y} (h : S ⊆ T) :
    Subobject.ofLE _ _ (singularCochainSubobject_anti R k M h) ≫
        (singularCochainSubobjectIso R k M S).hom =
      (singularCochainSubobjectIso R k M T).hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (TopTriple.totalToOuter.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat :=
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := singularCochainSubobjectι R k M T) (f₂ := singularCochainSubobjectι R k M S) _
    (extendMap_comp_singularCochainSubobjectι h)).trans (Category.assoc _ _ _).symm

/-- Every cochain vanishes on the empty set. -/
@[simp]
lemma singularCochainSubobject_eq_top {S : Set Y} (hS : S = ∅) :
    singularCochainSubobject R k M S = ⊤ := by
  have : IsEmpty (TopPair.ofSubset S).snd := by
    rw [hS]
    exact Set.isEmpty_coe_sort.2 rfl
  have hS := (TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex R k M
  have : IsIso ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f :=
    hS.isIso_f_iff.2 ((TauCeti.ChainComplex.linearYonedaFunctor k M).map_isZero
      (SSet.isZero_chainComplex (X := (TopPair.toSSetPair.obj (TopPair.ofSubset S)).left) R).op)
  have : IsIso (singularCochainSubobjectι R k M S) :=
    Functor.map_isIso (ComplexShape.embeddingUpNat.extendFunctor _) _
  exact Subobject.mk_eq_top_of_isIso _

/-- Only the zero cochain vanishes on the whole space. -/
@[simp]
lemma singularCochainSubobject_eq_bot {S : Set Y} (hS : S = Set.univ) :
    singularCochainSubobject R k M S = ⊥ := by
  have : IsIso (TopPair.ofSubset S).map := by
    refine TopCat.isIso_of_bijective_of_isOpenMap _ ⟨Subtype.val_injective, fun y ↦ ?_⟩
      (hS ▸ isOpen_univ : IsOpen S).isOpenEmbedding_subtypeVal.isOpenMap
    exact ⟨⟨y, hS ▸ Set.mem_univ y⟩, rfl⟩
  have hS := (TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex R k M
  have : IsIso ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).g :=
    Functor.map_isIso (TauCeti.ChainComplex.linearYonedaFunctor k M) _
  have hz := (ComplexShape.embeddingUpNat.extendFunctor _).map_isZero (hS.isIso_g_iff.1 this)
  exact Subobject.mk_eq_bot_iff_zero.2 (hz.eq_of_src _ _)

/-- For `S ⊆ T`, the quotient of the cochains vanishing on `S` by those vanishing on `T` is the
relative cochain complex of the pair `(T, S)`, reindexed along `ℕ ⊆ ℤ`. The isomorphism is
induced by restriction from `Y` to `T` (`TauCeti.π_singularCochainSubobjectCokernelIso_hom`). -/
def singularCochainSubobjectCokernelIso {S T : Set Y} (h : S ⊆ T) :
    cokernel (Subobject.ofLE _ _ (singularCochainSubobject_anti R k M h)) ≅
      ((TopPair.ofInclusion h).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  have hS := ((TopTriple.ofSubset h).shortExact_singularCochainComplexShortComplex R k M).extend
    ComplexShape.embeddingUpNat
  cokernel.mapIso _
      (((TopTriple.ofSubset h).singularCochainComplexShortComplex R k M).map
        (ComplexShape.embeddingUpNat.extendFunctor _)).f
      (singularCochainSubobjectIso R k M T) (singularCochainSubobjectIso R k M S)
      (ofLE_comp_singularCochainSubobjectIso_hom R k M h) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hS.gIsCokernel

/-- The identification of the quotient with relative cochains is restriction from the cochains of
`Y` vanishing on `S` to the cochains of `T` vanishing on `S`. -/
@[reassoc (attr := simp)]
lemma π_singularCochainSubobjectCokernelIso_hom {S T : Set Y} (h : S ⊆ T) :
    cokernel.π _ ≫ (singularCochainSubobjectCokernelIso R k M h).hom =
      (singularCochainSubobjectIso R k M S).hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (TopTriple.innerToTotal.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

/-! ### The filtration of the cochains by vanishing on the stages of a filtered space -/

variable (X : ℤ → Set Y)

/-- The decreasing filtration of the singular cochains of `Y`, reindexed along `ℕ ⊆ ℤ`, attached
to a family `X : ℤ → Set Y` of subsets: its stage `F^p` consists of the cochains vanishing on
`X (p - 1)`. For an increasing family the graded piece `F^p / F^{p+1}` is the relative cochain
complex of the pair `(X p, X (p - 1))` (`TauCeti.singularCochainFiltrationCokernelIso`). -/
def singularCochainFiltration (p : ℤ) :
    Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat) :=
  singularCochainSubobject R k M (X (p - 1))

/-- The stage `F^p` of the filtration consists of the cochains vanishing on `X (p - 1)`. -/
lemma singularCochainFiltration_eq (p : ℤ) :
    singularCochainFiltration R k M X p = singularCochainSubobject R k M (X (p - 1)) := (rfl)

variable {X}

/-- An increasing family of subsets gives a decreasing filtration of singular cochains. -/
lemma antitone_singularCochainFiltration (hX : Monotone X) :
    Antitone (singularCochainFiltration R k M X) :=
  fun _ _ h ↦ singularCochainSubobject_anti R k M (hX (by lia))

variable (hX : Monotone X)

/-- The graded piece `F^p / F^{p+1}` of the filtration of the singular cochains of `Y` by
vanishing on the `X (p - 1)` is the relative cochain complex of the pair `(X p, X (p - 1))`,
reindexed along `ℕ ⊆ ℤ`. -/
def singularCochainFiltrationCokernelIso (p : ℤ) :
    cokernel (Subobject.ofLE _ _ (antitone_singularCochainFiltration R k M hX
        (by lia : p ≤ p + 1))) ≅
      ((TopPair.ofInclusion (hX (by lia : p - 1 ≤ p))).singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat :=
  Subobject.cokernelOfLEIsoOfEq (by rw [singularCochainFiltration, add_sub_cancel_right]) rfl _
      (singularCochainSubobject_anti R k M (hX (by lia : p - 1 ≤ p))) ≪≫
    singularCochainSubobjectCokernelIso R k M (hX (by lia : p - 1 ≤ p))

/-- **The cohomological spectral sequence of a filtered space.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the decreasing
filtration of the singular cochains of `Y` whose stage `F^p` consists of the cochains vanishing on
`X (p - 1)`, in the classical cohomological indexing: it starts on page `1`, its differentials are
`d_r : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}`, and `E₁^{p,q} = H^{p+q}(X p, X (p - 1))`
(`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`). -/
abbrev filteredSpaceCohomologySpectralSequence :=
  CochainComplex.decreasingFiltrationSpectralSequence (singularCochainFiltration R k M X)
    (antitone_singularCochainFiltration R k M hX)

/-- **The first page of the cohomological spectral sequence of a filtered space.** The object at
`(p, q)` is the relative singular cohomology `Hⁿ(X p, X (p - 1))`, where `p + q = n`. -/
def filteredSpaceCohomologySpectralSequenceFirstPageXIso (p q : ℤ) (n : ℕ) (hn : p + q = n) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q) ≅
      (TopPair.ofInclusion (hX (by lia : p - 1 ≤ p))).singularCohomology R k M n :=
  CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
    (homologyFunctor _ _ (p + q)).mapIso (singularCochainFiltrationCokernelIso R k M hX p) ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat hn.symm

/-- The first page of the cohomological spectral sequence of a filtered space vanishes in negative
total degree `p + q`, since singular cochains are concentrated in nonnegative degrees. -/
lemma isZero_filteredSpaceCohomologySpectralSequence_page_one_X (p q : ℤ) (h : p + q < 0) :
    IsZero (((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q)) :=
  IsZero.of_iso ((extend_exactAt _ ComplexShape.embeddingUpNat _ fun n hn ↦ by
      have : (n : ℤ) = p + q := hn
      lia).isZero_homology)
    (CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
      (homologyFunctor _ _ (p + q)).mapIso (singularCochainFiltrationCokernelIso R k M hX p))

/-- **The abutment of the cohomological spectral sequence of a filtered space** in degree `n` is
the singular cohomology `Hⁿ(Y)`. -/
def filteredSpaceCohomologyAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        ((antitone_singularCochainFiltration R k M hX).comp fun _ _ h ↦ neg_le_neg h))).abutment
        n ≅
      Y.singularCohomology R k M n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat rfl

/-- **Strong convergence of the cohomological spectral sequence of a finite filtration of a
space.** If `X (b - 1)` is empty and `X (a - 1)` is all of `Y`, then on every page `r ≥ 1` with
`a ≤ p + r` and `p - r + 1 ≤ b`, the object at `(p, q)` is the graded piece
`F^p H^{p+q} / F^{p+1} H^{p+q}` of the induced filtration of the abutment, which is `H^{p+q}(Y)`
by `TauCeti.filteredSpaceCohomologyAbutmentIso`. -/
def filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFinite {a b : ℤ}
    (ha : X (a - 1) = Set.univ) (hb : X (b - 1) = ∅) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hra : a ≤ p + r) (hrb : p - r + 1 ≤ b) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page r).X (p, q) ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
          ((antitone_singularCochainFiltration R k M hX).comp fun _ _ h ↦ neg_le_neg h)))
        (-p - 1) (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFinite _ _
    (singularCochainSubobject_eq_bot R k M ha) (singularCochainSubobject_eq_top R k M hb) r hr p q
    hra hrb

/-! ### Cochains vanishing on simplices -/

/-- A cochain of `Y` in degree `m`, read in the complex reindexed along `ℕ ⊆ ℤ`, vanishes on `S`
exactly when it vanishes on every singular `m`-simplex of `Y` with image in `S`. -/
theorem mem_range_singularCochainSubobject_arrow_f_iff (S : Set Y) (m : ℕ)
    (x : ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X m) :
    x ∈ LinearMap.range ((singularCochainSubobject R k M S).arrow.f m).hom ↔
      ∀ σ : (TopCat.toSSet.obj Y) _⦋m⦌, Set.range (TopCat.simplexMap σ) ⊆ S →
        (TopCat.toSSet.obj Y).ιChainComplex σ ≫
          ((Y.singularCochainComplex R k M).extendXIso ComplexShape.embeddingUpNat rfl).hom x =
            0 := by
  set P := TopPair.ofSubset S
  have hsurj : LinearMap.range ((singularCochainSubobjectIso R k M S).hom.f m).hom = ⊤ :=
    LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  rw [← singularCochainSubobjectIso_hom_comp_singularCochainSubobjectι, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _ hsurj, singularCochainSubobjectι]
  refine (mem_range_extendMap_f_iff (e := ComplexShape.embeddingUpNat)
    (P.singularCochainComplexShortComplex R k M).f (i := m) rfl x).trans ?_
  -- A cochain lies in the image of relative cochains exactly when it vanishes on the chains of
  -- `S`, since relative chains are the cokernel of the chains of `S`.
  have key (y : (Y.singularCochainComplex R k M).X m) :
      y ∈ LinearMap.range ((P.singularCochainComplexShortComplex R k M).f.f m).hom ↔
        (SSet.chainComplexMap (TopPair.toSSetPair.obj P).hom R).f m ≫ y = 0 := by
    constructor
    · rintro ⟨g, rfl⟩
      -- The image of `g` is the composite of the quotient map with `g`.
      exact (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ g) ((TopPair.toSSetPair.obj P).chainComplex_condition_f R m)).trans
          zero_comp
    · intro hy
      exact ⟨((TopPair.toSSetPair.obj P).isColimitCokernelCoforkChainComplexX R m).desc
        (CokernelCofork.ofπ y hy),
        ((TopPair.toSSetPair.obj P).isColimitCokernelCoforkChainComplexX R m).fac _
          WalkingParallelPair.one⟩
  refine (key _).trans ?_
  constructor
  · intro h σ hσ
    obtain ⟨τ, rfl⟩ := (P.mem_range_toSSet_map_app_iff_range_simplexMap_subset σ).2
      (by rwa [TopPair.range_ofSubset_map])
    -- The summand of the image of `τ` is the summand of `τ` followed by the inclusion of the
    -- chains of `S`; the ambient space of `P` is `Y` only definitionally.
    exact (SSet.ι_chainComplexMap_f_assoc (f := TopCat.toSSet.map P.map) (R := R) (x := τ) (h := _)
      ).symm.trans ((congrArg (_ ≫ ·) h).trans comp_zero)
  · intro h
    refine SSet.chainComplex_hom_ext fun τ ↦ ?_
    refine (SSet.ι_chainComplexMap_f_assoc (f := (TopPair.toSSetPair.obj P).hom) (R := R)
      (x := τ) (h := _)).trans (.trans ?_ comp_zero.symm)
    exact h _ (by
      rw [← TopPair.range_ofSubset_map (B := S)]
      exact (P.mem_range_toSSet_map_app_iff_range_simplexMap_subset _).1 ⟨τ, rfl⟩)

/-! ### Exhaustive filtrations -/

omit hX in
/-- The case of `TauCeti.isCompleteFiltration_singularCochainFiltration` in the degrees `m ≥ 0`
where the reindexed cochains are the singular cochains. -/
private lemma isCompleteFiltration_singularCochainFiltration_natCast (hX : Monotone X)
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (m : ℕ) :
    TauCeti.IsCompleteFiltration fun j : ℕ ↦
      LinearMap.range ((singularCochainFiltration R k M X j).arrow.f m).hom := by
  let e : ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X m ≅
      (Y.singularCochainComplex R k M).X m :=
    (Y.singularCochainComplex R k M).extendXIso ComplexShape.embeddingUpNat rfl
  -- The value on a singular simplex `σ`, as a linear function of the reindexed cochain.
  let E (σ : (TopCat.toSSet.obj Y) _⦋m⦌) :
      ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X m →ₗ[k] (R ⟶ M) :=
    (Linear.leftComp k M ((TopCat.toSSet.obj Y).ιChainComplex σ)).comp e.hom.hom
  have hmem (j : ℕ) (x) :
      x ∈ LinearMap.range ((singularCochainFiltration R k M X j).arrow.f m).hom ↔
        ∀ σ, Set.range (TopCat.simplexMap σ) ⊆ X (j - 1) → E σ x = 0 :=
    mem_range_singularCochainSubobject_arrow_f_iff R k M (X (j - 1)) m x
  -- Each simplex lies in some stage; `w σ` is the first stage `j` with image in `X (j - 1)`.
  have hw (σ : (TopCat.toSSet.obj Y) _⦋m⦌) :
      ∃ j : ℕ, Set.range (TopCat.simplexMap σ) ⊆ X (j - 1) := by
    -- The topological simplex is a universe lift of a compact standard simplex.
    have : CompactSpace (SimplexCategory.toTop₀.obj ⦋m⦌) :=
      inferInstanceAs (CompactSpace (Convexity.StdSimplex ℝ (Fin (m + 1))))
    have : CompactSpace (SimplexCategory.toTop.{w}.obj ⦋m⦌) :=
      inferInstanceAs (CompactSpace (ULift _))
    exact (hK _ (isCompact_range (TopCat.simplexMap σ).continuous)).imp'
      (fun q ↦ (q + 1).toNat) fun q hq ↦ hq.trans (hX (by lia))
  classical
  let w σ := Nat.find (hw σ)
  have hinj : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).1 inferInstance
  refine ⟨fun i j hij x hx ↦ (hmem i x).2 fun σ hσ ↦ (hmem j x).1 hx σ
      (hσ.trans (hX (by lia))),
    fun x hx ↦ hinj ((SSet.chainComplex_hom_ext fun σ ↦
      ((hmem _ x).1 (hx (w σ)) σ (Nat.find_spec (hw σ))).trans comp_zero.symm).trans
        (map_zero e.hom.hom).symm),
    fun x hx ↦ ?_⟩
  -- Along the sequence the value on `σ` no longer changes from the stage `w σ` on.
  have hconst (σ : (TopCat.toSSet.obj Y) _⦋m⦌) (j : ℕ) (hj : w σ ≤ j) :
      E σ (x j) = E σ (x (w σ)) := by
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih =>
      rw [← ih, ← sub_eq_zero, ← map_sub]
      exact (hmem j _).1 (hx j) σ ((Nat.find_spec (hw σ)).trans (hX (by lia)))
  let L : ((TopCat.toSSet.obj Y).chainComplex R).X m ⟶ M :=
    Cofan.IsColimit.desc ((TopCat.toSSet.obj Y).isColimitChainComplexXCofan R m)
      fun σ ↦ E σ (x (w σ))
  refine ⟨e.inv.hom L, fun j ↦ (hmem j _).2 fun σ hσ ↦ ?_⟩
  rw [map_sub, sub_eq_zero, hconst σ j (Nat.find_min' (hw σ) hσ)]
  exact (congrArg ((TopCat.toSSet.obj Y).ιChainComplex σ ≫ ·) (Iso.inv_hom_id_apply e L)).trans
    (Cofan.IsColimit.fac ((TopCat.toSSet.obj Y).isColimitChainComplexXCofan R m) _ σ)

omit hX in
/-- **The filtration of the cochains of an exhaustive filtered space is complete.** Let `X` be an
increasing family of subsets of `Y` absorbing compact sets: every compact subset of `Y` lies in
some `X q`. Then in each degree the filtration of the singular cochains of `Y` by vanishing on the
`X (j - 1)`, `j ≥ 0`, is complete and separated. The family need not reach `Y` at any finite
stage, as for the preimages of the skeleta of an infinite-dimensional CW complex, so no stage of
the filtration need vanish in any degree. -/
theorem isCompleteFiltration_singularCochainFiltration (hX : Monotone X)
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (n : ℤ) :
    TauCeti.IsCompleteFiltration fun j : ℕ ↦
      LinearMap.range ((singularCochainFiltration R k M X j).arrow.f n).hom := by
  by_cases hn : ∃ m : ℕ, ComplexShape.embeddingUpNat.f m = n
  · obtain ⟨m, hm⟩ := hn
    obtain rfl : (m : ℤ) = n := hm
    exact isCompleteFiltration_singularCochainFiltration_natCast R k M hX hK m
  -- In negative degrees the reindexed cochains vanish.
  push Not at hn
  have : Subsingleton (((Y.singularCochainComplex R k M).extend
      ComplexShape.embeddingUpNat).X n) :=
    ModuleCat.isZero_iff_subsingleton.1 (isZero_extend_X _ _ n hn)
  exact ⟨fun _ _ _ x _ ↦ Subsingleton.elim x 0 ▸ zero_mem _,
    fun x _ ↦ Subsingleton.elim x 0,
    fun _ _ ↦ ⟨0, fun _ ↦ by rw [Subsingleton.elim (_ - _) 0]; exact zero_mem _⟩⟩

/-- **Strong convergence of the cohomological spectral sequence of an exhaustive first-quadrant
filtration of a space.** Let `X` be an increasing family of subsets of `Y` absorbing compact sets,
with `X (-1)` empty, such that the relative cohomology `Hⁿ(X j, X (j - 1))` vanishes for `n < j`,
as for the preimages of the skeleta of a CW complex under a Serre fibration. Then on every page
`r ≥ 1` with `p < r` and `q + 1 < r`, the object at `(p, q)` is the graded piece
`F^p H^{p+q} / F^{p+1} H^{p+q}` of the induced filtration of the abutment, which is `H^{p+q}(Y)` by
`TauCeti.filteredSpaceCohomologyAbutmentIso`. This filtration of `Hⁿ(Y)` is finite: its stage `p`
vanishes for `n < p`
(`CochainComplex.isZero_filtrationAbutmentFiltration_of_antitone_of_firstQuadrant`). No stage
`X q` need be all of `Y`. -/
def filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFirstQuadrant
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (h₀ : X (-1) = ∅)
    (hvanish : ∀ j : ℤ, 0 ≤ j → ∀ n : ℕ, n < j →
      IsZero ((TopPair.ofInclusion (hX (by lia : j - 1 ≤ j))).singularCohomology R k M n))
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hp : p < r) (hqr : q + 1 < r) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page r).X (p, q) ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
          ((antitone_singularCochainFiltration R k M hX).comp fun _ _ h ↦ neg_le_neg h)))
        (-p - 1) (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFirstQuadrant _ _
    (singularCochainSubobject_eq_top R k M (by rwa [zero_sub]))
    (isCompleteFiltration_singularCochainFiltration R k M hX hK)
    (fun j hj n hn ↦ by
      refine IsZero.of_iso ?_ ((homologyFunctor _ _ n).mapIso
        (singularCochainFiltrationCokernelIso R k M hX j))
      by_cases hm : ∃ m : ℕ, ComplexShape.embeddingUpNat.f m = n
      · obtain ⟨m, hm⟩ := hm
        have : (m : ℤ) = n := hm
        exact (hvanish j hj m (by lia)).of_iso
          (extendHomologyIso _ _ hm)
      · push Not at hm
        exact (extend_exactAt _ _ n hm).isZero_homology)
    r hr p q hp hqr

end TauCeti
