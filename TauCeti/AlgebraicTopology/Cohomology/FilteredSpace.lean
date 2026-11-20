/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.CategoryTheory.Subobject.Cokernel
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The cohomology spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a map to it. The singular cochains of `Y`
relative to the `X q` form a decreasing filtration of the singular cochains of `Y`: the cochains
vanishing on the chains of `X q` (`TauCeti.singularCochainFiltration`). This file studies the
spectral sequence of that filtered cochain complex
(`TauCeti.filteredSpaceCohomologySpectralSequence`), in the classical cohomological indexing of
`CochainComplex.decreasingFiltrationSpectralSequence`, with the stage `F^p` the cochains vanishing
on `X (p - 1)`.

* **Graded pieces.** For `X a ⊆ X b`, the quotient of the cochains relative to `X a` by those
  relative to `X b` is the relative singular cochain complex of the pair `(X b, X a)`
  (`TauCeti.singularCochainFiltrationCokernelIso`), because the cochain sequence of the triple
  `(Y, X b, X a)` is short exact.
* **First page.** The object at `(p, q)` on the first page is the relative singular cohomology
  `Hⁿ(X p, X (p - 1))` with `p + q = n`
  (`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`); it vanishes when `p + q < 0`.
* **Convergence.** The abutment in degree `n` is `Hⁿ(Y)`
  (`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by the images `F^p H` of the
  cohomology of `Y` relative to `X (p - 1)`. When `X a = ∅` and `X b = Y`, the filtration is
  finite and the spectral sequence converges strongly: on late pages the object at `(p, q)` is the
  graded piece `F^p H / F^{p+1} H` of the filtration of `H^{p+q}(Y)`
  (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFinite`).
* **Completeness.** Suppose instead that `X (-1)` is empty and that every compact subset of `Y`
  lies in some `X q`. A singular simplex has compact image, so a cochain is determined by its
  values on the simplices of the `X q`, and a family of cochains which agree on larger and larger
  `X q` glues to a cochain: the filtration is complete and separated in each degree
  (`TauCeti.isCompleteFiltration_singularCochainFiltration`). If moreover `Hⁿ(X j, X (j - 1))`
  vanishes for `n < j`, the spectral sequence converges strongly
  (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGraded`), although no stage of the
  filtration need vanish in any degree. This is the situation of the skeletal filtration of the
  total space of a fibration over an infinite-dimensional CW complex.

Filtering the total space of a fibration by the preimages of the skeleta of the base gives the
cohomology Serre spectral sequence, with `E₁^{p,q} = H^{p+q}(Eₚ, Eₚ₋₁)`
(`TauCeti.TopCat.serreCohomologySpectralSequence`). The identification of the first differential
with the connecting map of the triple `(X (p + 1), X p, X (p - 1))`
(`TauCeti.TopTriple.singularCohomologyδ`) is not treated here.

This is the cohomological counterpart of `TauCeti.filteredSpaceSpectralSequence`
(`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic`), whose construction it dualises.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex, and Chapter 5, its application to the
  filtration of a total space by the preimages of the skeleta of the base.
* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorem 5.5.10, convergence of a complete
  filtration.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*)
  [Ring k] [Linear k C] (M : C) {Y : TopCat.{w}} (X : ℤ → Set Y)

/-- The inclusion of the singular cochains of `Y` relative to `X q` into the singular cochains of
`Y`, with both cochain complexes reindexed along `ℕ ⊆ ℤ`. -/
def singularCochainFiltrationι (q : ℤ) :
    ((TopPair.ofSubset (X q)).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat ⟶
      (Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  extendMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
    ((TopPair.ofSubset (X q)).singularChainComplexπ R).op) _

/-- The inclusion of the relative singular cochains is induced by the quotient map from the
singular chains of `Y` to the relative singular chains of `(Y, X q)`. -/
lemma singularCochainFiltrationι_def (q : ℤ) :
    singularCochainFiltrationι R k M X q =
      extendMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
        ((TopPair.ofSubset (X q)).singularChainComplexπ R).op) ComplexShape.embeddingUpNat := by
  rw [singularCochainFiltrationι]

instance (q : ℤ) : Mono (singularCochainFiltrationι R k M X q) := by
  have := ((TopPair.ofSubset (X q)).shortExact_singularCochainComplexShortComplex R k M).mono_f
  rw [singularCochainFiltrationι_def]
  exact HomologicalComplex.mono_extendMap _ _

/-- The filtration of the singular cochains of `Y` by the cochains vanishing on the chains of the
subsets `X q`, with the cochain complexes reindexed along `ℕ ⊆ ℤ`. It decreases as `X q` grows. -/
def singularCochainFiltration (q : ℤ) :
    Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat) :=
  Subobject.mk (singularCochainFiltrationι R k M X q)

/-- The stage of the filtration at `q` is the reindexed relative singular cochain complex of the
pair `(Y, X q)`. -/
def singularCochainFiltrationIso (q : ℤ) :
    (singularCochainFiltration R k M X q : CochainComplex (ModuleCat.{v} k) ℤ) ≅
      ((TopPair.ofSubset (X q)).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  Subobject.underlyingIso (singularCochainFiltrationι R k M X q)

/-- The identification of the stage at `q` with relative cochains is compatible with the
inclusions into the cochains of `Y`. -/
@[reassoc (attr := simp)]
lemma singularCochainFiltrationIso_hom_comp_singularCochainFiltrationι (q : ℤ) :
    (singularCochainFiltrationIso R k M X q).hom ≫ singularCochainFiltrationι R k M X q =
      (singularCochainFiltration R k M X q).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {X}

/-- For `X a ⊆ X b`, the inclusion of the cochains relative to `X b` into the cochains of `Y`
factors through the restriction `C*(Y, X b) ⟶ C*(Y, X a)` of the triple `(Y, X b, X a)`. -/
@[simp, reassoc]
lemma extendMap_comp_singularCochainFiltrationι {a b : ℤ} (hab : X a ⊆ X b) :
    extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.totalToOuter.app (TopTriple.ofSubset hab))) ComplexShape.embeddingUpNat ≫
      singularCochainFiltrationι R k M X a = singularCochainFiltrationι R k M X b := by
  rw [singularCochainFiltrationι_def, singularCochainFiltrationι_def]
  -- The quotient map to the chains relative to `X a`, followed by the map to the chains relative
  -- to `X b`, is the quotient map to the chains relative to `X b`; apply `Hom(-, M)`. The pairs of
  -- the triple `(Y, X b, X a)` are the pairs `(Y, X b)` and `(Y, X a)` only up to definitional
  -- unfolding, so the composites are formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) <|
    ((TauCeti.ChainComplex.linearYonedaFunctor k M).map_comp _ _).symm.trans <|
      congrArg (fun f ↦ (TauCeti.ChainComplex.linearYonedaFunctor k M).map f.op)
        ((TopTriple.ofSubset hab).singularChainComplexπ_comp_totalToOuter R)

/-- The filtration of singular cochains is antitone in the subsets. -/
lemma singularCochainFiltration_anti {a b : ℤ} (hab : X a ⊆ X b) :
    singularCochainFiltration R k M X b ≤ singularCochainFiltration R k M X a :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_singularCochainFiltrationι R k M hab)

/-- Under the identifications of the stages of the filtration with relative cochain complexes,
the inclusion `F_b ⟶ F_a` is the restriction of the triple `(Y, X b, X a)`. -/
@[reassoc]
lemma ofLE_comp_singularCochainFiltrationIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    Subobject.ofLE _ _ (singularCochainFiltration_anti R k M hab) ≫
        (singularCochainFiltrationIso R k M X a).hom =
      (singularCochainFiltrationIso R k M X b).hom ≫
        extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
          (TopTriple.totalToOuter.app (TopTriple.ofSubset hab))) ComplexShape.embeddingUpNat :=
  -- As above, the stages are related to the pairs of the triple only definitionally, so the
  -- equations are composed directly rather than by `rw`.
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := singularCochainFiltrationι R k M X b) (f₂ := singularCochainFiltrationι R k M X a) _
    (extendMap_comp_singularCochainFiltrationι R k M hab)).trans (Category.assoc _ _ _).symm

/-- An increasing family of subsets gives a decreasing filtration of singular cochains. -/
lemma antitone_singularCochainFiltration (hX : Monotone X) :
    Antitone (singularCochainFiltration R k M X) :=
  fun _ _ h ↦ singularCochainFiltration_anti R k M (hX h)

/-- The stage of the filtration at an empty subset is everything. -/
@[simp]
lemma singularCochainFiltration_eq_top {a : ℤ} (ha : X a = ∅) :
    singularCochainFiltration R k M X a = ⊤ := by
  have : IsEmpty (TopPair.ofSubset (X a)).snd := by
    rw [ha]
    exact Set.isEmpty_coe_sort.2 rfl
  have : IsIso ((TopPair.ofSubset (X a)).singularChainComplexπ R) :=
    SSetPair.isIso_chainComplexπ _ R
  have : IsIso (singularCochainFiltrationι R k M X a) := by
    rw [singularCochainFiltrationι_def]
    exact Functor.map_isIso (ComplexShape.embeddingUpNat.extendFunctor _) _
  exact Subobject.mk_eq_top_of_isIso _

/-- The stage of the filtration at the whole space is zero. -/
@[simp]
lemma singularCochainFiltration_eq_bot {b : ℤ} (hb : X b = Set.univ) :
    singularCochainFiltration R k M X b = ⊥ := by
  have := TopPair.isIso_ofSubset_map_of_eq_univ hb
  -- The map of the singular simplicial pair of `(Y, X b)` is `TopCat.toSSet.map` of the
  -- inclusion of `X b` by definition (`TopPair.toSSetPair_obj_hom`).
  have : IsIso (TopPair.toSSetPair.obj (TopPair.ofSubset (X b))).hom :=
    inferInstanceAs (IsIso (TopCat.toSSet.map (TopPair.ofSubset (X b)).map))
  have hz : IsZero (((TopPair.ofSubset (X b)).singularCochainComplex R k M).extend
      ComplexShape.embeddingUpNat) :=
    (ComplexShape.embeddingUpNat.extendFunctor _).map_isZero <|
      (TauCeti.ChainComplex.linearYonedaFunctor k M).map_isZero
        (SSetPair.isZero_chainComplex (TopPair.toSSetPair.obj (TopPair.ofSubset (X b))) R).op
  exact Subobject.mk_eq_bot_iff_zero.2 (hz.eq_of_src _ _)

/-- For `X a ⊆ X b`, the quotient of the cochains relative to `X a` by the cochains relative to
`X b` is the relative singular cochain complex of the pair `(X b, X a)`, reindexed along
`ℕ ⊆ ℤ`. The isomorphism is induced by the restriction of cochains of the triple
`(Y, X b, X a)` (`TauCeti.π_singularCochainFiltrationCokernelIso_hom`). -/
def singularCochainFiltrationCokernelIso {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel (Subobject.ofLE _ _ (singularCochainFiltration_anti R k M hab)) ≅
      ((TopPair.ofInclusion hab).singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat :=
  have hS := ((TopTriple.ofSubset hab).shortExact_singularCochainComplexShortComplex R k M).extend
    ComplexShape.embeddingUpNat
  cokernel.mapIso _ _ (singularCochainFiltrationIso R k M X b)
      (singularCochainFiltrationIso R k M X a)
      (ofLE_comp_singularCochainFiltrationIso_hom R k M hab) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hS.gIsCokernel

/-- The identification of `F_a / F_b` with relative singular cochains is induced by the
restriction from the cochains of `Y` relative to `X a` to the cochains of the pair `(X b, X a)`. -/
@[reassoc (attr := simp)]
lemma π_singularCochainFiltrationCokernelIso_hom {a b : ℤ} (hab : X a ⊆ X b) :
    cokernel.π _ ≫ (singularCochainFiltrationCokernelIso R k M hab).hom =
      (singularCochainFiltrationIso R k M X a).hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (TopTriple.innerToTotal.app (TopTriple.ofSubset hab))) ComplexShape.embeddingUpNat :=
  -- The cokernel of the triple's cochain sequence is stated for the pairs of the triple, so the
  -- colimit equations are composed directly rather than through `simp`.
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

section SpectralSequence

variable (hX : Monotone X)

include hX in
/-- The stages `F^p`, the cochains vanishing on `X (p - 1)`, form a decreasing filtration. -/
lemma antitone_singularCochainFiltration_sub_one :
    Antitone fun p : ℤ ↦ singularCochainFiltration R k M X (p - 1) :=
  fun _ _ h ↦ antitone_singularCochainFiltration R k M hX (by lia)

/-- **The cohomology spectral sequence of a filtered space.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the decreasing
filtration of the singular cochains of `Y` whose stage `F^p` is the cochains vanishing on
`X (p - 1)`, in the classical cohomological indexing: it starts on page `1`, its differentials are
`d_r : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}`, and `E₁^{p,q} = H^{p+q}(X p, X (p - 1))`. -/
abbrev filteredSpaceCohomologySpectralSequence :=
  CochainComplex.decreasingFiltrationSpectralSequence _
    (antitone_singularCochainFiltration_sub_one R k M hX)

/-- **The spectral object of the cohomology spectral sequence of a filtered space**, whose
abutment in degree `n` is `Hⁿ(Y)` (`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by the
images of the cohomology of the cochains vanishing on the `X (p - 1)`: the piece indexed by `-p`
is the image of the cohomology of `Y` relative to `X (p - 1)`. -/
abbrev filteredSpaceCohomologySpectralObject :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
    ((antitone_singularCochainFiltration_sub_one R k M hX).comp fun _ _ h ↦ neg_le_neg h))

/-- The object at `(p, q)` on the first page is the cohomology in degree `p + q` of the reindexed
relative singular cochains of `(X b, X a)`, for `a = p - 1` and `b = p`. -/
private def firstPageXIsoExtend (p q a b : ℤ) (ha : a = p - 1) (hb : b = p) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q) ≅
      (((TopPair.ofInclusion (hX (by lia : a ≤ b))).singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat).homology (p + q) :=
  CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
    (homologyFunctor _ _ (p + q)).mapIso
      (Subobject.cokernelOfLEIsoOfEq (by rw [hb, add_sub_cancel_right]) (by rw [ha]) _
          (singularCochainFiltration_anti R k M (hX (by lia : a ≤ b))) ≪≫
        singularCochainFiltrationCokernelIso R k M (hX (by lia : a ≤ b)))

/-- **The first page of the cohomology spectral sequence of a filtered space.** The object at
`(p, q)` on the first page is the relative singular cohomology `Hⁿ(X p, X (p - 1))`, where
`p + q = n`. The indices `p - 1` and `p` are given as `a` and `b` together with equations, for
flexibility. -/
def filteredSpaceCohomologySpectralSequenceFirstPageXIso (p q a b : ℤ) (ha : a = p - 1)
    (hb : b = p) (n : ℕ) (hn : p + q = n) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q) ≅
      (TopPair.ofInclusion (hX (by lia : a ≤ b))).singularCohomology R k M n :=
  firstPageXIsoExtend R k M hX p q a b ha hb ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat hn.symm

/-- The first page of the cohomology spectral sequence of a filtered space vanishes in negative
total degree `p + q`, since singular cochains are concentrated in nonnegative degrees. -/
lemma isZero_filteredSpaceCohomologySpectralSequence_page_one_X (p q : ℤ) (h : p + q < 0) :
    IsZero (((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q)) :=
  IsZero.of_iso ((extend_exactAt _ ComplexShape.embeddingUpNat _ fun n hn ↦ by
      rw [ComplexShape.embeddingUpNat_f] at hn
      lia).isZero_homology)
    (firstPageXIsoExtend R k M hX p q (p - 1) p rfl rfl)

/-- **The abutment of the cohomology spectral sequence of a filtered space** in degree `n` is the
singular cohomology `Hⁿ(Y)`. -/
def filteredSpaceCohomologyAbutmentIso (n : ℕ) :
    (filteredSpaceCohomologySpectralObject R k M hX).abutment n ≅
      Y.singularCohomology R k M n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat rfl

/-- **Strong convergence of the cohomology spectral sequence of a finite filtration of a space.**
If `X a = ∅` and `X b` is all of `Y`, then on every page `r ≥ 1` with `b + 1 ≤ p + r` and
`p - r ≤ a`, the object at `(p, q)` is the graded piece `F^p H / F^{p+1} H` of the filtration of the
abutment in degree `p + q`, which is `H^{p+q}(Y)` by `TauCeti.filteredSpaceCohomologyAbutmentIso`;
here `F^p H` is the image of the cohomology of `Y` relative to `X (p - 1)`. -/
def filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFinite {a b : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hra : b + 1 ≤ p + r)
    (hrb : p - r ≤ a) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page r).X (p, q) ≅
      cokernel ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltrationMap (-p - 1)
        (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFinite _ _
    (a := b + 1) (b := a + 1)
    (by rw [add_sub_cancel_right]; exact singularCochainFiltration_eq_bot R k M hb)
    (by rw [add_sub_cancel_right]; exact singularCochainFiltration_eq_top R k M ha) r hr p q hra
    (by lia)

end SpectralSequence

/-! ### Completeness and convergence -/

section Complete

variable {R k M}

/-- In degree `n`, a cochain of `Y` is a relative cochain of `(Y, S)` exactly when it vanishes on
every singular `n`-simplex of `Y` with image in `S`. -/
private lemma mem_range_f_iff (S : Set Y) (n : ℕ)
    (y : ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).X₂.X n) :
    y ∈ LinearMap.range
        (((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f.f n).hom ↔
      ∀ σ : (TopCat.toSSet.obj Y) _⦋n⦌, Set.range (Y.toSSetObjEquiv _ σ) ⊆ S →
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ y = 0 := by
  -- The cochain sequence of the pair is exact: relative cochains are the cochains whose
  -- restriction to `S` vanishes.
  have hP := (((TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex
    R k M).map_of_exact (HomologicalComplex.eval _ _ n)).exact.moduleCat_range_eq_ker
  refine (Iff.of_eq (congrArg (y ∈ ·) hP)).trans LinearMap.mem_ker |>.trans ?_
  -- The restriction to `S` is precomposition with the chains of `S`; the subtype coercions of the
  -- two pairs of spaces involved differ, so the restriction is stated with `change`.
  change (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset S).map) R).f n ≫ y = 0 ↔ _
  constructor
  · intro h σ hσ
    obtain ⟨τ, rfl⟩ := ((TopPair.range_ofSubset_map (B := S) ▸
      (TopPair.ofSubset S).isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff _ σ).2 hσ)
    exact (SSet.ι_chainComplexMap_f_assoc _ _ (TopCat.toSSet.map (TopPair.ofSubset S).map) R τ
      y).symm.trans ((congrArg (_ ≫ ·) h).trans comp_zero)
  · intro h
    refine SSet.chainComplex_hom_ext fun τ ↦ ?_
    refine (SSet.ι_chainComplexMap_f_assoc _ _ (TopCat.toSSet.map (TopPair.ofSubset S).map) R τ
      y).trans ((h _ ?_).trans comp_zero.symm)
    exact (TopPair.range_ofSubset_map (B := S) ▸
      (TopPair.ofSubset S).isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff _ _).1 ⟨τ, rfl⟩

/-- **The filtration of singular cochains, elementwise.** A cochain of `Y` in degree `n` lies in
the stage of the filtration at `q` exactly when it vanishes on every singular `n`-simplex of `Y`
with image in `X q`. The cochain is read in degree `m = n` of the reindexed complex. -/
theorem mem_range_singularCochainFiltration_arrow_iff (X : ℤ → Set Y) (q : ℤ) {n : ℕ} {m : ℤ}
    (hn : ComplexShape.embeddingUpNat.f n = m)
    (x : ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X m) :
    x ∈ LinearMap.range ((singularCochainFiltration R k M X q).arrow.f m).hom ↔
      ∀ σ : (TopCat.toSSet.obj Y) _⦋n⦌, Set.range (Y.toSSetObjEquiv _ σ) ⊆ X q →
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫
          (extendXIso (Y.singularCochainComplex R k M) ComplexShape.embeddingUpNat hn).hom x =
          0 := by
  -- The ambient cochains of the pair `(Y, X q)` are those of `Y` up to unfolding; the isomorphism
  -- is taken at the former to match the terms of the cochain sequence of the pair.
  let eY := extendXIso ((TopPair.ofSubset (X q)).singularCochainComplexShortComplex R k M).X₂
    ComplexShape.embeddingUpNat hn
  let eP := extendXIso ((TopPair.ofSubset (X q)).singularCochainComplex R k M)
    ComplexShape.embeddingUpNat hn
  -- The range of the arrow is the range of the inclusion of the relative cochains.
  have hrange : LinearMap.range ((singularCochainFiltration R k M X q).arrow.f m).hom =
      LinearMap.range ((singularCochainFiltrationι R k M X q).f m).hom := by
    rw [← singularCochainFiltrationIso_hom_comp_singularCochainFiltrationι,
      HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  rw [hrange, singularCochainFiltrationι_def, extendMap_f _ _ hn]
  refine Iff.trans ?_ (mem_range_f_iff (X q) n (eY.hom x))
  -- In degree `m` the inclusion is that of degree `n`, conjugated by the isomorphisms `eP`, `eY`;
  -- the composites are restated as applied composites, which `rw` does not unfold.
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨eP.hom y, ?_⟩
    change _ = ((eP.hom ≫
      ((TopPair.ofSubset (X q)).singularCochainComplexShortComplex R k M).f.f n ≫ eY.inv) ≫
        eY.hom) y
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ModuleCat.comp_apply]
  · rintro ⟨z, hz⟩
    refine ⟨eP.inv z, ?_⟩
    change (eP.inv ≫ eP.hom ≫
      ((TopPair.ofSubset (X q)).singularCochainComplexShortComplex R k M).f.f n ≫ eY.inv) z = x
    rw [Iso.inv_hom_id_assoc, ModuleCat.comp_apply]
    exact (congrArg eY.inv hz).trans (Iso.hom_inv_id_apply eY x)

/-- If every compact subset of `Y` lies in some `X q`, every singular simplex of `Y` lies in some
`X (j - 1)` with `j` a natural number. -/
private lemma exists_range_subset (hX : Monotone X) (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q)
    {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    ∃ j : ℕ, Set.range (Y.toSSetObjEquiv _ σ) ⊆ X (j - 1) := by
  obtain ⟨q, hq⟩ := hK _ (isCompact_range (Y.toSSetObjEquiv _ σ).continuous)
  exact ⟨(q + 1).toNat, hq.trans (hX (by lia))⟩

/-- **Limits for the filtration of singular cochains.** If every compact subset of `Y` lies in
some `X q`, a sequence of cochains whose `j`th and `(j + 1)`st terms agree on `X (j - 1)` has a
limit: a cochain agreeing with its `j`th term on `X (j - 1)` for every `j`. The sequence
stabilizes on each singular simplex, and the stable values define the limit. -/
private lemma exists_limit (hX : Monotone X) (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q)
    {n : ℕ} {m : ℤ} (hn : ComplexShape.embeddingUpNat.f n = m)
    (x : ℕ → ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X m)
    (hx : ∀ j : ℕ, x (j + 1) - x j ∈
      LinearMap.range ((singularCochainFiltration R k M X (j - 1)).arrow.f m).hom) :
    ∃ L, ∀ j : ℕ, L - x j ∈
      LinearMap.range ((singularCochainFiltration R k M X (j - 1)).arrow.f m).hom := by
  let e := extendXIso (Y.singularCochainComplex R k M) ComplexShape.embeddingUpNat hn
  have hmem (j : ℕ) (x) := mem_range_singularCochainFiltration_arrow_iff (R := R) (k := k)
    (M := M) X (j - 1) hn x
  -- The terms of the sequence agree, on a simplex of `X (a - 1)`, from the `a`th term on.
  have hstep (j : ℕ) (σ : (TopCat.toSSet.obj Y) _⦋n⦌)
      (hσ : Set.range (Y.toSSetObjEquiv _ σ) ⊆ X (j - 1)) :
      (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ e.hom (x (j + 1)) =
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ e.hom (x j) := by
    have := (hmem j _).1 (hx j) σ hσ
    rw [map_sub] at this
    exact sub_eq_zero.1 ((Preadditive.comp_sub _ _ _).symm.trans this)
  have hagree (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ℕ)
      (hσ : Set.range (Y.toSSetObjEquiv _ σ) ⊆ X (a - 1)) (b : ℕ) (hab : a ≤ b) :
      (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ e.hom (x b) =
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ e.hom (x a) := by
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ b hab ih => exact (hstep b σ (hσ.trans (hX (by lia)))).trans ih
  choose J hJ using fun σ : (TopCat.toSSet.obj Y) _⦋n⦌ ↦ exists_range_subset hX hK σ
  -- The limit takes on each simplex the value at which the sequence stabilizes there.
  let z := Cofan.IsColimit.desc ((TopCat.toSSet.obj Y).isColimitChainComplexXCofan R n)
    fun σ ↦ (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ e.hom (x (J σ))
  refine ⟨e.inv z, fun j ↦ (hmem j _).2 fun σ hσ ↦ ?_⟩
  rw [map_sub, show e.hom (e.inv z) = z from Iso.inv_hom_id_apply e z]
  refine (Preadditive.comp_sub _ _ _).trans (sub_eq_zero.2 ((Cofan.IsColimit.fac _ _ σ).trans ?_))
  rcases le_total (J σ) j with h | h
  · exact (hagree σ (J σ) (hJ σ) j h).symm
  · exact hagree σ j hσ (J σ) h

/-- **The filtration of singular cochains is complete and separated.** Suppose that every compact
subset of `Y` lies in some `X q`. Then in each degree the filtration of the singular cochains of
`Y` by the cochains vanishing on `X (j - 1)`, `j ∈ ℕ`, is separated, since a singular simplex lies
in some `X q`, and complete: a sequence of cochains whose `j`th and `(j + 1)`st terms agree on
`X (j - 1)` stabilizes on each simplex, and the stable values define its limit. -/
theorem isCompleteFiltration_singularCochainFiltration (hX : Monotone X)
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (m : ℤ) :
    IsCompleteFiltration fun j : ℕ ↦
      LinearMap.range ((singularCochainFiltration R k M X (j - 1)).arrow.f m).hom := by
  have hanti : Antitone fun j : ℕ ↦
      LinearMap.range ((singularCochainFiltration R k M X (j - 1)).arrow.f m).hom :=
    fun _ _ h ↦ Subobject.range_arrow_f_hom_le
      (antitone_singularCochainFiltration_sub_one R k M hX (by lia)) m
  by_cases hm : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = m
  swap
  · -- Outside the degrees of the singular cochains the complex vanishes.
    push Not at hm
    have : Subsingleton (((Y.singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat).X m) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_extend_X _ _ m hm)
    exact ⟨hanti, fun x _ ↦ Subsingleton.elim x 0,
      fun x _ ↦ ⟨0, fun j ↦ by rw [Subsingleton.elim (0 - x j) 0]; exact zero_mem _⟩⟩
  obtain ⟨n, hn⟩ := hm
  refine ⟨hanti, fun x hx ↦ ?_, fun x hx ↦ exists_limit hX hK hn x hx⟩
  -- A cochain vanishing on every `X (j - 1)` vanishes on every simplex.
  let e := extendXIso (Y.singularCochainComplex R k M) ComplexShape.embeddingUpNat hn
  have h0 : e.hom x = 0 := SSet.chainComplex_hom_ext fun σ ↦ by
    obtain ⟨j, hj⟩ := exists_range_subset hX hK σ
    exact ((mem_range_singularCochainFiltration_arrow_iff X _ hn x).1 (hx j) σ hj).trans
      comp_zero.symm
  rw [← Iso.hom_inv_id_apply e x, h0, map_zero]

/-- For `X a ⊆ X b`, the graded piece `F_a / F_b` of the filtration of singular cochains has
vanishing cohomology in degree `m` when the relative singular cohomology `Hⁿ(X b, X a)` vanishes
for `m = n`. In negative degrees `m` there is nothing to check. -/
lemma isZero_homology_cokernel_singularCochainFiltration {a b : ℤ} (hab : X a ⊆ X b) (m : ℤ)
    (hm : ∀ n : ℕ, m = n → IsZero ((TopPair.ofInclusion hab).singularCohomology R k M n)) :
    IsZero ((cokernel (Subobject.ofLE _ _ (singularCochainFiltration_anti R k M hab))).homology
      m) := by
  refine IsZero.of_iso ?_
    ((homologyFunctor _ _ m).mapIso (singularCochainFiltrationCokernelIso R k M hab))
  by_cases hm' : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = m
  · obtain ⟨n, hn⟩ := hm'
    exact (hm n hn.symm).of_iso (extendHomologyIso _ _ hn)
  · push Not at hm'
    exact (extend_exactAt _ _ m hm').isZero_homology

section Convergence

variable (hX : Monotone X) (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (h₀ : X (-1) = ∅)
  (hvanish : ∀ (j : ℤ) (n : ℕ), n < j →
    IsZero ((TopPair.ofInclusion (hX (sub_le_self j zero_le_one))).singularCohomology R k M n))

include h₀ in
private lemma singularCochainFiltration_zero_sub_one :
    singularCochainFiltration R k M X (0 - 1) = ⊤ :=
  singularCochainFiltration_eq_top R k M (by rw [zero_sub, h₀])

include hvanish in
private lemma isZero_homology_cokernel (j : ℤ) (_ : 0 ≤ j) (n : ℤ) (hn : n < j) :
    IsZero ((cokernel (Subobject.ofLE (singularCochainFiltration R k M X (j + 1 - 1))
      (singularCochainFiltration R k M X (j - 1))
      (antitone_singularCochainFiltration_sub_one R k M hX (by lia)))).homology n) :=
  -- The stage `X (j + 1 - 1)` is `X j`.
  (isZero_homology_cokernel_singularCochainFiltration (hX (sub_le_self j zero_le_one)) n
    fun n' hn' ↦ hvanish j n' (by lia)).of_iso ((homologyFunctor _ _ n).mapIso
      (Subobject.cokernelOfLEIsoOfEq (congrArg (singularCochainFiltration R k M X) (by lia))
        rfl _ _))

include hK h₀ hvanish in
/-- **The filtration of the abutment vanishes above the degree.** Suppose that `X (-1)` is empty,
that every compact subset of `Y` lies in some `X q`, and that `Hⁿ(X j, X (j - 1)) = 0` for
`n < j`. Then the piece of the filtration of `Hⁿ(Y)` given by the cochains vanishing on
`X (p - 1)`, indexed by `-p`, vanishes for `n < p`. -/
theorem isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration {p n : ℤ} (hn : n < p) :
    IsZero ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltration (-p) n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration_of_antitone_of_firstQuadrant _
    (antitone_singularCochainFiltration_sub_one R k M hX)
    (singularCochainFiltration_zero_sub_one h₀)
    (isCompleteFiltration_singularCochainFiltration hX hK)
    (isZero_homology_cokernel hX hvanish) hn

/-- **Strong convergence of the cohomology spectral sequence of a filtered space.** Suppose that
`X (-1)` is empty, that every compact subset of `Y` lies in some `X q`, and that the relative
cohomology `Hⁿ(X j, X (j - 1))` vanishes for `n < j`; the family need not reach `Y` at any finite
stage. Then on every page `r ≥ 1` with `p < r` and `q + 1 < r`, the object at `(p, q)` is the
graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the filtration of the abutment `H^{p+q}(Y)`
(`TauCeti.filteredSpaceCohomologyAbutmentIso`), whose `p`th piece, indexed by `-p - 1` in the
spectral object, is the image of the cohomology of the cochains vanishing on `X (p - 1)`. -/
def filteredSpaceCohomologySpectralSequencePageXIsoGraded (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hp : p < r) (hq : q + 1 < r) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page r).X (p, q) ≅
      cokernel ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltrationMap (-p - 1)
        (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFirstQuadrant _
    (antitone_singularCochainFiltration_sub_one R k M hX)
    (singularCochainFiltration_zero_sub_one h₀)
    (isCompleteFiltration_singularCochainFiltration hX hK)
    (isZero_homology_cokernel hX hvanish) r hr p q hp hq

end Convergence

end Complete

end TauCeti
