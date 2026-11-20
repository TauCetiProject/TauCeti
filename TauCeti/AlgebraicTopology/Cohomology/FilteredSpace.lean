/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.CategoryTheory.Subobject.Cokernel
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
  (`TauCeti.filteredSpaceCohomologyAbutmentIso`). When `X a = ∅` and `X b = Y`, the filtration is
  finite and the spectral sequence converges strongly: on late pages the object at `(p, q)` is the
  graded piece `F^p H / F^{p+1} H` of the filtration of `H^{p+q}(Y)` by the images `F^p H` of the
  cohomology of `Y` relative to `X (p - 1)`
  (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFinite`).

Filtering the total space of a fibration by the preimages of the skeleta of the base gives the
cohomology Serre spectral sequence, with `E₁^{p,q} = H^{p+q}(Eₚ, Eₚ₋₁)`. Over an
infinite-dimensional base that filtration is not finite in any degree. Its convergence, through
the completeness of the cochain filtration
(`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete`), is not treated here; neither is
the identification of the first differential with the connecting map of the triple
`(X (p + 1), X p, X (p - 1))` (`TauCeti.TopTriple.singularCohomologyδ`).

This is the cohomological counterpart of `TauCeti.filteredSpaceSpectralSequence`
(`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic`), whose construction it dualises.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex, and Chapter 5, its application to the
  filtration of a total space by the preimages of the skeleta of the base.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

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
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        ((antitone_singularCochainFiltration_sub_one R k M hX).comp
          fun _ _ h ↦ neg_le_neg h))).abutment n ≅
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
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        ((antitone_singularCochainFiltration_sub_one R k M hX).comp
          fun _ _ h ↦ neg_le_neg h))).abutmentFiltrationMap (-p - 1) (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFinite _ _
    (a := b + 1) (b := a + 1)
    (by rw [add_sub_cancel_right]; exact singularCochainFiltration_eq_bot R k M hb)
    (by rw [add_sub_cancel_right]; exact singularCochainFiltration_eq_top R k M ha) r hr p q hra
    (by lia)

end SpectralSequence

end TauCeti
