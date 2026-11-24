/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
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
* **First differential.** The differential `d₁ : E₁^{p,q} ⟶ E₁^{p+1,q}` is the connecting map
  `Hⁿ(X p, X (p - 1)) ⟶ Hⁿ⁺¹(X (p + 1), X p)` of the triple `(X (p + 1), X p, X (p - 1))`
  (`TauCeti.filteredSpaceCohomologySpectralSequence_first_page_d_eq`). This holds because the
  sequence of graded pieces `F^{p+1}/F^{p+2} ⟶ F^p/F^{p+2} ⟶ F^p/F^{p+1}`, whose connecting map is
  the first differential (`CochainComplex.decreasingFiltrationSpectralSequence_first_page_d_eq`),
  is isomorphic to the relative singular cochain sequence of the triple.
* **Convergence.** The abutment in degree `n` is `Hⁿ(Y)`
  (`TauCeti.filteredSpaceCohomologyAbutmentIso`). When `X a = ∅` and `X b = Y`, the filtration is
  finite and the spectral sequence converges strongly: on late pages the object at `(p, q)` is the
  graded piece `F^p H / F^{p+1} H` of the filtration of `H^{p+q}(Y)` by the images `F^p H` of the
  cohomology of `Y` relative to `X (p - 1)`
  (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFinite`).
* **Completeness.** A singular cochain vanishes on `X q` exactly when it vanishes on every singular
  simplex with image in `X q` (`TauCeti.mem_range_singularCochainFiltration_arrow_iff`). If every
  compact subset of `Y` lies in some `X q`, then every singular simplex of `Y` lies in some `X q`,
  so in each degree the filtration is complete and separated
  (`TauCeti.isCompleteFiltration_singularCochainFiltration`): a cochain is the family of its
  restrictions to the simplices (`TauCeti.cochainComponentsLinearEquiv`), and in these coordinates
  the filtration is the weight filtration of a product, the weight of a simplex being the first
  stage containing it. Unlike the filtration of singular chains, the stages
  need not vanish in any degree, as for the skeletal filtration of an infinite-dimensional CW
  complex.
* **Convergence of a complete filtration.** If moreover `X (-1) = ∅` and `Hⁿ(X j, X (j - 1)) = 0`
  whenever `n < j`, the spectral sequence converges strongly: on every page `r ≥ 1` with `p < r`
  and `q + 1 < r` the object at `(p, q)` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the
  filtration of the abutment
  (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFirstQuadrant`). The piece
  `F^p Hⁿ` of this filtration vanishes for `n < p`
  (`TauCeti.isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration`).

* **Naturality.** A map `g : Y ⟶ Y'` carrying each `X q` into the stage `X' q` of a filtration of
  `Y'` pulls back the cochains vanishing on `X' q` to cochains vanishing on `X q`
  (`TauCeti.factors_singularCochainFiltration`), and so induces a morphism from the cohomology
  spectral sequence of `Y'` to that of `Y` (`TauCeti.filteredSpaceCohomologySpectralSequenceMap`),
  contravariantly functorial in `g`. On the first page it is the map
  `Hⁿ(X' p, X' (p - 1)) ⟶ Hⁿ(X p, X (p - 1))` induced by `g`
  (`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso_hom_naturality`), so it is an
  isomorphism from the first page on as soon as `g` induces isomorphisms on the cohomology of the
  steps (`TauCeti.isIso_filteredSpaceCohomologySpectralSequenceMap_hom_f`).

Filtering the total space of a fibration by the preimages of the skeleta of the base gives the
cohomology Serre spectral sequence, with `E₁^{p,q} = H^{p+q}(Eₚ, Eₚ₋₁)` and first differential the
connecting map of three consecutive preimages of skeleta; see
`TauCeti.AlgebraicTopology.Singular.Fibration.Cohomology`.

This is the cohomological counterpart of `TauCeti.filteredSpaceSpectralSequence`
(`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic`), whose construction it dualises.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex, and Chapter 5, its application to the
  filtration of a total space by the preimages of the skeleta of the base.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Theorem 5.5.10 (complete convergence).
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

/-- For `X a ⊆ X b`, the quotient of the cochains relative to `X a` by those relative to `X b` has
vanishing cohomology in degree `m` when the relative singular cohomology `Hⁿ(X b, X a)` vanishes
for `m = n`. In negative degrees there is nothing to check. -/
lemma isZero_homology_cokernel_singularCochainFiltration {a b : ℤ} (hab : X a ⊆ X b) (m : ℤ)
    (hm : ∀ n : ℕ, m = n → IsZero ((TopPair.ofInclusion hab).singularCohomology R k M n)) :
    IsZero ((cokernel (Subobject.ofLE _ _ (singularCochainFiltration_anti R k M hab))).homology
      m) := by
  refine IsZero.of_iso ?_ ((homologyFunctor (ModuleCat.{v} k) _ m).mapIso
    (singularCochainFiltrationCokernelIso R k M hab))
  by_cases hm' : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = m
  · obtain ⟨n, hn⟩ := hm'
    exact (hm n hn.symm).of_iso (extendHomologyIso _ _ hn)
  · push Not at hm'
    exact (extend_exactAt _ _ m hm').isZero_homology

section Membership

variable {R k M}

/-- **A cochain vanishes on `X q` exactly when it lies in the stage of the filtration at `q`.** A
singular cochain `c` of degree `m` of `Y`, read in degree `n = m` of the extended complex, lies in
the cochains relative to `X q` exactly when `c` vanishes on every singular `m`-simplex of `Y` with
image in `X q`. -/
theorem mem_range_singularCochainFiltration_arrow_iff (q : ℤ) {m : ℕ} {n : ℤ}
    (hn : ComplexShape.embeddingUpNat.f m = n)
    (c : ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X n) :
    c ∈ LinearMap.range ((singularCochainFiltration R k M X q).arrow.f n).hom ↔
      ∀ σ : (TopCat.toSSet.obj Y) _⦋m⦌, Set.range (Y.toSSetObjEquiv _ σ) ⊆ X q →
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫
          ((Y.singularCochainComplex R k M).extendXIso _ hn).hom c = 0 := by
  rw [← singularCochainFiltrationIso_hom_comp_singularCochainFiltrationι, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _ (ModuleCat.range_eq_top_of_epi _),
    singularCochainFiltrationι_def]
  refine (HomologicalComplex.mem_range_extendMap_f_iff _ _ hn c).trans ?_
  have h := TopPair.mem_range_linearYonedaFunctor_map_singularChainComplexπ_f_iff
    (TopPair.ofSubset (X q)) R k M m (((Y.singularCochainComplex R k M).extendXIso _ hn).hom c)
  rwa [TopPair.range_ofSubset_map] at h

end Membership

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

/-- **The spectral object of the cohomology spectral sequence of a filtered space**, for an
increasing family `X : ℤ → Set Y` of subsets of `Y`. Its abutment in degree `n` is `Hⁿ(Y)`
(`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by the images of the relative cohomology
of the pairs `(Y, X (p - 1))`; the piece `F^p` sits at index `-p`. -/
abbrev filteredSpaceCohomologySpectralObject :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
    ((antitone_singularCochainFiltration_sub_one R k M hX).comp fun _ _ h ↦ neg_le_neg h))

/-- The graded piece `F^p / F^{p+1}` of the cochains of a filtered space, the cochains vanishing on
`X (p - 1)` modulo those vanishing on `X p`, is the relative singular cochain complex of
`(X b, X a)`, reindexed along `ℕ ⊆ ℤ`, for `a = p - 1` and `b = p`. -/
def singularCochainFiltrationGradedIso (p a b : ℤ) (ha : a = p - 1) (hb : b = p) :
    cokernel (Subobject.ofLE (singularCochainFiltration R k M X (p + 1 - 1))
        (singularCochainFiltration R k M X (p - 1))
        (antitone_singularCochainFiltration_sub_one R k M hX (by lia))) ≅
      ((TopPair.ofInclusion (hX (by lia : a ≤ b))).singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat :=
  Subobject.cokernelOfLEIsoOfEq (by rw [hb, add_sub_cancel_right]) (by rw [ha]) _
      (singularCochainFiltration_anti R k M (hX (by lia : a ≤ b))) ≪≫
    singularCochainFiltrationCokernelIso R k M (hX (by lia : a ≤ b))

/-- The identification `TauCeti.singularCochainFiltrationGradedIso` of the graded piece
`F^p / F^{p+1}` of the cochains of a filtered space with the relative cochains of `(X b, X a)` is
the restriction of the cochains relative to `X (p - 1) = X a`. -/
@[reassoc (attr := simp)]
lemma π_singularCochainFiltrationGradedIso_hom (p a b : ℤ) (ha : a = p - 1) (hb : b = p) :
    cokernel.π _ ≫ (singularCochainFiltrationGradedIso R k M hX p a b ha hb).hom =
      Subobject.ofLE _ _ (by rw [ha]) ≫ (singularCochainFiltrationIso R k M X a).hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (TopTriple.innerToTotal.app (TopTriple.ofSubset (hX (by lia : a ≤ b)))))
          ComplexShape.embeddingUpNat := by
  simp only [singularCochainFiltrationGradedIso, Iso.trans_hom,
    Subobject.π_cokernelOfLEIsoOfEq_hom_assoc, π_singularCochainFiltrationCokernelIso_hom]
  -- The composite of `TauCeti.π_singularCochainFiltrationCokernelIso_hom` ends in the cochains of
  -- a pair of the triple, which is the pair `(X b, X a)` of the statement only after unfolding.
  rfl

/-- The object at `(p, q)` on the first page is the cohomology in degree `p + q` of the reindexed
relative singular cochains of `(X b, X a)`, for `a = p - 1` and `b = p`. -/
private def firstPageXIsoExtend (p q a b : ℤ) (ha : a = p - 1) (hb : b = p) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q) ≅
      (((TopPair.ofInclusion (hX (by lia : a ≤ b))).singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat).homology (p + q) :=
  CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
    (homologyFunctor _ _ (p + q)).mapIso (singularCochainFiltrationGradedIso R k M hX p a b ha hb)

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

/-- `TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso` is the identification of the
first page of a decreasing filtration with the cohomology of its graded pieces, followed by the
identification of the graded piece `F^p / F^{p+1}` with the reindexed relative cochains of
`(X b, X a)` and by `HomologicalComplex.extendHomologyIso`. -/
lemma filteredSpaceCohomologySpectralSequenceFirstPageXIso_hom (p q a b : ℤ) (ha : a = p - 1)
    (hb : b = p) (n : ℕ) (hn : p + q = n) :
    (filteredSpaceCohomologySpectralSequenceFirstPageXIso R k M hX p q a b ha hb n hn).hom =
      (CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _
          (antitone_singularCochainFiltration_sub_one R k M hX) p q).hom ≫
        HomologicalComplex.homologyMap
          (singularCochainFiltrationGradedIso R k M hX p a b ha hb).hom (p + q) ≫
        (extendHomologyIso _ ComplexShape.embeddingUpNat hn.symm).hom :=
  (rfl)

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
      cokernel ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltrationMap
        (-p - 1) (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFinite _ _
    (a := b + 1) (b := a + 1)
    (by rw [add_sub_cancel_right]; exact singularCochainFiltration_eq_bot R k M hb)
    (by rw [add_sub_cancel_right]; exact singularCochainFiltration_eq_top R k M ha) r hr p q hra
    (by lia)

/-! ### Completeness and convergence -/

variable {R k M}

include hX in
/-- **The filtration of singular cochains is complete and separated.** If every compact subset of
`Y` lies in some `X q`, then in each degree the stages of the filtration of the singular cochains
by vanishing on `X (j - a)`, `j : ℕ`, form a complete separated filtration, for every offset `a`.
A cochain is the family of its restrictions to the singular simplices
(`TauCeti.cochainComponentsLinearEquiv`), and in these coordinates the filtration is the weight
filtration of a product (`TauCeti.isCompleteFiltration_pi`), the weight of a simplex being the
first stage containing it; a singular simplex has compact image, so it has a weight. -/
theorem isCompleteFiltration_singularCochainFiltration
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (a n : ℤ) :
    IsCompleteFiltration fun j : ℕ ↦
      LinearMap.range ((singularCochainFiltration R k M X (j - a)).arrow.f n).hom := by
  classical
  by_cases hn : ∃ m : ℕ, ComplexShape.embeddingUpNat.f m = n
  swap
  · -- Below degree `0` the extended cochain complex vanishes.
    push Not at hn
    have : Subsingleton (((Y.singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat).X n) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_extend_X _ _ n hn)
    exact
      { antitone _ _ _ x _ := by rw [Subsingleton.elim x 0]; exact zero_mem _
        eq_zero_of_forall_mem x _ := Subsingleton.elim x 0
        exists_limit x _ := ⟨0, fun j ↦ by rw [Subsingleton.elim (0 - x j) 0]; exact zero_mem _⟩ }
  obtain ⟨m, hm⟩ := hn
  -- A singular simplex has compact image, so it lies in some stage `X (j - a)`.
  have hσ (σ : (TopCat.toSSet.obj Y) _⦋m⦌) :
      ∃ j : ℕ, Set.range (Y.toSSetObjEquiv _ σ) ⊆ X (j - a) := by
    obtain ⟨q, hq⟩ := hK _ (isCompact_range (Y.toSSetObjEquiv _ σ).continuous)
    exact ⟨(q + a).toNat, hq.trans (hX (by lia))⟩
  -- In the coordinates given by the simplices, the filtration is a weight filtration of a
  -- product, with the weight of a simplex the first stage containing it.
  let G : ℕ → Submodule k ((TopCat.toSSet.obj Y) _⦋m⦌ → (R ⟶ M)) := fun j ↦
    ⨅ (σ) (_ : Nat.find (hσ σ) < j), LinearMap.ker (LinearMap.proj σ)
  have hG := isCompleteFiltration_pi (fun σ ↦ Nat.find (hσ σ)) G fun j v ↦ by simp [G]
  convert ((hG.comp_add_right 1).comap_linearEquiv
    (cochainComponentsLinearEquiv k (TopCat.toSSet.obj Y) R M m)).comap_linearEquiv
      ((Y.singularCochainComplex R k M).extendXIso _ hm).toLinearEquiv using 1
  funext j
  ext x
  rw [mem_range_singularCochainFiltration_arrow_iff _ hm]
  simp only [G, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker]
  -- A simplex lies in `X (j - a)` exactly when its weight is at most `j`; the coordinates of a
  -- cochain are its restrictions to the summands of the simplices.
  -- `Iso.toLinearMap_toLinearEquiv` unwraps the coordinate equivalence; the two sides then
  -- differ only in the instances of the coercion to functions, closed by `rfl`.
  refine forall_congr' fun σ ↦ imp_congr ?_ (by
    rw [LinearMap.proj_apply, LinearEquiv.coe_coe, cochainComponentsLinearEquiv_apply,
      Iso.toLinearMap_toLinearEquiv]; rfl)
  rw [Nat.lt_succ_iff, Nat.find_le_iff]
  exact ⟨fun h ↦ ⟨j, le_rfl, h⟩, fun ⟨i, hi, h⟩ ↦ h.trans (hX (by lia))⟩

/-- The graded pieces `F^j / F^{j+1}` of the filtration of singular cochains have vanishing
cohomology in degree `m` when `Hⁿ(X j, X (j - 1))` vanishes for `m = n`. -/
private lemma isZero_homology_filtrationCokernel (j m : ℤ)
    (h : ∀ n : ℕ, m = n →
      IsZero ((TopPair.ofInclusion (hX (by lia : j - 1 ≤ j))).singularCohomology R k M n)) :
    IsZero ((cokernel (Subobject.ofLE (singularCochainFiltration R k M X (j + 1 - 1))
      (singularCochainFiltration R k M X (j - 1))
      (antitone_singularCochainFiltration_sub_one R k M hX (by lia)))).homology m) :=
  (isZero_homology_cokernel_singularCochainFiltration R k M _ m h).of_iso
    ((homologyFunctor (ModuleCat.{v} k) _ m).mapIso
      (Subobject.cokernelOfLEIsoOfEq (by rw [add_sub_cancel_right]) rfl _ _))

include hX in
/-- **The filtration of the abutment vanishes above the degree.** Suppose that every compact
subset of `Y` lies in some `X q` and that `Hⁿ(X j, X (j - 1)) = 0` whenever `n < j`. Then the piece
`F^p Hⁿ(Y)` of the induced filtration of the abutment, the image of `Hⁿ(Y, X (p - 1))`, vanishes
for `n < p`. -/
theorem isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q)
    (hvanish : ∀ (j : ℤ) (n : ℕ), n < j →
      IsZero ((TopPair.ofInclusion (hX (by lia : j - 1 ≤ j))).singularCohomology R k M n))
    {p n : ℤ} (hn : n < p) :
    IsZero ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltration (-p) n) := by
  refine Abelian.SpectralObject.isZero_abutmentFiltration _
    (CochainComplex.isZero_spectralObject_H_bot _ _ (-p) n ?_)
  rw [Function.comp_apply, neg_neg]
  rcases lt_or_ge n 0 with hn₀ | hn₀
  · -- In negative degrees the extended cochains, and so their subcomplexes, vanish.
    refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (HomologicalComplex.ExactAt.of_isZero (IsZero.of_mono
        ((singularCochainFiltration R k M X (p - 1)).arrow.f n)
        (isZero_extend_X _ _ n fun m hm ↦ ?_)))
    have : (m : ℤ) = n := hm
    lia
  · -- Above degree `n` the graded pieces have no cohomology in degree `n`, and the stages from
    -- `p ≥ 0` on form a complete filtration.
    obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ p)
    exact CochainComplex.isZero_homology_of_antitone_of_isCompleteFiltration _
      (antitone_singularCochainFiltration_sub_one R k M hX)
      (by
        convert (isCompleteFiltration_singularCochainFiltration hX hK 1 (n - 1)).comp_add_right p'
          using 2
        push_cast
        rw [add_comm])
      (fun x hx ↦ (isCompleteFiltration_singularCochainFiltration hX hK 1 n).eq_zero_of_forall_mem
        x fun j ↦ hx j)
      fun j hj ↦ isZero_homology_filtrationCokernel hX j n fun m hm ↦ hvanish j m (by lia)

/-- **Strong convergence of the cohomology spectral sequence of a complete filtration of a
space.** Suppose that every compact subset of `Y` lies in some `X q`, that `X (-1) = ∅`, and that
`Hⁿ(X j, X (j - 1)) = 0` whenever `n < j`, so that the first page is concentrated in the first
quadrant. Then on every page `r ≥ 1` with `p < r` and `q + 1 < r`, the object at `(p, q)` is the
graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the induced filtration of the abutment
`H^{p+q}(Y)` (`TauCeti.filteredSpaceCohomologyAbutmentIso`). The stages of the filtration of the
cochains need not vanish in any degree. -/
def filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFirstQuadrant
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (h₀ : X (-1) = ∅)
    (hvanish : ∀ (j : ℤ) (n : ℕ), n < j →
      IsZero ((TopPair.ofInclusion (hX (by lia : j - 1 ≤ j))).singularCohomology R k M n))
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hp : p < r) (hq : q + 1 < r) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page r).X (p, q) ≅
      cokernel ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltrationMap
        (-p - 1) (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFirstQuadrant
    (fun p ↦ singularCochainFiltration R k M X (p - 1))
    (antitone_singularCochainFiltration_sub_one R k M hX)
    (singularCochainFiltration_eq_top R k M (by rwa [zero_sub]))
    (isCompleteFiltration_singularCochainFiltration hX hK 1)
    (fun j _ m hm ↦ isZero_homology_filtrationCokernel hX j m fun n hn ↦ hvanish j n (by lia))
    r hr p q hp hq

end SpectralSequence

section FirstDifferential

variable {a b c : ℤ} (hab : X a ⊆ X b) (hbc : X b ⊆ X c)

/-- Restricting cochains from `(Y, X b)` to `(X c, X b)` and then to `(X c, X a)` is restricting
them to `(Y, X a)` and then to `(X c, X a)`. -/
private lemma extendMap_innerToTotal_comp_extendMap_totalToOuter :
    extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.innerToTotal.app (TopTriple.ofSubset hbc))) ComplexShape.embeddingUpNat ≫
      extendMap (TopPair.singularCochainComplexMap
        (TopTriple.totalToOuter.app (TopTriple.ofInclusions hab hbc))) ComplexShape.embeddingUpNat =
    extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.totalToOuter.app (TopTriple.ofSubset hab))) ComplexShape.embeddingUpNat ≫
      extendMap (TopPair.singularCochainComplexMap
        (TopTriple.innerToTotal.app (TopTriple.ofSubset (hab.trans hbc))))
        ComplexShape.embeddingUpNat := by
  -- Both composites are induced by the inclusion `(X c, X a) ⟶ (Y, X b)`. The pairs of the triples
  -- agree only up to definitional unfolding, so the composites are formed with `exact`.
  have h : TopTriple.totalToOuter.app (TopTriple.ofInclusions hab hbc) ≫
        TopTriple.innerToTotal.app (TopTriple.ofSubset hbc) =
      TopTriple.innerToTotal.app (TopTriple.ofSubset (hab.trans hbc)) ≫
        TopTriple.totalToOuter.app (TopTriple.ofSubset hab) := by
    ext : 2 <;> rfl
  exact (extendMap_comp _ _ _).symm.trans <| (congrArg (extendMap · _) <|
    (TopPair.singularCochainComplexMap_comp _ _).symm.trans <|
      (congrArg (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)) h).trans
        (TopPair.singularCochainComplexMap_comp _ _)).trans (extendMap_comp _ _ _)

/-- Restricting cochains from `(Y, X a)` to `(X c, X a)` and then to `(X b, X a)` is restricting
them to `(X b, X a)`. -/
private lemma extendMap_innerToTotal_comp_extendMap_innerToTotal :
    extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.innerToTotal.app (TopTriple.ofSubset (hab.trans hbc))))
        ComplexShape.embeddingUpNat ≫
      extendMap (TopPair.singularCochainComplexMap
        (TopTriple.innerToTotal.app (TopTriple.ofInclusions hab hbc))) ComplexShape.embeddingUpNat =
    extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.innerToTotal.app (TopTriple.ofSubset hab))) ComplexShape.embeddingUpNat := by
  -- As above, the composite is formed with `exact`.
  have h : TopTriple.innerToTotal.app (TopTriple.ofInclusions hab hbc) ≫
        TopTriple.innerToTotal.app (TopTriple.ofSubset (hab.trans hbc)) =
      TopTriple.innerToTotal.app (TopTriple.ofSubset hab) := by
    ext : 2 <;> rfl
  exact (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) <|
    (TopPair.singularCochainComplexMap_comp _ _).symm.trans
      (congrArg (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)) h)

variable {hab hbc} in
/-- On the quotient `C*(Y, X b)/C*(Y, X c)`, identified with the cochains of `(X c, X b)`, the
restriction to `(X c, X a)` is induced by the inclusion `C*(Y, X b) ⊆ C*(Y, X a)`. -/
private lemma cokernelOfLEIsoOfEq_trans_hom_comp_extendMap_totalToOuter
    (hAB : singularCochainFiltration R k M X c ≤ singularCochainFiltration R k M X b)
    (hBD : singularCochainFiltration R k M X b ≤ singularCochainFiltration R k M X a) :
    (Subobject.cokernelOfLEIsoOfEq rfl rfl hAB (singularCochainFiltration_anti R k M hbc) ≪≫
        singularCochainFiltrationCokernelIso R k M hbc).hom ≫
      extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.totalToOuter.app (TopTriple.ofInclusions hab hbc)))
        ComplexShape.embeddingUpNat =
    cokernel.map (Subobject.ofLE _ _ hAB) (Subobject.ofLE _ _ hAB ≫ Subobject.ofLE _ _ hBD)
        (𝟙 _) (Subobject.ofLE _ _ hBD) (by simp) ≫
      (cokernelIsoOfEq (Subobject.ofLE_comp_ofLE _ _ _ hAB hBD) ≪≫
        singularCochainFiltrationCokernelIso R k M (hab.trans hbc)).hom := by
  apply coequalizer.hom_ext
  simp only [TopTriple.totalPair_obj_ofInclusions, coequalizer_as_cokernel, Iso.trans_hom,
    TopTriple.outerPair_obj_ofInclusions, Category.assoc, Subobject.π_cokernelOfLEIsoOfEq_hom_assoc,
    Subobject.ofLE_refl, π_singularCochainFiltrationCokernelIso_hom_assoc, Category.id_comp,
    cokernel.π_desc_assoc, π_comp_cokernelIsoOfEq_hom_assoc,
    π_singularCochainFiltrationCokernelIso_hom]
  -- The composites pass through pairs of different triples, which agree only up to definitional
  -- unfolding, so they are reassociated by hand.
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
    (extendMap_innerToTotal_comp_extendMap_totalToOuter _ _ _ hab hbc)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
        (ofLE_comp_singularCochainFiltrationIso_hom R k M hab).symm).trans (Category.assoc _ _ _)

variable {hab hbc} in
/-- On the quotient `C*(Y, X a)/C*(Y, X c)`, identified with the cochains of `(X c, X a)`, the
restriction to `(X b, X a)` is the projection to `C*(Y, X a)/C*(Y, X b)`. -/
private lemma cokernelIsoOfEq_trans_hom_comp_extendMap_innerToTotal
    (hAB : singularCochainFiltration R k M X c ≤ singularCochainFiltration R k M X b)
    (hBD : singularCochainFiltration R k M X b ≤ singularCochainFiltration R k M X a) :
    (cokernelIsoOfEq (Subobject.ofLE_comp_ofLE _ _ _ hAB hBD) ≪≫
        singularCochainFiltrationCokernelIso R k M (hab.trans hbc)).hom ≫
      extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.innerToTotal.app (TopTriple.ofInclusions hab hbc)))
        ComplexShape.embeddingUpNat =
    cokernel.map (Subobject.ofLE _ _ hAB ≫ Subobject.ofLE _ _ hBD) (Subobject.ofLE _ _ hBD)
        (Subobject.ofLE _ _ hAB) (𝟙 _) (by simp) ≫
      (Subobject.cokernelOfLEIsoOfEq rfl rfl hBD (singularCochainFiltration_anti R k M hab) ≪≫
        singularCochainFiltrationCokernelIso R k M hab).hom := by
  apply coequalizer.hom_ext
  simp only [TopTriple.innerPair_obj_ofInclusions, coequalizer_as_cokernel, Iso.trans_hom,
    TopTriple.totalPair_obj_ofInclusions, Category.assoc, π_comp_cokernelIsoOfEq_hom_assoc,
    π_singularCochainFiltrationCokernelIso_hom_assoc, cokernel.π_desc_assoc, Category.id_comp,
    Subobject.π_cokernelOfLEIsoOfEq_hom_assoc, Subobject.ofLE_refl,
    π_singularCochainFiltrationCokernelIso_hom]
  -- As above, the composite is reassociated by hand.
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
    (extendMap_innerToTotal_comp_extendMap_innerToTotal _ _ _ hab hbc)).trans
      (Category.id_comp _).symm

/-- For `X a ⊆ X b ⊆ X c` and subobjects `A ≤ B ≤ D` equal to the cochains vanishing on `X c`,
`X b` and `X a`, the connecting map of the sequence `B/A ⟶ D/A ⟶ D/B` is the connecting map of the
cochain sequence of the triple `(X c, X b, X a)`, under the identifications of the quotients with
relative cochains. -/
private lemma δ_comp_homologyMap_cokernelOfLEIsoOfEq_trans_hom
    {A B D : Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat)}
    (hA : A = singularCochainFiltration R k M X c) (hB : B = singularCochainFiltration R k M X b)
    (hD : D = singularCochainFiltration R k M X a) (hAB : A ≤ B) (hBD : B ≤ D) (n₀ n₁ : ℤ)
    (h : (ComplexShape.up ℤ).Rel n₀ n₁) :
    (cokernelCompSequence_shortExact (Subobject.ofLE A B hAB)
        (Subobject.ofLE B D hBD)).δ n₀ n₁ h ≫
      HomologicalComplex.homologyMap (Subobject.cokernelOfLEIsoOfEq hA hB hAB
        (singularCochainFiltration_anti R k M hbc) ≪≫
          singularCochainFiltrationCokernelIso R k M hbc).hom n₁ =
    HomologicalComplex.homologyMap (Subobject.cokernelOfLEIsoOfEq hB hD hBD
        (singularCochainFiltration_anti R k M hab) ≪≫
          singularCochainFiltrationCokernelIso R k M hab).hom n₀ ≫
      (((TopTriple.ofInclusions hab hbc).shortExact_singularCochainComplexShortComplex R k M).extend
        ComplexShape.embeddingUpNat).δ n₀ n₁ h := by
  subst hA hB hD
  -- The morphism from the sequence of graded pieces to the extended cochain sequence of the
  -- triple, given by the identifications of the graded pieces with relative cochains. The squares
  -- are read in the extended sequence, whose objects are the reindexed relative cochain complexes
  -- only after unfolding `extendFunctor`.
  let ψ : cokernelCompSequence (Subobject.ofLE _ _ hAB) (Subobject.ofLE _ _ hBD) ⟶
      ((TopTriple.ofInclusions hab hbc).singularCochainComplexShortComplex R k M).map
        (ComplexShape.embeddingUpNat.extendFunctor _) :=
    { τ₁ := (Subobject.cokernelOfLEIsoOfEq rfl rfl hAB _ ≪≫
        singularCochainFiltrationCokernelIso R k M hbc).hom
      τ₂ := (cokernelIsoOfEq (Subobject.ofLE_comp_ofLE _ _ _ hAB hBD) ≪≫
        singularCochainFiltrationCokernelIso R k M (hab.trans hbc)).hom
      τ₃ := (Subobject.cokernelOfLEIsoOfEq rfl rfl hBD _ ≪≫
        singularCochainFiltrationCokernelIso R k M hab).hom
      comm₁₂ := cokernelOfLEIsoOfEq_trans_hom_comp_extendMap_totalToOuter R k M hAB hBD
      comm₂₃ := cokernelIsoOfEq_trans_hom_comp_extendMap_innerToTotal R k M hAB hBD }
  exact HomologicalComplex.HomologySequence.δ_naturality ψ (cokernelCompSequence_shortExact _ _)
    (((TopTriple.ofInclusions hab hbc).shortExact_singularCochainComplexShortComplex R k M).extend
      ComplexShape.embeddingUpNat) n₀ n₁ h

variable (hX : Monotone X)

/-- **The first differential of the cohomology spectral sequence of a filtered space.** Under the
identifications of the first page with relative singular cohomology, the differential
`d₁ : E₁^{p,q} ⟶ E₁^{p+1,q}` is the connecting map `Hⁿ(X p, X (p - 1)) ⟶ Hⁿ⁺¹(X (p + 1), X p)` of
the triple `(X (p + 1), X p, X (p - 1))`, where `p + q = n`. -/
theorem filteredSpaceCohomologySpectralSequence_first_page_d_eq (p q : ℤ) (n : ℕ)
    (hn : p + q = n) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page 1).d (p, q) (p + 1, q) =
      (filteredSpaceCohomologySpectralSequenceFirstPageXIso R k M hX p q (p - 1) p rfl rfl n
          hn).hom ≫
        (TopTriple.ofInclusions (hX (by lia : p - 1 ≤ p))
          (hX (by lia : p ≤ p + 1))).singularCohomologyδ R k M n (n + 1) ≫
        (filteredSpaceCohomologySpectralSequenceFirstPageXIso R k M hX (p + 1) q p (p + 1)
          (by lia) rfl (n + 1) (by push_cast; lia)).inv := by
  -- The first differential is the connecting map of the quotients of the stages of the filtration
  -- (`CochainComplex.decreasingFiltrationSpectralSequence_first_page_d_eq`). It is that of the
  -- extended cochain sequence of the triple, which is the connecting map of the triple.
  have key := δ_comp_homologyMap_cokernelOfLEIsoOfEq_trans_hom R k M (hX (by lia : p - 1 ≤ p))
    (hX (by lia : p ≤ p + 1)) (A := singularCochainFiltration R k M X (p + 1 + 1 - 1))
    (B := singularCochainFiltration R k M X (p + 1 - 1)) (by rw [add_sub_cancel_right])
    (by rw [add_sub_cancel_right]) rfl
    (antitone_singularCochainFiltration_sub_one R k M hX (by lia))
    (antitone_singularCochainFiltration_sub_one R k M hX (by lia)) (p + q) (p + 1 + q)
    (by simp only [ComplexShape.up_Rel]; lia)
  have hext := ShortComplex.ShortExact.extend_δ_comp_extendHomologyIso_hom
    (TopTriple.shortExact_singularCochainComplexShortComplex
      (TopTriple.ofInclusions (hX (by lia : p - 1 ≤ p)) (hX (by lia : p ≤ p + 1))) R k M)
    ComplexShape.embeddingUpNat (i := n) (j := n + 1) (i' := p + q) (j' := p + 1 + q) (by simp)
    hn.symm (by rw [ComplexShape.embeddingUpNat_f]; push_cast; lia)
    (by simp only [ComplexShape.up_Rel]; lia)
  rw [CochainComplex.decreasingFiltrationSpectralSequence_first_page_d_eq,
    (Iso.eq_comp_inv (HomologicalComplex.homologyMapIso _ (p + 1 + q))).2 key,
    (Iso.eq_comp_inv (HomologicalComplex.extendHomologyIso _ _ _)).2 hext,
    filteredSpaceCohomologySpectralSequenceFirstPageXIso,
    filteredSpaceCohomologySpectralSequenceFirstPageXIso, firstPageXIsoExtend, firstPageXIsoExtend]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    HomologicalComplex.homologyFunctor_map, Category.assoc]
  -- The left-hand side is reassociated by hand: its composites pass through the objects of the
  -- extended cochain sequence of the triple, which agree with those of the right-hand side only
  -- after unfolding, so `simp` cannot reach them.
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (Category.assoc _ _ _)))))

end FirstDifferential

section Naturality

variable {Y' Y'' : TopCat.{w}} {X' : ℤ → Set Y'} {X'' : ℤ → Set Y''} (g : Y ⟶ Y')
  (hg : ∀ q, Set.MapsTo g (X q) (X' q))

/-- Pulling back singular cochains along a map `g : Y ⟶ Y'` carrying `X q` into `X' q` restricts
to the cochains relative to `X' q` and `X q`: there it is the cochain map induced by the map of
pairs `(Y, X q) ⟶ (Y', X' q)`. -/
@[reassoc]
lemma singularCochainFiltrationι_comp_extendMap_singularCochainComplexMap (q : ℤ) :
    singularCochainFiltrationι R k M X' q ≫
        extendMap (TopCat.singularCochainComplexMap g) ComplexShape.embeddingUpNat =
      extendMap (TopPair.singularCochainComplexMap (TopPair.ofSubsetMap g (hg q)))
          ComplexShape.embeddingUpNat ≫ singularCochainFiltrationι R k M X q := by
  -- Apply `Hom(-, M)` to the naturality of the quotient maps to relative chains. The cochain
  -- complexes of the pairs agree with those of the composites only up to unfolding, so the
  -- equations are composed as terms.
  have h := ((TauCeti.ChainComplex.linearYonedaFunctor k M).map_comp
      ((TopPair.ofSubset (X' q)).singularChainComplexπ R).op
      (SSet.chainComplexMap (TopCat.toSSet.map g) R).op).symm.trans <|
    (congrArg (fun φ ↦ (TauCeti.ChainComplex.linearYonedaFunctor k M).map φ.op)
      (TopPair.singularChainComplexπ_ofSubsetMap_naturality g (hg q) R)).trans <|
    (TauCeti.ChainComplex.linearYonedaFunctor k M).map_comp
      (TopPair.singularChainComplexMap (TopPair.ofSubsetMap g (hg q)) R).op
      ((TopPair.ofSubset (X q)).singularChainComplexπ R).op
  rw [singularCochainFiltrationι_def, singularCochainFiltrationι_def]
  exact (extendMap_comp _ _ _).symm.trans
    ((congrArg (extendMap · ComplexShape.embeddingUpNat) h).trans (extendMap_comp _ _ _))

include hg in
/-- **Pulling back cochains respects the filtrations.** A cochain of `Y'` vanishing on `X' q`
pulls back along a map `g : Y ⟶ Y'` carrying `X q` into `X' q` to a cochain of `Y` vanishing on
`X q`. -/
lemma factors_singularCochainFiltration (q : ℤ) :
    (singularCochainFiltration R k M X q).Factors ((singularCochainFiltration R k M X' q).arrow ≫
      extendMap (TopCat.singularCochainComplexMap g) ComplexShape.embeddingUpNat) := by
  rw [← singularCochainFiltrationIso_hom_comp_singularCochainFiltrationι, Category.assoc,
    singularCochainFiltrationι_comp_extendMap_singularCochainComplexMap R k M g hg q,
    ← Category.assoc]
  exact Subobject.factors_of_factors_right _ (Subobject.mk_factors_self _)

variable (hX : Monotone X) (hX' : Monotone X') (hX'' : Monotone X'')

include hX hX' g hg in
/-- **The morphism of cohomology spectral sequences induced by a map of filtered spaces.** A
continuous map `g : Y ⟶ Y'` carrying each `X q` into `X' q` pulls back the cochains of `Y'`
vanishing on `X' (p - 1)` to cochains of `Y` vanishing on `X (p - 1)`, and so induces a morphism
from the cohomology spectral sequence of the filtration of `Y'` by the `X' q` to that of the
filtration of `Y` by the `X q`. On the first page it is the map induced by `g` on the relative
singular cohomology of the steps
(`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso_hom_naturality`). -/
def filteredSpaceCohomologySpectralSequenceMap :
    filteredSpaceCohomologySpectralSequence R k M hX' ⟶
      filteredSpaceCohomologySpectralSequence R k M hX :=
  CochainComplex.decreasingFiltrationSpectralSequenceMap _ _
    (extendMap (TopCat.singularCochainComplexMap g) ComplexShape.embeddingUpNat)
    fun p ↦ factors_singularCochainFiltration R k M g hg (p - 1)

/-- The identity of a filtered space induces the identity of its cohomology spectral sequence. -/
@[simp]
lemma filteredSpaceCohomologySpectralSequenceMap_id
    (h : ∀ q, Set.MapsTo (𝟙 Y : Y ⟶ Y) (X q) (X q)) :
    filteredSpaceCohomologySpectralSequenceMap R k M (𝟙 Y) h hX hX = 𝟙 _ := by
  -- The pullback along the identity is the identity of the cochains.
  have e : extendMap (TopCat.singularCochainComplexMap (R := R) (k := k) (M := M) (𝟙 Y))
      ComplexShape.embeddingUpNat = 𝟙 _ := by
    rw [TopCat.singularCochainComplexMap_id, extendMap_id]
  rw [filteredSpaceCohomologySpectralSequenceMap,
    CochainComplex.decreasingFiltrationSpectralSequenceMap_congr e,
    CochainComplex.decreasingFiltrationSpectralSequenceMap_id]

/-- A composite of maps of filtered spaces induces the composite of the morphisms of cohomology
spectral sequences, in the opposite order. -/
@[reassoc]
lemma filteredSpaceCohomologySpectralSequenceMap_comp (g' : Y' ⟶ Y'')
    (hg' : ∀ q, Set.MapsTo g' (X' q) (X'' q)) (hgg' : ∀ q, Set.MapsTo (g ≫ g') (X q) (X'' q)) :
    filteredSpaceCohomologySpectralSequenceMap R k M (g ≫ g') hgg' hX hX'' =
      filteredSpaceCohomologySpectralSequenceMap R k M g' hg' hX' hX'' ≫
        filteredSpaceCohomologySpectralSequenceMap R k M g hg hX hX' := by
  -- Pulling back along `g ≫ g'` is pulling back along `g'` and then along `g`.
  have e : extendMap (TopCat.singularCochainComplexMap (R := R) (k := k) (M := M) (g ≫ g'))
      ComplexShape.embeddingUpNat = extendMap (TopCat.singularCochainComplexMap g')
        ComplexShape.embeddingUpNat ≫
      extendMap (TopCat.singularCochainComplexMap g) ComplexShape.embeddingUpNat := by
    rw [TopCat.singularCochainComplexMap_comp, extendMap_comp]
  rw [filteredSpaceCohomologySpectralSequenceMap, filteredSpaceCohomologySpectralSequenceMap,
    filteredSpaceCohomologySpectralSequenceMap,
    CochainComplex.decreasingFiltrationSpectralSequenceMap_congr e,
    CochainComplex.decreasingFiltrationSpectralSequenceMap_comp]

/-- The map of pairs `(X b, X a) ⟶ (Y', X' a)` through `(Y, X a)` agrees with the map through
`(X' b, X' a)`: both are `g` on the ambient spaces. -/
private lemma innerToTotal_comp_ofSubsetMap {a b : ℤ} (hab : a ≤ b) :
    TopTriple.innerToTotal.app (TopTriple.ofSubset (hX hab)) ≫ TopPair.ofSubsetMap g (hg a) =
      filteredSpaceStepMap hX hX' g hg hab ≫
        TopTriple.innerToTotal.app (TopTriple.ofSubset (hX' hab)) := by
  refine TopPair.hom_ext_of_fst _ ?_
  ext x
  exact (TopPair.ofSubsetMap_fst_apply g (hg a) _).trans
    (filteredSpaceStepMap_fst_apply hX hX' g hg hab x).symm

/-- On the stage `F^p`, the cochains pulled back along `g` are those induced by the map of pairs
`(Y, X (p - 1)) ⟶ (Y', X' (p - 1))`, under the identifications of the stages with relative
cochains. -/
@[reassoc]
private lemma factorThru_comp_singularCochainFiltrationIso_hom (q : ℤ) :
    (singularCochainFiltration R k M X q).factorThru _
        (factors_singularCochainFiltration R k M g hg q) ≫
        (singularCochainFiltrationIso R k M X q).hom =
      (singularCochainFiltrationIso R k M X' q).hom ≫
        extendMap (TopPair.singularCochainComplexMap (TopPair.ofSubsetMap g (hg q)))
          ComplexShape.embeddingUpNat := by
  rw [← cancel_mono (singularCochainFiltrationι R k M X q), Category.assoc,
    singularCochainFiltrationIso_hom_comp_singularCochainFiltrationι, Subobject.factorThru_arrow,
    Category.assoc, ← singularCochainFiltrationι_comp_extendMap_singularCochainComplexMap,
    singularCochainFiltrationIso_hom_comp_singularCochainFiltrationι_assoc]

/-- On the graded pieces `F^p / F^{p+1}`, identified with the relative singular cochains of the
pairs `(X p, X (p - 1))`, the morphism of filtrations induced by `g` is the cochain map induced by
the map of pairs `(X p, X (p - 1)) ⟶ (X' p, X' (p - 1))`. -/
private lemma decreasingFiltrationGradedMap_comp_cokernelIso_hom (p : ℤ) :
    CochainComplex.decreasingFiltrationGradedMap
        (antitone_singularCochainFiltration_sub_one R k M hX')
        (antitone_singularCochainFiltration_sub_one R k M hX)
        (extendMap (TopCat.singularCochainComplexMap g) ComplexShape.embeddingUpNat)
        (fun p ↦ factors_singularCochainFiltration R k M g hg (p - 1)) p ≫
      (singularCochainFiltrationGradedIso R k M hX p (p - 1) p rfl rfl).hom =
      (singularCochainFiltrationGradedIso R k M hX' p (p - 1) p rfl rfl).hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (filteredSpaceStepMap hX hX' g hg (by lia : p - 1 ≤ p))) ComplexShape.embeddingUpNat := by
  have π₁ := CochainComplex.π_decreasingFiltrationGradedMap
    (hF := antitone_singularCochainFiltration_sub_one R k M hX')
    (hG := antitone_singularCochainFiltration_sub_one R k M hX) _
    (fun p ↦ factors_singularCochainFiltration R k M g hg (p - 1)) p
  have hl := π_singularCochainFiltrationGradedIso_hom R k M hX p (p - 1) p rfl rfl
  have hr := π_singularCochainFiltrationGradedIso_hom R k M hX' p (p - 1) p rfl rfl
  simp only [Subobject.ofLE_refl, Category.id_comp] at hl hr
  -- The two maps of pairs `(X p, X (p - 1)) ⟶ (Y', X' (p - 1))` agree, so their cochain maps do.
  have h₂ := (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · ComplexShape.embeddingUpNat)
      ((TopPair.singularCochainComplexMap_comp (R := R) (k := k) (M := M) _ _).symm.trans <|
        (congrArg TopPair.singularCochainComplexMap
          (innerToTotal_comp_ofSubsetMap g hg hX hX' (by lia : p - 1 ≤ p))).trans <|
        TopPair.singularCochainComplexMap_comp _ _)).trans <| extendMap_comp _ _ _
  -- After the quotient map from `F^p`, both sides restrict the stage `F^p` of `Y'` to the pair
  -- `(X p, X (p - 1))`.
  refine (cancel_epi (cokernel.π _)).1 ?_
  rw [reassoc_of% π₁, hl, reassoc_of% hr]
  exact (factorThru_comp_singularCochainFiltrationIso_hom_assoc R k M g hg (p - 1) _).trans
    (_ ≫= h₂)

include hX hX' g hg in
/-- **The morphism of cohomology spectral sequences of a map of filtered spaces on the first
page.** Let `g : Y ⟶ Y'` carry each `X q` into `X' q`. Under the identifications of the first
pages with relative singular cohomology
(`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`), the morphism of cohomology
spectral sequences induced by `g` is, at `(p, q)`, the map
`Hⁿ(X' p, X' (p - 1)) ⟶ Hⁿ(X p, X (p - 1))` induced by `g`, where `p + q = n`. -/
@[reassoc]
theorem filteredSpaceCohomologySpectralSequenceFirstPageXIso_hom_naturality (p q a b : ℤ)
    (ha : a = p - 1) (hb : b = p) (n : ℕ) (hn : p + q = n) :
    ((filteredSpaceCohomologySpectralSequenceMap R k M g hg hX hX').hom 1 le_rfl).f (p, q) ≫
        (filteredSpaceCohomologySpectralSequenceFirstPageXIso R k M hX p q a b ha hb n hn).hom =
      (filteredSpaceCohomologySpectralSequenceFirstPageXIso R k M hX' p q a b ha hb n hn).hom ≫
        TopPair.singularCohomologyMap (filteredSpaceStepMap hX hX' g hg (by lia : a ≤ b)) n := by
  subst a b
  have e₁ := CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso_hom_naturality
    (hF := antitone_singularCochainFiltration_sub_one R k M hX')
    (hG := antitone_singularCochainFiltration_sub_one R k M hX) _
    (fun p ↦ factors_singularCochainFiltration R k M g hg (p - 1)) p q
  have e₂ := congrArg (HomologicalComplex.homologyMap · (p + q))
    (decreasingFiltrationGradedMap_comp_cokernelIso_hom R k M g hg hX hX' p)
  simp only [HomologicalComplex.homologyMap_comp] at e₂
  have e₃ := extendHomologyIso_hom_naturality (TopPair.singularCochainComplexMap (R := R) (k := k)
    (M := M) (filteredSpaceStepMap hX hX' g hg (by lia : p - 1 ≤ p))) ComplexShape.embeddingUpNat
    (j := n) (j' := p + q) hn.symm
  rw [filteredSpaceCohomologySpectralSequenceMap,
    filteredSpaceCohomologySpectralSequenceFirstPageXIso_hom,
    filteredSpaceCohomologySpectralSequenceFirstPageXIso_hom, reassoc_of% e₁, reassoc_of% e₂, e₃]
  simp only [Category.assoc]

include hX hX' g hg in
/-- **The comparison theorem for cohomology spectral sequences of maps of filtered spaces.** If a
map `g : Y ⟶ Y'` carrying each `X q` into `X' q` induces isomorphisms
`Hⁿ(X' p, X' (p - 1)) ≅ Hⁿ(X p, X (p - 1))` for every `p` and `n`, then the induced morphism of
cohomology spectral sequences is an isomorphism on every object of every page `r ≥ 1`. -/
theorem isIso_filteredSpaceCohomologySpectralSequenceMap_hom_f
    (h : ∀ (p : ℤ) (n : ℕ), IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (filteredSpaceStepMap hX hX' g hg (by lia : p - 1 ≤ p)) n))
    (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((filteredSpaceCohomologySpectralSequenceMap R k M g hg hX hX').hom r hr).f pq) := by
  refine SpectralSequence.Hom.isIso_hom_f_of_le _ 1 le_rfl (fun pq ↦ ?_) r hr pq
  obtain ⟨p, q⟩ := pq
  rcases lt_or_ge (p + q) 0 with hneg | hnn
  · -- Below total degree `0` both first pages vanish.
    exact (isZero_filteredSpaceCohomologySpectralSequence_page_one_X R k M hX' p q hneg).isIso
      (isZero_filteredSpaceCohomologySpectralSequence_page_one_X R k M hX p q hneg) _
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  have e := filteredSpaceCohomologySpectralSequenceFirstPageXIso_hom_naturality R k M g hg hX hX'
    p q (p - 1) p rfl rfl n hn
  rw [← Iso.eq_comp_inv] at e
  have := h p n
  rw [e]
  infer_instance

end Naturality

end TauCeti
