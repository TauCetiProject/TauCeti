/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.AlgebraicTopology.Cohomology.Triple
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The cohomological spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a map to it. The singular cochains of `Y`
vanishing on `X (p - 1)` form a decreasing filtration `F^p` of the singular cochains of `Y`, and
this file studies the spectral sequence of that filtered complex
(`TauCeti.filteredSpaceCohomologySpectralSequence`), in the classical cohomological indexing of
`CochainComplex.decreasingFiltrationSpectralSequence`. It is the cohomological counterpart of the
spectral sequence `TauCeti.filteredSpaceSpectralSequence` of the filtration of singular chains.
Singular cochains in degree `n` are placed in degree `n` of a cochain complex indexed by `ℤ` along
`ComplexShape.embeddingUpNat`.

The cochains vanishing on a subset `S ⊆ Y` are the relative singular cochains `C*(Y, S)`, a
subcomplex of `C*(Y)` (`TauCeti.vanishingSingularCochains`). They decrease as `S` grows.

* **Graded pieces.** For `S ⊆ T`, the quotient of the cochains vanishing on `S` by those vanishing
  on `T` is the relative singular cochain complex of the pair `(T, S)`
  (`TauCeti.vanishingSingularCochainsCokernelIso`), by the short exact cochain sequence of the
  triple `(Y, T, S)`.
* **First page.** The object at `(p, q)` on the first page is the relative singular cohomology
  `H^{p+q}(X p, X (p - 1))` (`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`); it
  vanishes when `p + q < 0`.
* **Abutment.** The abutment in degree `n` is `Hⁿ(Y)`
  (`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by the images of the cohomology of the
  stages, the cochains vanishing on `X (p - 1)`.
* **Convergence.** Suppose that `X (-1)` is empty and that every compact subset of `Y` lies in
  some `X q`. A singular simplex has compact image, so a cochain is determined by its values on
  the simplices of the `X q`, and a family of cochains which agree on larger and larger `X q`
  glues to a cochain: the filtration is complete and separated in each degree
  (`TauCeti.isCompleteFiltration_vanishingSingularCochains`). If moreover `Hⁿ(X j, X (j - 1))`
  vanishes for `n < j`, the spectral sequence converges strongly: on every late enough page the
  object at `(p, q)` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the filtration of
  `H^{p+q}(Y)` (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGraded`). The stages of
  the filtration need not vanish in any degree; this is the situation of the skeletal filtration
  over an infinite-dimensional CW complex.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Chapter 5.
* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorem 5.5.10.
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

/-! ### The cochains vanishing on a subset -/

section Vanishing

/-- The inclusion of the relative singular cochains of `(Y, S)`, the cochains vanishing on `S`, into
the singular cochains of `Y`, with both cochain complexes reindexed along `ℕ ⊆ ℤ`. -/
def vanishingSingularCochainsι (S : Set Y) :
    ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat ⟶
      (Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  extendMap ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f _

/-- The inclusion of the cochains vanishing on `S` is induced by the quotient map from the singular
chains of `Y` to the relative singular chains of `(Y, S)`. -/
lemma vanishingSingularCochainsι_def (S : Set Y) :
    vanishingSingularCochainsι R k M S =
      extendMap ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f
        ComplexShape.embeddingUpNat :=
  (rfl)

instance (S : Set Y) : Mono (vanishingSingularCochainsι R k M S) :=
  have := ((TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex R k M).mono_f
  HomologicalComplex.mono_extendMap _ _

/-- The **cochains vanishing on `S`**: the relative singular cochains of `(Y, S)`, as a subcomplex
of the singular cochains of `Y`, reindexed along `ℕ ⊆ ℤ`. -/
def vanishingSingularCochains (S : Set Y) :
    Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat) :=
  Subobject.mk (vanishingSingularCochainsι R k M S)

/-- The cochains vanishing on `S` are the reindexed relative singular cochain complex of
`(Y, S)`. -/
def vanishingSingularCochainsIso (S : Set Y) :
    (vanishingSingularCochains R k M S : CochainComplex (ModuleCat.{v} k) ℤ) ≅
      ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  Subobject.underlyingIso (vanishingSingularCochainsι R k M S)

@[reassoc (attr := simp)]
lemma vanishingSingularCochainsIso_hom_comp_ι (S : Set Y) :
    (vanishingSingularCochainsIso R k M S).hom ≫ vanishingSingularCochainsι R k M S =
      (vanishingSingularCochains R k M S).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {R k M}

/-- For `S ⊆ T`, the inclusion of the cochains vanishing on `T` into those of `Y` factors through
the cochains vanishing on `S`, by the map induced by the identity of `Y` as a map of pairs
`(Y, S) ⟶ (Y, T)`, the map of pairs of the triple `(Y, T, S)`. -/
@[reassoc]
lemma extendMap_comp_vanishingSingularCochainsι {S T : Set Y} (h : S ⊆ T) :
    extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.totalToOuter.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat ≫
      vanishingSingularCochainsι R k M S =
    vanishingSingularCochainsι R k M T := by
  -- The map of pairs is the identity on the ambient space `Y`, so the square of cochain sequences
  -- it induces has the identity of the cochains of `Y` in the middle.
  have h₂ := (TopPair.singularCochainComplexShortComplexMap (R := R) (k := k) (M := M)
    (TopTriple.totalToOuter.app (TopTriple.ofSubset h))).comm₁₂
  rw [TopPair.singularCochainComplexShortComplexMap_τ₁,
    TopPair.singularCochainComplexShortComplexMap_τ₂, TopTriple.totalToOuter_app_fst,
    TopCat.singularCochainComplexMap_id, Category.comp_id] at h₂
  -- The pairs of the triple are those of the subsets `S` and `T` only up to unfolding, so the
  -- composite is formed with `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans (congrArg (extendMap · _) h₂)

/-- **The cochains vanishing on a larger subset form a smaller subcomplex.** -/
lemma vanishingSingularCochains_anti {S T : Set Y} (h : S ⊆ T) :
    vanishingSingularCochains R k M T ≤ vanishingSingularCochains R k M S :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_vanishingSingularCochainsι h)

/-- Under the identifications with relative singular cochains, the inclusion of the cochains
vanishing on `T` into those vanishing on `S ⊆ T` is induced by the map of pairs
`(Y, S) ⟶ (Y, T)`. -/
@[reassoc]
lemma ofLE_comp_vanishingSingularCochainsIso_hom {S T : Set Y} (h : S ⊆ T) :
    Subobject.ofLE _ _ (vanishingSingularCochains_anti (R := R) (k := k) (M := M) h) ≫
        (vanishingSingularCochainsIso R k M S).hom =
      (vanishingSingularCochainsIso R k M T).hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (TopTriple.totalToOuter.app (TopTriple.ofSubset h)))
          ComplexShape.embeddingUpNat :=
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := vanishingSingularCochainsι R k M T) (f₂ := vanishingSingularCochainsι R k M S) _
    (extendMap_comp_vanishingSingularCochainsι h)).trans (Category.assoc _ _ _).symm

/-- Every cochain vanishes on the empty set. -/
@[simp]
lemma vanishingSingularCochains_empty :
    vanishingSingularCochains R k M (∅ : Set Y) = ⊤ := by
  have : IsEmpty (TopPair.ofSubset (∅ : Set Y)).snd := Set.isEmpty_coe_sort.2 rfl
  have : IsIso ((TopPair.ofSubset (∅ : Set Y)).singularChainComplexπ R) :=
    SSetPair.isIso_chainComplexπ _ R
  have : IsIso ((TopPair.ofSubset (∅ : Set Y)).singularCochainComplexShortComplex R k M).f := by
    rw [TopPair.singularCochainComplexShortComplex_f_eq]
    exact Functor.map_isIso _ _
  have : IsIso (vanishingSingularCochainsι R k M (∅ : Set Y)) := by
    rw [vanishingSingularCochainsι_def]
    exact Functor.map_isIso (ComplexShape.embeddingUpNat.extendFunctor _) _
  exact Subobject.mk_eq_top_of_isIso _

/-- The relative singular cochain sequence of the triple `(Y, T, S)`, for `S ⊆ T`. -/
private lemma tripleShortExact {S T : Set Y} (h : S ⊆ T) :
    (((TopTriple.ofSubset h).singularCochainComplexShortComplex R k M).map
      (ComplexShape.embeddingUpNat.extendFunctor _)).ShortExact :=
  (((TopTriple.ofSubset h).shortExact_singularCochainComplexShortComplex R k M).extend
    ComplexShape.embeddingUpNat)

/-- **The graded pieces of the filtration by vanishing.** For `S ⊆ T`, the quotient of the
cochains vanishing on `S` by those vanishing on `T` is the relative singular cochain complex of
the pair `(T, S)`, reindexed along `ℕ ⊆ ℤ`. The isomorphism is induced by restricting cochains
vanishing on `S` from `Y` to `T` (`TauCeti.π_vanishingSingularCochainsCokernelIso_hom`). -/
def vanishingSingularCochainsCokernelIso {S T : Set Y} (h : S ⊆ T) :
    cokernel (Subobject.ofLE _ _ (vanishingSingularCochains_anti (R := R) (k := k) (M := M) h)) ≅
      ((TopPair.ofInclusion h).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  cokernel.mapIso _ (((TopTriple.ofSubset h).singularCochainComplexShortComplex R k M).map
      (ComplexShape.embeddingUpNat.extendFunctor _)).f
      (vanishingSingularCochainsIso R k M T) (vanishingSingularCochainsIso R k M S)
      -- The first map of the cochain sequence of the triple `(Y, T, S)` is induced by the map of
      -- pairs `(Y, S) ⟶ (Y, T)`.
      (ofLE_comp_vanishingSingularCochainsIso_hom h) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (tripleShortExact h).gIsCokernel

/-- The identification of the graded piece with relative cochains is induced by restricting the
cochains vanishing on `S` from `Y` to `T`. -/
@[reassoc (attr := simp)]
lemma π_vanishingSingularCochainsCokernelIso_hom {S T : Set Y} (h : S ⊆ T) :
    cokernel.π _ ≫ (vanishingSingularCochainsCokernelIso (R := R) (k := k) (M := M) h).hom =
      (vanishingSingularCochainsIso R k M S).hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (TopTriple.innerToTotal.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat := by
  refine (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

/-- The quotient of the cochains vanishing on `S` by those vanishing on `T ⊇ S` has vanishing
cohomology in degree `m` when the relative singular cohomology `Hⁿ(T, S)` vanishes for `m = n`. In
negative degrees `m` there is nothing to check. -/
lemma isZero_homology_cokernel_vanishingSingularCochains {S T : Set Y} (h : S ⊆ T) (m : ℤ)
    (hm : ∀ n : ℕ, m = n → IsZero ((TopPair.ofInclusion h).singularCohomology R k M n)) :
    IsZero ((cokernel (Subobject.ofLE _ _
      (vanishingSingularCochains_anti (R := R) (k := k) (M := M) h))).homology m) := by
  refine IsZero.of_iso ?_
    ((homologyFunctor _ _ m).mapIso (vanishingSingularCochainsCokernelIso h))
  by_cases hm' : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = m
  · obtain ⟨n, hn⟩ := hm'
    exact (hm n hn.symm).of_iso (extendHomologyIso _ _ hn)
  · push Not at hm'
    exact (extend_exactAt _ _ m hm').isZero_homology

end Vanishing

/-! ### The spectral sequence -/

section SpectralSequence

variable {X : ℤ → Set Y} (hX : Monotone X)

include hX in
/-- The cochains vanishing on `X (p - 1)` form a decreasing filtration of the singular cochains of
`Y`. -/
lemma antitone_vanishingSingularCochains :
    Antitone fun p ↦ vanishingSingularCochains R k M (X (p - 1)) :=
  fun _ _ h ↦ vanishingSingularCochains_anti (hX (by lia))

/-- **The cohomological spectral sequence of a filtered space.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the decreasing
filtration `F^p` of the singular cochains of `Y` by the cochains vanishing on `X (p - 1)`, in the
classical cohomological indexing: it starts on page `1`, its differentials are
`d_r : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}`, and `E₁^{p,q} = H^{p+q}(X p, X (p - 1))`
(`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`). -/
abbrev filteredSpaceCohomologySpectralSequence :=
  CochainComplex.decreasingFiltrationSpectralSequence _
    (antitone_vanishingSingularCochains (R := R) (k := k) (M := M) hX)

/-- **The spectral object of the cohomological spectral sequence of a filtered space**, whose
abutment in degree `n` is `Hⁿ(Y)` (`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by the
images of the cohomology of the cochains vanishing on the `X (p - 1)`; the piece indexed by `-p`
is the image of the cohomology of the cochains vanishing on `X (p - 1)`. -/
abbrev filteredSpaceCohomologySpectralObject :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
    ((antitone_vanishingSingularCochains (R := R) (k := k) (M := M) hX).comp
      fun _ _ h ↦ neg_le_neg h))

/-- **The first page of the cohomological spectral sequence of a filtered space.** The object at
`(p, q)` on the first page is the relative singular cohomology `Hⁿ(X b, X a)`, where `a = p - 1`,
`b = p` and `n = p + q`. The indices are given together with equations, for flexibility. -/
def filteredSpaceCohomologySpectralSequenceFirstPageXIso (p q a b : ℤ) (ha : a = p - 1)
    (hb : b = p) (n : ℕ) (hn : p + q = n) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q) ≅
      (TopPair.ofInclusion (hX (by lia : a ≤ b))).singularCohomology R k M n :=
  CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
    (homologyFunctor _ _ _).mapIso
      (Subobject.cokernelOfLEIsoOfEq (A' := vanishingSingularCochains R k M (X b))
        (B' := vanishingSingularCochains R k M (X a))
        (congrArg (fun i ↦ vanishingSingularCochains R k M (X i)) (by lia))
        (congrArg (fun i ↦ vanishingSingularCochains R k M (X i)) (by lia)) _
        (vanishingSingularCochains_anti (hX (by lia : a ≤ b))) ≪≫
        vanishingSingularCochainsCokernelIso _) ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat hn.symm

/-- The first page of the cohomological spectral sequence of a filtered space vanishes in negative
total degree `p + q`, since singular cochains are concentrated in nonnegative degrees. -/
lemma isZero_filteredSpaceCohomologySpectralSequence_page_one_X (p q : ℤ) (h : p + q < 0) :
    IsZero (((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q)) :=
  IsZero.of_iso ((extend_exactAt _ ComplexShape.embeddingUpNat _ fun n hn ↦ by
      have : (n : ℤ) = p + q := hn
      lia).isZero_homology)
    (CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso
      (fun p ↦ vanishingSingularCochains R k M (X (p - 1)))
      (antitone_vanishingSingularCochains R k M hX)
      p q ≪≫
      (homologyFunctor _ _ _).mapIso
        (vanishingSingularCochainsCokernelIso (hX (by lia : p - 1 ≤ p + 1 - 1))))

/-- **The abutment of the cohomological spectral sequence of a filtered space** in degree `n` is
the singular cohomology `Hⁿ(Y)`. -/
def filteredSpaceCohomologyAbutmentIso (n : ℕ) :
    (filteredSpaceCohomologySpectralObject R k M hX).abutment n ≅
      Y.singularCohomology R k M n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat rfl

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

/-- **Cochains vanishing on a subset, elementwise.** A cochain of `Y` in degree `n` lies in the
subcomplex of cochains vanishing on `S` exactly when it vanishes on every singular `n`-simplex of
`Y` with image in `S`. The cochain is read in degree `m = n` of the reindexed complex. -/
theorem mem_range_vanishingSingularCochains_arrow_iff (S : Set Y) {n : ℕ} {m : ℤ}
    (hn : ComplexShape.embeddingUpNat.f n = m)
    (x : ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X m) :
    x ∈ LinearMap.range ((vanishingSingularCochains R k M S).arrow.f m).hom ↔
      ∀ σ : (TopCat.toSSet.obj Y) _⦋n⦌, Set.range (Y.toSSetObjEquiv _ σ) ⊆ S →
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫
          (extendXIso (Y.singularCochainComplex R k M) ComplexShape.embeddingUpNat hn).hom x =
          0 := by
  -- The ambient cochains of the pair `(Y, S)` are those of `Y` up to unfolding; the isomorphism
  -- is taken at the former to match the terms of the cochain sequence of the pair.
  let eY := extendXIso ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).X₂
    ComplexShape.embeddingUpNat hn
  let eP := extendXIso ((TopPair.ofSubset S).singularCochainComplex R k M)
    ComplexShape.embeddingUpNat hn
  -- The range of the arrow is the range of the inclusion of the relative cochains.
  have hrange : LinearMap.range ((vanishingSingularCochains R k M S).arrow.f m).hom =
      LinearMap.range ((vanishingSingularCochainsι R k M S).f m).hom := by
    rw [← vanishingSingularCochainsIso_hom_comp_ι, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  rw [hrange, vanishingSingularCochainsι_def, extendMap_f _ _ hn]
  refine Iff.trans ?_ (mem_range_f_iff S n (eY.hom x))
  -- In degree `m` the inclusion is that of degree `n`, conjugated by the isomorphisms `eP`, `eY`;
  -- the composites are restated as applied composites, which `rw` does not unfold.
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨eP.hom y, ?_⟩
    change _ = ((eP.hom ≫ ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f.f n ≫
      eY.inv) ≫ eY.hom) y
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ModuleCat.comp_apply]
  · rintro ⟨z, hz⟩
    refine ⟨eP.inv z, ?_⟩
    change (eP.inv ≫ eP.hom ≫
      ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f.f n ≫ eY.inv) z = x
    rw [Iso.inv_hom_id_assoc, ModuleCat.comp_apply]
    exact (congrArg eY.inv hz).trans (Iso.hom_inv_id_apply eY x)

variable {X : ℤ → Set Y}

/-- If every compact subset of `Y` lies in some `X q`, every singular simplex of `Y` lies in some
`X (j - 1)` with `j` a natural number. -/
private lemma exists_range_subset (hX : Monotone X) (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q)
    {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    ∃ j : ℕ, Set.range (Y.toSSetObjEquiv _ σ) ⊆ X (j - 1) := by
  obtain ⟨q, hq⟩ := hK _ (isCompact_range (Y.toSSetObjEquiv _ σ).continuous)
  exact ⟨(q + 1).toNat, hq.trans (hX (by lia))⟩

/-- **Limits for the filtration by vanishing.** If every compact subset of `Y` lies in some `X q`,
a sequence of cochains whose `j`th and `(j + 1)`st terms agree on `X (j - 1)` has a limit: a
cochain agreeing with its `j`th term on `X (j - 1)` for every `j`. The sequence stabilizes on each
singular simplex, and the stable values define the limit. -/
private lemma exists_limit (hX : Monotone X) (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q)
    {n : ℕ} {m : ℤ} (hn : ComplexShape.embeddingUpNat.f n = m)
    (x : ℕ → ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X m)
    (hx : ∀ j : ℕ, x (j + 1) - x j ∈
      LinearMap.range ((vanishingSingularCochains R k M (X (j - 1))).arrow.f m).hom) :
    ∃ L, ∀ j : ℕ, L - x j ∈
      LinearMap.range ((vanishingSingularCochains R k M (X (j - 1))).arrow.f m).hom := by
  let e := extendXIso (Y.singularCochainComplex R k M) ComplexShape.embeddingUpNat hn
  have hmem (j : ℕ) (x) := mem_range_vanishingSingularCochains_arrow_iff (R := R) (k := k)
    (M := M) (X (j - 1)) hn x
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

/-- **The filtration of singular cochains by vanishing is complete and separated.** Suppose that
every compact subset of `Y` lies in some `X q`. Then in each degree the filtration of the singular
cochains of `Y` by the cochains vanishing on `X (j - 1)`, `j ∈ ℕ`, is separated, since a singular
simplex lies in some `X q`, and complete: a sequence of cochains whose `j`th and `(j + 1)`st terms
agree on `X (j - 1)` stabilizes on each simplex, and the stable values define its limit. -/
theorem isCompleteFiltration_vanishingSingularCochains (hX : Monotone X)
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (m : ℤ) :
    IsCompleteFiltration fun j : ℕ ↦
      LinearMap.range ((vanishingSingularCochains R k M (X (j - 1))).arrow.f m).hom := by
  have hanti : Antitone fun j : ℕ ↦
      LinearMap.range ((vanishingSingularCochains R k M (X (j - 1))).arrow.f m).hom :=
    fun _ _ h ↦ Subobject.range_arrow_f_hom_le (vanishingSingularCochains_anti (hX (by lia))) m
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
    exact ((mem_range_vanishingSingularCochains_arrow_iff _ hn x).1 (hx j) σ hj).trans
      comp_zero.symm
  rw [← Iso.hom_inv_id_apply e x, h0, map_zero]

section Convergence

variable (hX : Monotone X) (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (h₀ : X (-1) = ∅)
  (hvanish : ∀ (j : ℤ) (n : ℕ), n < j →
    IsZero ((TopPair.ofInclusion (hX (sub_le_self j zero_le_one))).singularCohomology R k M n))

include h₀ in
private lemma vanishingSingularCochains_zero_sub_one :
    vanishingSingularCochains R k M (X (0 - 1)) = ⊤ := by
  rw [zero_sub, h₀, vanishingSingularCochains_empty]

include hvanish in
private lemma isZero_homology_cokernel (j : ℤ) (_ : 0 ≤ j) (n : ℤ) (hn : n < j) :
    IsZero ((cokernel (Subobject.ofLE (vanishingSingularCochains R k M (X (j + 1 - 1)))
      (vanishingSingularCochains R k M (X (j - 1)))
      (antitone_vanishingSingularCochains R k M hX (by lia)))).homology n) :=
  -- The stage `X (j + 1 - 1)` is `X j`.
  (isZero_homology_cokernel_vanishingSingularCochains (hX (sub_le_self j zero_le_one)) n
    fun n' hn' ↦ hvanish j n' (by lia)).of_iso ((homologyFunctor _ _ n).mapIso
      (Subobject.cokernelOfLEIsoOfEq (congrArg (fun i ↦ vanishingSingularCochains R k M (X i))
        (by lia)) rfl _ _))

include hK h₀ hvanish in
/-- **The filtration of the abutment vanishes above the degree.** Suppose that `X (-1)` is empty,
that every compact subset of `Y` lies in some `X q`, and that `Hⁿ(X j, X (j - 1)) = 0` for
`n < j`. Then the piece of the filtration of `Hⁿ(Y)` given by the cochains vanishing on
`X (p - 1)`, indexed by `-p`, vanishes for `n < p`. -/
theorem isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration {p n : ℤ} (hn : n < p) :
    IsZero ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltration (-p) n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration_of_antitone_of_firstQuadrant _
    (antitone_vanishingSingularCochains R k M hX) (vanishingSingularCochains_zero_sub_one h₀)
    (isCompleteFiltration_vanishingSingularCochains hX hK)
    (isZero_homology_cokernel hX hvanish) hn

/-- **Strong convergence of the cohomological spectral sequence of a filtered space.** Suppose
that `X (-1)` is empty, that every compact subset of `Y` lies in some `X q`, and that the relative
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
    (antitone_vanishingSingularCochains R k M hX) (vanishingSingularCochains_zero_sub_one h₀)
    (isCompleteFiltration_vanishingSingularCochains hX hK)
    (isZero_homology_cokernel hX hvanish) r hr p q hp hq

end Convergence

end Complete

end TauCeti
