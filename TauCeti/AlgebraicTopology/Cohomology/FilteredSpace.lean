/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.Embedding.ExtendSubobject
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete
public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.CategoryTheory.Subobject.Cokernel

/-!
# The cohomological spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a map to it. The singular cochains of `Y` that
vanish on the singular simplices of `X (p - 1)`, that is the relative cochains `C*(Y, X (p - 1))`,
form a decreasing filtration `F^p` of the singular cochains of `Y`
(`TauCeti.singularCochainFiltration`), and this file studies the spectral sequence of that
filtered complex (`TauCeti.filteredSpaceCohomologySpectralSequence`), in the classical
cohomological indexing of `CochainComplex.decreasingFiltrationSpectralSequence`. Singular cochains
are indexed by `ℕ`, and are extended by zero to `ℤ` along `ComplexShape.embeddingUpNat`.

* **Graded pieces.** For `S ⊆ S'`, the quotient of the cochains vanishing on `S` by those vanishing
  on `S'` is the relative singular cochain complex of the pair `(S', S)`
  (`TauCeti.singularCochainSubobjectCokernelIso`), by the short exact cochain sequence of the
  triple `(Y, S', S)`.
* **First page.** The object at `(p, q)` on the first page is the relative singular cohomology
  `H^{p+q}(X p, X (p - 1))` (`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`); it
  vanishes when `p + q < 0`.
* **Abutment.** The abutment in degree `n` is the singular cohomology `Hⁿ(Y)`
  (`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by the images of the relative
  cohomology of the pairs `(Y, X (p - 1))`.
* **Completeness.** If every compact subset of `Y` lies in some `X q`, then every singular simplex
  of `Y` lies in some `X q`, so in each degree the filtration is complete and separated
  (`TauCeti.isCompleteFiltration_singularCochainFiltration`): a cochain is determined by its values
  on the simplices, and a sequence of cochains whose successive differences vanish on larger and
  larger `X q` stabilizes on each simplex. Unlike the filtration of singular chains, the stages
  need not vanish in any degree, as for the skeletal filtration of an infinite-dimensional CW
  complex.
* **Convergence.** If moreover `X (-1) = ∅` and `H^n(X j, X (j - 1)) = 0` whenever `n < j`, the
  spectral sequence converges strongly: on every page `r ≥ 1` with `p < r` and `q + 1 < r` the
  object at `(p, q)` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the filtration of the
  abutment (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFirstQuadrant`). The
  piece `F^p Hⁿ` of this filtration vanishes for `n < p`
  (`TauCeti.isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration`).

For the preimages of the skeleta of a CW base under a Serre fibration this is the cohomological
Serre spectral sequence; see `TauCeti.AlgebraicTopology.Singular.Fibration.Cohomology`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.6 and Section 5.1.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Theorem 5.5.10 (complete convergence).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*)
  [Ring k] [Linear k C] (M : C) {Y : TopCat.{w}}

/-! ### Cochains vanishing on a subset -/

section Subset

/-- The inclusion of the relative singular cochains `C*(Y, S)`, the cochains vanishing on the
singular simplices of `S`, into the singular cochains of `Y`, with both cochain complexes extended
by zero to `ℤ` along `ComplexShape.embeddingUpNat`. -/
def singularCochainSubobjectι (S : Set Y) :
    ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat ⟶
      (Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  extendMap ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f
    ComplexShape.embeddingUpNat

/-- The inclusion of the cochains vanishing on `S` is induced by the map from the relative cochains
of `(Y, S)` to the cochains of `Y`. -/
lemma singularCochainSubobjectι_def (S : Set Y) :
    singularCochainSubobjectι R k M S =
      extendMap ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f
        ComplexShape.embeddingUpNat := (rfl)

instance (S : Set Y) : Mono (singularCochainSubobjectι R k M S) := by
  have := ((TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex R k M).mono_f
  exact HomologicalComplex.mono_extendMap _ _

/-- The singular cochains of `Y` vanishing on the singular simplices of `S`, as a subcomplex of the
singular cochains of `Y` extended by zero to `ℤ`. -/
def singularCochainSubobject (S : Set Y) :
    Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat) :=
  Subobject.mk (singularCochainSubobjectι R k M S)

/-- The subcomplex of cochains vanishing on `S` is the extended relative cochain complex of
`(Y, S)`. -/
def singularCochainSubobjectIso (S : Set Y) :
    (singularCochainSubobject R k M S : CochainComplex (ModuleCat.{v} k) ℤ) ≅
      ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  Subobject.underlyingIso _

/-- The identification of the subcomplex of cochains vanishing on `S` with the relative cochains
of `(Y, S)` is compatible with the inclusions into the cochains of `Y`. -/
@[reassoc (attr := simp)]
lemma singularCochainSubobjectIso_hom_comp_singularCochainSubobjectι (S : Set Y) :
    (singularCochainSubobjectIso R k M S).hom ≫ singularCochainSubobjectι R k M S =
      (singularCochainSubobject R k M S).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {R k M} in
/-- For `S ⊆ S'`, the cochains vanishing on `S'` vanish on `S`: the inclusion of the relative
cochains of `(Y, S')` into those of `Y` factors through the relative cochains of `(Y, S)`, by the
map induced by the map of pairs `(Y, S) ⟶ (Y, S')` of the triple `(Y, S', S)`. -/
@[reassoc]
lemma extendMap_singularCochainComplexMap_comp_singularCochainSubobjectι {S S' : Set Y}
    (h : S ⊆ S') :
    extendMap (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M)
        (TopTriple.totalToOuter.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat ≫
      singularCochainSubobjectι R k M S = singularCochainSubobjectι R k M S' := by
  have hc := congrArg (fun φ ↦ (TauCeti.ChainComplex.linearYonedaFunctor k M).map φ.op)
    ((TopTriple.ofSubset h).singularChainComplexπ_comp_totalToOuter R)
  simp only [op_comp, Functor.map_comp] at hc
  exact (extendMap_comp _ _ _).symm.trans (congrArg (extendMap · _) hc)

variable {R k M} in
/-- The subcomplex of cochains vanishing on `S` shrinks as `S` grows. -/
lemma singularCochainSubobject_anti {S S' : Set Y} (h : S ⊆ S') :
    singularCochainSubobject R k M S' ≤ singularCochainSubobject R k M S :=
  Subobject.mk_le_mk_of_comm _
    (extendMap_singularCochainComplexMap_comp_singularCochainSubobjectι h)

variable {R k M} in
/-- Under the identifications with relative cochains, the inclusion of the cochains vanishing on
`S'` into those vanishing on `S` is induced by the map of pairs `(Y, S) ⟶ (Y, S')`. -/
@[reassoc]
lemma ofLE_comp_singularCochainSubobjectIso_hom {S S' : Set Y} (h : S ⊆ S') :
    Subobject.ofLE _ _ (singularCochainSubobject_anti h) ≫
        (singularCochainSubobjectIso R k M S).hom =
      (singularCochainSubobjectIso R k M S').hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (TopTriple.totalToOuter.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat :=
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := singularCochainSubobjectι R k M S') (f₂ := singularCochainSubobjectι R k M S) _
    (extendMap_singularCochainComplexMap_comp_singularCochainSubobjectι h)).trans
      (Category.assoc _ _ _).symm

/-- When `S` is empty, every cochain vanishes on `S`. -/
lemma singularCochainSubobject_eq_top {S : Set Y} (hS : S = ∅) :
    singularCochainSubobject R k M S = ⊤ := by
  have : IsEmpty (TopPair.ofSubset S).snd := by
    rw [hS]
    exact Set.isEmpty_coe_sort.2 rfl
  have : IsIso ((TopPair.ofSubset S).singularChainComplexπ R) :=
    SSetPair.isIso_chainComplexπ _ R
  have : IsIso ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f := by
    rw [TopPair.singularCochainComplexShortComplex_f_eq]
    exact Functor.map_isIso _ _
  have : IsIso (singularCochainSubobjectι R k M S) :=
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} k)).map_isIso _
  exact Subobject.mk_eq_top_of_isIso _

variable {S S' : Set Y} (h : S ⊆ S')

/-- The extended cochain sequence `C*(Y, S') ⟶ C*(Y, S) ⟶ C*(S', S)` of the triple `(Y, S', S)`,
written with the pairs of nested subsets. -/
private abbrev subsetTripleShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℤ) :=
  ShortComplex.mk
    (X₁ := ((TopPair.ofSubset S').singularCochainComplex R k M).extend ComplexShape.embeddingUpNat)
    (X₂ := ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat)
    (X₃ := ((TopPair.ofInclusion h).singularCochainComplex R k M).extend
      ComplexShape.embeddingUpNat)
    (extendMap (TopPair.singularCochainComplexMap
      (TopTriple.totalToOuter.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat)
    (extendMap (TopPair.singularCochainComplexMap
      (TopTriple.innerToTotal.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat)
    (((TopTriple.ofSubset h).singularCochainComplexShortComplex R k M).map
      (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} k))).zero

private lemma subsetTripleShortComplex_shortExact :
    (subsetTripleShortComplex R k M h).ShortExact :=
  ((TopTriple.ofSubset h).shortExact_singularCochainComplexShortComplex R k M).extend _

/-- **The graded pieces of the filtration by vanishing.** For `S ⊆ S'`, the quotient of the
cochains vanishing on `S` by those vanishing on `S'` is the relative singular cochain complex of
the pair `(S', S)`, extended by zero to `ℤ`. The isomorphism is induced by restriction of cochains
from `(Y, S)` to `(S', S)` (`TauCeti.π_singularCochainSubobjectCokernelIso_hom`). -/
def singularCochainSubobjectCokernelIso :
    cokernel (Subobject.ofLE _ _ (singularCochainSubobject_anti (R := R) (k := k) (M := M) h)) ≅
      ((TopPair.ofInclusion h).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  cokernel.mapIso _ (subsetTripleShortComplex R k M h).f
      (singularCochainSubobjectIso R k M S') (singularCochainSubobjectIso R k M S)
      (ofLE_comp_singularCochainSubobjectIso_hom h) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (subsetTripleShortComplex_shortExact R k M h).gIsCokernel

/-- The identification of the graded piece with relative cochains of `(S', S)` is induced by the
restriction of cochains along the map of pairs `(S', S) ⟶ (Y, S)`. -/
@[reassoc (attr := simp)]
lemma π_singularCochainSubobjectCokernelIso_hom :
    cokernel.π _ ≫ (singularCochainSubobjectCokernelIso R k M h).hom =
      (singularCochainSubobjectIso R k M S).hom ≫
        extendMap (TopPair.singularCochainComplexMap
          (TopTriple.innerToTotal.app (TopTriple.ofSubset h))) ComplexShape.embeddingUpNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

/-- The graded piece of the filtration by vanishing has vanishing cohomology in degree `m` when the
relative singular cohomology `Hⁿ(S', S)` vanishes for `m = n`. In negative degrees there is
nothing to check. -/
lemma isZero_homology_cokernel_singularCochainSubobject (m : ℤ)
    (hm : ∀ n : ℕ, m = n →
      IsZero ((TopPair.ofInclusion h).singularCohomology R k M n)) :
    IsZero ((cokernel (Subobject.ofLE _ _
      (singularCochainSubobject_anti (R := R) (k := k) (M := M) h))).homology m) := by
  refine IsZero.of_iso ?_
    ((homologyFunctor (ModuleCat.{v} k) _ m).mapIso (singularCochainSubobjectCokernelIso R k M h))
  by_cases hm' : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = m
  · obtain ⟨n, hn⟩ := hm'
    exact (hm n hn.symm).of_iso (extendHomologyIso _ _ hn)
  · push Not at hm'
    exact (extend_exactAt _ _ m hm').isZero_homology

end Subset

/-! ### Membership in the stages -/

section Membership

variable {R k M}

/-- **A cochain vanishes on `S` exactly when it lies in the image of the relative cochains.** A
singular cochain `c` of degree `m` of `Y`, read in degree `n = m` of the extended complex, is a
cochain vanishing on `S` exactly when `c` vanishes on every singular `m`-simplex of `Y` with image
in `S`. -/
theorem mem_range_singularCochainSubobject_arrow_iff (S : Set Y) {m : ℕ} {n : ℤ}
    (hn : ComplexShape.embeddingUpNat.f m = n)
    (c : ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X n) :
    c ∈ LinearMap.range ((singularCochainSubobject R k M S).arrow.f n).hom ↔
      ∀ σ : (TopCat.toSSet.obj Y) _⦋m⦌, Set.range (Y.toSSetObjEquiv _ σ) ⊆ S →
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫
          ((Y.singularCochainComplex R k M).extendXIso _ hn).hom c = 0 := by
  -- The stage is the image of the extended relative cochains, whose image in degree `m` is the
  -- kernel of restriction to `S`, by exactness of the cochain sequence of the pair `(Y, S)`.
  have hrange : LinearMap.range ((singularCochainSubobject R k M S).arrow.f n).hom =
      LinearMap.range ((singularCochainSubobjectι R k M S).f n).hom := by
    rw [← singularCochainSubobjectIso_hom_comp_singularCochainSubobjectι,
      HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have hexact : LinearMap.range
      (((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f.f m).hom =
        LinearMap.ker ((TopCat.singularCochainComplexMap (R := R) (k := k) (M := M)
          (TopPair.ofSubset S).map).f m).hom :=
    (((TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex R k M).exact.map
      (HomologicalComplex.eval (ModuleCat.{v} k) (ComplexShape.up ℕ) m)).moduleCat_range_eq_ker
  rw [hrange, singularCochainSubobjectι_def]
  refine (HomologicalComplex.mem_range_extendMap_f_iff ComplexShape.embeddingUpNat
    ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f hn c).trans ?_
  rw [hexact, LinearMap.mem_ker]
  rw [TopCat.singularCochainComplexMap_f_apply]
  refine (SSet.chainComplexMap_f_comp_eq_zero_iff _ R _).trans ⟨fun hc σ hσ ↦ ?_, fun hc τ ↦ ?_⟩
  · obtain ⟨τ, rfl⟩ := ((TopPair.ofSubset S).isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff
      _ σ).2 (hσ.trans (TopPair.range_ofSubset_map (B := S)).ge)
    exact hc τ
  · exact hc _ ((((TopPair.ofSubset S).isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff
      _ _).1 ⟨τ, rfl⟩).trans (TopPair.range_ofSubset_map (B := S)).le)

end Membership

/-! ### The filtration of a filtered space -/

variable (X : ℤ → Set Y)

/-- The decreasing filtration of the singular cochains of `Y`, extended by zero to `ℤ`, whose
`p`th stage `F^p` consists of the cochains vanishing on the singular simplices of `X (p - 1)`. -/
abbrev singularCochainFiltration (p : ℤ) :
    Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat) :=
  singularCochainSubobject R k M (X (p - 1))

variable {X} (hX : Monotone X)

include hX in
/-- The filtration of the singular cochains by vanishing on an increasing family of subsets is
decreasing. -/
lemma antitone_singularCochainFiltration : Antitone (singularCochainFiltration R k M X) :=
  fun _ _ hpq ↦ singularCochainSubobject_anti (hX (by lia))

/-- **The cohomological spectral sequence of a filtered space.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the decreasing
filtration of the singular cochains of `Y` by the cochains vanishing on the `X (p - 1)`, in the
classical cohomological indexing: it starts on page `1`, with differentials
`d_r : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}`. -/
abbrev filteredSpaceCohomologySpectralSequence :=
  CochainComplex.decreasingFiltrationSpectralSequence (singularCochainFiltration R k M X)
    (antitone_singularCochainFiltration R k M hX)

/-- **The spectral object of the cohomological spectral sequence of a filtered space**, for an
increasing family `X : ℤ → Set Y` of subsets of `Y`. Its abutment in degree `n` is `Hⁿ(Y)`
(`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by the images of the relative cohomology
of the pairs `(Y, X (p - 1))`; the piece `F^p` sits at index `-p`. -/
abbrev filteredSpaceCohomologySpectralObject :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
    ((antitone_singularCochainFiltration R k M hX).comp fun _ _ h ↦ neg_le_neg h))

/-- The graded piece `F^p / F^{p+1}` of the filtration of singular cochains by vanishing is the
quotient of the cochains vanishing on `X (p - 1)` by those vanishing on `X p`. -/
private def filtrationCokernelIsoOfEq (p : ℤ) :
    cokernel (Subobject.ofLE (singularCochainFiltration R k M X (p + 1))
      (singularCochainFiltration R k M X p)
      (antitone_singularCochainFiltration R k M hX (by lia))) ≅
      cokernel (Subobject.ofLE _ _ (singularCochainSubobject_anti (R := R) (k := k) (M := M)
        (hX (by lia : p - 1 ≤ p)))) :=
  Subobject.cokernelOfLEIsoOfEq
    (congrArg (fun i ↦ singularCochainSubobject R k M (X i)) (add_sub_cancel_right p 1)) rfl _ _

/-- The graded piece `F^p / F^{p+1}` of the filtration of singular cochains by vanishing is the
relative singular cochain complex of the pair `(X p, X (p - 1))`. -/
private def filtrationCokernelIso (p : ℤ) :
    cokernel (Subobject.ofLE (singularCochainFiltration R k M X (p + 1))
      (singularCochainFiltration R k M X p)
      (antitone_singularCochainFiltration R k M hX (by lia))) ≅
      ((TopPair.ofInclusion (hX (by lia : p - 1 ≤ p))).singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat :=
  filtrationCokernelIsoOfEq R k M hX p ≪≫
    singularCochainSubobjectCokernelIso R k M (hX (by lia : p - 1 ≤ p))

/-- **The first page of the cohomological spectral sequence of a filtered space.** The object at
`(p, q)` on the first page is the relative singular cohomology `H^{p+q}(X p, X (p - 1))`. -/
def filteredSpaceCohomologySpectralSequenceFirstPageXIso (p q : ℤ) (n : ℕ) (hn : p + q = n) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q) ≅
      (TopPair.ofInclusion (hX (by lia : p - 1 ≤ p))).singularCohomology R k M n :=
  CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
    (homologyFunctor (ModuleCat.{v} k) _ _).mapIso (filtrationCokernelIso R k M hX p) ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat hn.symm

/-- The first page of the cohomological spectral sequence of a filtered space vanishes in
negative total degree `p + q`, since singular cochains are concentrated in nonnegative degrees. -/
lemma isZero_filteredSpaceCohomologySpectralSequence_page_one_X (p q : ℤ) (h : p + q < 0) :
    IsZero (((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q)) :=
  IsZero.of_iso ((extend_exactAt _ ComplexShape.embeddingUpNat _ fun n hn ↦ by
      have : (n : ℤ) = p + q := hn
      lia).isZero_homology)
    (CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
      (homologyFunctor (ModuleCat.{v} k) _ _).mapIso (filtrationCokernelIso R k M hX p))

/-- **The abutment of the cohomological spectral sequence of a filtered space** in degree `n` is
the singular cohomology `Hⁿ(Y)`. -/
def filteredSpaceCohomologyAbutmentIso (n : ℕ) :
    (filteredSpaceCohomologySpectralObject R k M hX).abutment n ≅
      Y.singularCohomology R k M n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat rfl


/-! ### Completeness and convergence -/

variable {R k M}

include hX in
/-- **The filtration of singular cochains is complete and separated.** If every compact subset of
`Y` lies in some `X q`, then in each degree the stages `F^j`, `j ≥ 0`, of the filtration of the
singular cochains by vanishing on `X (j - 1)` form a complete separated filtration: a cochain is
determined by its values on the singular simplices, each of which lies in some `X q`, and a
sequence whose successive differences vanish on larger and larger `X q` stabilizes on each
simplex. -/
theorem isCompleteFiltration_singularCochainFiltration
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (n : ℤ) :
    IsCompleteFiltration fun j : ℕ ↦
      LinearMap.range ((singularCochainFiltration R k M X j).arrow.f n).hom := by
  have hanti : Antitone fun j : ℕ ↦
      LinearMap.range ((singularCochainFiltration R k M X j).arrow.f n).hom := fun _ _ hab ↦
    Subobject.range_arrow_f_hom_le
      (antitone_singularCochainFiltration R k M hX (by exact_mod_cast hab)) n
  by_cases hn : ∃ m : ℕ, ComplexShape.embeddingUpNat.f m = n
  swap
  · -- Below degree `0` the extended cochain complex vanishes.
    push Not at hn
    have : Subsingleton (((Y.singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat).X n) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_extend_X _ _ n hn)
    exact ⟨hanti, fun x _ ↦ Subsingleton.elim _ _,
      fun x _ ↦ ⟨0, fun j ↦ by rw [Subsingleton.elim (0 - x j) 0]; exact zero_mem _⟩⟩
  obtain ⟨m, hm⟩ := hn
  have hmem (j : ℕ) (c) := mem_range_singularCochainSubobject_arrow_iff (R := R) (k := k)
    (M := M) (X ((j : ℤ) - 1)) hm c
  set e := (Y.singularCochainComplex R k M).extendXIso ComplexShape.embeddingUpNat hm
  -- Every singular simplex lies in the stage `X (N σ - 1)`.
  have hN (σ : (TopCat.toSSet.obj Y) _⦋m⦌) :
      ∃ N : ℕ, Set.range (Y.toSSetObjEquiv _ σ) ⊆ X ((N : ℤ) - 1) := by
    obtain ⟨q, hq⟩ := hK _ (isCompact_range (Y.toSSetObjEquiv _ σ).continuous)
    exact ⟨(q + 1).toNat, hq.trans (hX (by lia))⟩
  choose N hN using hN
  refine ⟨hanti, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · -- A cochain vanishing on every stage vanishes on every simplex.
    have h₀ : e.hom x = 0 := SSet.chainComplex_hom_ext fun σ ↦
      ((hmem _ x).1 (hx _) σ (hN σ)).trans comp_zero.symm
    simpa using congrArg e.inv h₀
  · -- On a simplex in `X (a - 1)`, the sequence is constant from `a` on.
    have hstab (σ : (TopCat.toSSet.obj Y) _⦋m⦌) (a : ℕ)
        (ha : Set.range (Y.toSSetObjEquiv _ σ) ⊆ X ((a : ℤ) - 1)) (b : ℕ) (hab : a ≤ b) :
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ e.hom (x b) =
          (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ e.hom (x a) := by
      induction b, hab using Nat.le_induction with
      | base => rfl
      | succ b hab ih =>
        have h := (hmem b _).1 (hx b) σ (ha.trans (hX (by lia)))
        rw [map_sub] at h
        exact (sub_eq_zero.1 ((Preadditive.comp_sub _ _ _).symm.trans h)).trans ih
    -- The limit takes on each simplex `σ` the eventual value of the sequence there.
    let L := Cofan.IsColimit.desc ((TopCat.toSSet.obj Y).isColimitChainComplexXCofan R m)
      fun σ ↦ (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫ e.hom (x (N σ))
    refine ⟨e.inv L, fun j ↦ (hmem j _).2 fun σ hσ ↦ ?_⟩
    have hL : e.hom (e.inv L) = L := ConcreteCategory.congr_hom e.inv_hom_id L
    rw [map_sub, hL]
    refine (Preadditive.comp_sub _ _ _).trans (sub_eq_zero.2 ((Cofan.IsColimit.fac _ _ σ).trans ?_))
    rcases le_total j (N σ) with h | h
    · exact hstab σ j hσ _ h
    · exact (hstab σ _ (hN σ) _ h).symm

/-- The graded pieces `F^j / F^{j+1}` of the filtration of singular cochains by vanishing have
vanishing cohomology in degree `m` when `Hⁿ(X j, X (j - 1))` vanishes for `m = n`. -/
private lemma isZero_homology_filtrationCokernel (j m : ℤ)
    (h : ∀ n : ℕ, m = n →
      IsZero ((TopPair.ofInclusion (hX (by lia : j - 1 ≤ j))).singularCohomology R k M n)) :
    IsZero ((cokernel (Subobject.ofLE (singularCochainFiltration R k M X (j + 1))
      (singularCochainFiltration R k M X j)
      (antitone_singularCochainFiltration R k M hX (by lia)))).homology m) :=
  (isZero_homology_cokernel_singularCochainSubobject R k M _ m h).of_iso
    ((homologyFunctor (ModuleCat.{v} k) _ m).mapIso (filtrationCokernelIsoOfEq R k M hX j))

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
        ((singularCochainFiltration R k M X p).arrow.f n) (isZero_extend_X _ _ n fun m hm ↦ ?_)))
    have : (m : ℤ) = n := hm
    lia
  · -- Above degree `n` the graded pieces have no cohomology in degree `n`, and the stages from
    -- `p ≥ 0` on form a complete filtration.
    obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ p)
    exact CochainComplex.isZero_homology_of_antitone_of_isCompleteFiltration _
      (antitone_singularCochainFiltration R k M hX)
      (by
        convert (isCompleteFiltration_singularCochainFiltration hX hK (n - 1)).comp_add_right p'
          using 2
        push_cast
        rw [add_comm])
      (fun x hx ↦ (isCompleteFiltration_singularCochainFiltration hX hK n).eq_zero_of_forall_mem
        x fun j ↦ hx j)
      fun j hj ↦ isZero_homology_filtrationCokernel hX j n fun m hm ↦ hvanish j m (by lia)

/-- **Strong convergence of the cohomological spectral sequence of a filtered space.** Suppose
that every compact subset of `Y` lies in some `X q`, that `X (-1) = ∅`, and that
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
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFirstQuadrant _ _
    (singularCochainSubobject_eq_top R k M (by rwa [zero_sub]))
    (isCompleteFiltration_singularCochainFiltration hX hK)
    (fun j _ m hm ↦ isZero_homology_filtrationCokernel hX j m fun n hn ↦ hvanish j n (by lia))
    r hr p q hp hq

end TauCeti
