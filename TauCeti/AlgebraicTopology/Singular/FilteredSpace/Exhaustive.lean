/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Filtration

/-!
# Exhaustive filtrations of a space

Let `X : ℤ → Set Y` be an increasing family of subsets of a space `Y` which *absorbs compact
sets*: every compact subset of `Y` lies in some `X q`. Since a singular simplex has compact
image, every singular chain of `Y` is then a chain of some `X q`
(`TauCeti.exists_mem_range_singularChainFiltration_arrow`): the filtration of the singular chains
of `Y` by those of the `X q` is exhaustive, even when no `X q` is all of `Y`. The proof uses that
singular chains have compact supports (`TauCeti.isColimitMapCoconeToSSet`).

The convergence statements for exhaustive filtrations of
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive` therefore apply to the spectral
sequence of the filtered space (`TauCeti.filteredSpaceSpectralSequence`), with coefficients in
modules:

* the filtration of the abutment `Hₙ(Y)` is exhaustive
  (`TauCeti.exists_mem_range_filteredSpace_abutmentFiltrationι`);
* it reaches `Hₙ(Y)` at `b` when the relative homology groups `Hₙ(X (i + 1), X i)` vanish for
  `i ≥ b` (`TauCeti.isIso_filteredSpace_abutmentFiltrationι`);
* when moreover some stage `X a` is empty and the relative homology groups `Hₙ₊₁(X (i + 1), X i)`
  vanish for large `i`, the object at `(p, q)` with `p + q = -n` on a large enough page is the
  corresponding graded piece of the filtration of `Hₙ(Y)`
  (`TauCeti.filteredSpaceSpectralSequencePageXIsoGradedOfExhaustive`). This is strong convergence
  without a finite upper bound on the filtration.

The main example is the **skeletal filtration** `TauCeti.skeletalFiltration C p` of a space over a
relative CW complex `C`: its stage `q` is the preimage `p⁻¹(Bᵠ)` of the `q`-skeleton under a
map `p : Y → B`. For continuous `p` it absorbs compact sets
(`TauCeti.exists_subset_skeletalFiltration_of_isCompact`) whatever the number of cells and the
dimension of `C`, so singular chains are exhausted by it
(`TauCeti.exists_mem_range_singularChainFiltration_skeletalFiltration_arrow`). For the total
space of a fibration over a CW complex this is the filtration whose spectral sequence is the
Serre spectral sequence; the identification of its second page is not treated here.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorem 5.5.1.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Chapter 5.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Appendix, Proposition A.1.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w

namespace TauCeti

section FilteredSpace

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k) {Y : TopCat.{w}} {X : ℤ → Set Y}

/-- The stages of an increasing family of subsets, as a diagram of spaces. -/
private abbrev stageDiagram (hX : Monotone X) : ℤ ⥤ TopCat.{w} where
  obj q := (TopPair.ofSubset (X q)).snd
  map f := TopCat.ofHom (ContinuousMap.inclusion (hX f.le))

/-- The inclusions of the stages of an increasing family of subsets into the space. -/
private abbrev stageCocone (hX : Monotone X) : Cocone (stageDiagram hX) where
  pt := Y
  ι := { app q := (TopPair.ofSubset (X q)).map }

/-- **Singular chains are exhausted by an absorbing filtration.** If every compact subset of `Y`
lies in some member of an increasing family `X` of subsets, then every singular chain of `Y` is a
chain of some `X q`. -/
theorem exists_mem_range_singularChainFiltration_arrow (hX : Monotone X)
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (m : ℤ)
    (x : (((TopCat.toSSet.obj Y).chainComplex M).extend ComplexShape.embeddingDownNat).X m) :
    ∃ q, x ∈ LinearMap.range ((singularChainFiltration M X q).arrow.f m).hom := by
  by_cases hm : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = m
  · obtain ⟨n, hn⟩ := hm
    have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{w} k)) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    have hc := isColimitOfPreserves (HomologicalComplex.eval _ _ n)
      (isColimitOfPreserves ((SSet.chainComplexFunctor (ModuleCat.{w} k)).obj M)
        (isColimitMapCoconeToSSet (stageCocone hX)
          (fun q ↦ (TopPair.ofSubset (X q)).isEmbedding_map)
          (fun K hKc ↦ (hK K hKc).imp fun q hq y hy ↦ ⟨⟨y, hq hy⟩, rfl⟩)))
    obtain ⟨q, y, hy⟩ := Concrete.isColimit_exists_rep _ hc
      ((((TopCat.toSSet.obj Y).chainComplex M).extendXIso _ hn).hom x)
    -- The leg at `q` of the colimit cocone is, by definition of the image cocones, the map of
    -- singular chains in degree `n` induced by the inclusion of `X q`.
    change (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) M).f n y = _
      at hy
    refine ⟨q, (singularChainFiltrationIso M X q).inv.f m
      (((((TopCat.toSSet.obj (TopPair.ofSubset (X q)).snd).chainComplex M).extendXIso _ hn).inv
        y)), ?_⟩
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
      ← singularChainFiltrationIso_hom_comp_singularChainFiltrationι, Iso.inv_hom_id_assoc,
      singularChainFiltrationι_def, ← ModuleCat.comp_apply, extendMap_f _ _ hn]
    -- After cancelling the two degree-`n` identifications of the chains of `X q`, this is `hy`.
    -- The cancellation is stated through `congrArg`, since `Iso.inv_hom_id_assoc` does not match
    -- the composite syntactically: the source of `y` is written through the diagram.
    refine Eq.trans ?_ ((congrArg _ hy).trans (Iso.hom_inv_id_apply _ x))
    exact congrArg (fun z ↦ ((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map)
      M).f n ≫ (((TopCat.toSSet.obj Y).chainComplex M).extendXIso _ hn).inv) z)
      (Iso.inv_hom_id_apply _ y)
  · refine ⟨0, ?_⟩
    rw [(ModuleCat.isZero_iff_subsingleton.1
      (isZero_extend_X _ _ m fun n hn ↦ hm ⟨n, hn⟩)).elim x 0]
    exact Submodule.zero_mem _

/-- A graded piece of the filtration of singular chains has vanishing homology in degree `-n`
when the corresponding relative singular homology group vanishes. -/
private lemma isZero_homology_cokernel_of_isZero_singularHomology {a b : ℤ} (hab : X a ⊆ X b)
    {n : ℕ} {m : ℤ} (hm : m = -n) (h : IsZero ((TopPair.ofInclusion hab).singularHomology M n)) :
    IsZero ((cokernel (Subobject.ofLE _ _ (singularChainFiltration_mono M hab))).homology m) :=
  h.of_iso (HomologicalComplex.homologyMapIso (singularChainFiltrationCokernelIso M hab) m ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat hm.symm)

variable (hX : Monotone X) (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q)
include hK

/-- **The filtration of singular homology by an absorbing filtration is exhaustive.** If every
compact subset of `Y` lies in some `X q`, then every class of the abutment `Hₙ(Y)`
(`TauCeti.filteredSpaceAbutmentIso`) lies in some piece of its filtration, the image of
`Hₙ(X q)`. -/
theorem exists_mem_range_filteredSpace_abutmentFiltrationι {m : ℤ}
    (x : (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_singularChainFiltration M hX))).abutment m) :
    ∃ q, x ∈ LinearMap.range ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_singularChainFiltration M hX))).abutmentFiltrationι q m).hom :=
  CochainComplex.exists_mem_range_filtrationAbutmentFiltrationι _ _
    (exists_mem_range_singularChainFiltration_arrow M hX hK m) x

/-- **The filtration of singular homology reaches `Hₙ(Y)`.** If every compact subset of `Y` lies
in some `X q`, and the relative homology groups `Hₙ(X (i + 1), X i)` vanish for all `i ≥ b`, then
the `b`th piece of the filtration of the abutment `Hₙ(Y)` is everything: every class of `Hₙ(Y)`
comes from `Hₙ(X b)`. -/
theorem isIso_filteredSpace_abutmentFiltrationι {b : ℤ} (n : ℕ)
    (h : ∀ i, b ≤ i →
      IsZero ((TopPair.ofInclusion (hX (Int.le_add_one le_rfl : i ≤ i + 1))).singularHomology
        M n)) :
    IsIso ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_singularChainFiltration M hX))).abutmentFiltrationι b (-n)) :=
  CochainComplex.isIso_filtrationAbutmentFiltrationι_of_exhaustive _ _
    (exists_mem_range_singularChainFiltration_arrow M hX hK _)
    fun i hi ↦ isZero_homology_cokernel_of_isZero_singularHomology M _ rfl (h i hi)

/-- **Strong convergence of the spectral sequence of an absorbing filtration of a space.** Let
`pq = (p, q)` with `p + q = -n`. Suppose that every compact subset of `Y` lies in some `X i`, that
`X a = ∅` for some `a ≥ q - r + 2`, and that the relative homology groups
`Hₙ₊₁(X (i + 1), X i)` vanish for all `i ≥ q + r - 1`. Then the object at `(p, q)` on page `r ≥ 2`
is the graded piece `F_{q+1} H / F_q H` of the filtration of the abutment `Hₙ(Y)`. No finite
upper bound on the filtration is needed. -/
def filteredSpaceSpectralSequencePageXIsoGradedOfExhaustive {a : ℤ} (ha : X a = ∅) (r : ℤ)
    (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a) (n : ℕ) (hn : pq.1 + pq.2 = -n)
    (h : ∀ i, pq.2 + r - 1 ≤ i →
      IsZero ((TopPair.ofInclusion (hX (Int.le_add_one le_rfl : i ≤ i + 1))).singularHomology
        M (n + 1))) :
    ((filteredSpaceSpectralSequence M hX).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_singularChainFiltration M hX))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfExhaustive _ _ r hr pq
    (exists_mem_range_singularChainFiltration_arrow M hX hK _)
    ((singularChainFiltration M X _).isZero_homology_of_eq_bot
      (eq_bot_iff.2 ((monotone_singularChainFiltration M hX hra).trans
        (singularChainFiltration_eq_bot M ha).le)) _)
    fun i hi ↦ isZero_homology_cokernel_of_isZero_singularHomology M _ (by push_cast; lia)
      (h i hi)

end FilteredSpace

section SkeletalChains

open Topology

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k) {Y : TopCat.{w}} {B : Type*}
  [TopologicalSpace B] [T2Space B] (C : Set B) {D : Set B} [RelCWComplex C D] {p : Y → B}

/-- **Singular chains are exhausted by the skeletal filtration.** For a continuous map `p` from a
space `Y` into a relative CW complex, every singular chain of `Y` is a chain of the preimage
`p⁻¹(Bᵠ)` of some skeleton. The CW complex may have infinitely many cells and be
infinite-dimensional. -/
theorem exists_mem_range_singularChainFiltration_skeletalFiltration_arrow (hp : Continuous p)
    (hpC : ∀ y, p y ∈ C) (m : ℤ)
    (x : (((TopCat.toSSet.obj Y).chainComplex M).extend ComplexShape.embeddingDownNat).X m) :
    ∃ q, x ∈ LinearMap.range
      ((singularChainFiltration M (skeletalFiltration C p) q).arrow.f m).hom :=
  exists_mem_range_singularChainFiltration_arrow M (monotone_skeletalFiltration C p)
    (fun _ hK ↦ exists_subset_skeletalFiltration_of_isCompact C p hK hp.continuousOn
      fun y _ ↦ hpC y) m x

end SkeletalChains

end TauCeti
