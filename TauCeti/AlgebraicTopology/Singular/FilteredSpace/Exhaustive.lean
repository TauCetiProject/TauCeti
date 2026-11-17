/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# Exhaustive filtrations of a space

Let `X : ℤ → Set Y` be an increasing family of subsets of a space `Y` that absorbs compact sets:
every compact subset of `Y` lies in some `X q`. The family need not reach `Y` at any finite
stage. The basic example is the filtration of a space mapping to an infinite-dimensional CW
complex by the preimages of the skeleta
(`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Skeleton`).

A singular simplex has compact image, so it lies in some `X q`. Hence, with coefficients in a
module `M`, every singular chain of `Y` lies in some stage of the filtration of the singular
chains by those of the `X q` (`TauCeti.exists_mem_range_singularChainFiltration_arrow`). This is
the exhaustiveness hypothesis of the convergence theorems for filtered complexes in
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive`, which therefore apply to
`TauCeti.filteredSpaceSpectralSequence`:

* the filtration of the abutment `Hₙ(Y)` is exhaustive
  (`TauCeti.exists_mem_range_filteredSpaceAbutmentFiltrationι`);
* if the relative homology `Hₙ(X (i + 1), X i)` vanishes for all `i ≥ b`, the `b`th piece of the
  filtration of `Hₙ(Y)` is everything
  (`TauCeti.isIso_filteredSpaceAbutmentFiltrationι_of_exhaustive`);
* if `X a = ∅` and the relative homology `H_{1-(p+q)}(X (i + 1), X i)` vanishes for all large
  `i`, the spectral sequence converges strongly: on a late enough page the object at `(p, q)` is
  the graded piece `F_{q+1} H / F_q H` of `H_{-(p+q)}(Y)`
  (`TauCeti.filteredSpaceSpectralSequencePageXIsoGradedOfExhaustive`).

The filtration of the abutment vanishes at a stage `X a = ∅`, by
`CochainComplex.isZero_filtrationAbutmentFiltration` and
`TauCeti.singularChainFiltration_eq_bot`, so in each degree it is finite, exhaustive and
separated as soon as the graded pieces vanish from some stage on.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.6 and Section 5.1, the spectral sequence of the filtration of a total space by the
  preimages of the skeleta of a CW base.
* A. Hatcher, *Algebraic Topology*, Section 3.3, Proposition 3.33 and its proof (a singular
  chain has compact image, so it lies in some member of a directed family of subspaces absorbing
  compact sets).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w

namespace TauCeti

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k) {Y : TopCat.{w}} {X : ℤ → Set Y}

/-- The subspaces `X q` of a monotone family, with their inclusions into `Y`, as a cocone over the
diagram indexed by `ℤ`. -/
private def filteredSpaceCocone (hX : Monotone X) :
    Cocone ({ obj q := TopCat.of (X q)
              map f := TopCat.ofHom (ContinuousMap.inclusion (hX f.le)) } : ℤ ⥤ TopCat.{w}) where
  pt := Y
  ι := { app q := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

/-- **Singular chains of an exhaustive filtration of a space.** If every compact subset of `Y` lies
in some `X q`, every singular chain of `Y`, in each degree of the reindexed chain complex, lies in
some stage of the filtration by the singular chains of the `X q`. -/
theorem exists_mem_range_singularChainFiltration_arrow (hX : Monotone X)
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (m : ℤ)
    (x : (((TopCat.toSSet.obj Y).chainComplex M).extend ComplexShape.embeddingDownNat).X m) :
    ∃ q, x ∈ LinearMap.range ((singularChainFiltration M X q).arrow.f m).hom := by
  by_cases hm : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = m
  · obtain ⟨n, hn⟩ := hm
    have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{w} k)) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    -- In degree `n` the singular chains of `Y` are the filtered colimit of those of the `X q`,
    -- because a singular simplex has compact image.
    have hc := isColimitOfPreserves
      ((SSet.chainComplexFunctor (ModuleCat.{w} k)).obj M ⋙ HomologicalComplex.eval _ _ n)
      (isColimitMapCoconeToSSet (filteredSpaceCocone hX)
        (fun q ↦ Topology.IsEmbedding.subtypeVal)
        (fun K hK' ↦ (hK K hK').imp fun q hq y hy ↦ ⟨⟨y, hq hy⟩, rfl⟩))
    obtain ⟨q, y, hy⟩ := Concrete.isColimit_exists_rep _ hc
      ((((TopCat.toSSet.obj Y).chainComplex M).extendXIso _ hn).hom x)
    -- Transport the preimage `y` from degree `n` to degree `m = -n` of the extended complexes.
    obtain ⟨z, rfl⟩ := (mem_range_extendMap_f_iff _
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset (X q)).map) M) hn x).2 ⟨y, hy⟩
    refine ⟨q, (singularChainFiltrationIso M X q).inv.f m z, ?_⟩
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
      ← singularChainFiltrationIso_hom_comp_singularChainFiltrationι, Iso.inv_hom_id_assoc,
      singularChainFiltrationι_def]
    -- The two sides differ only in the coercion of a linear map to a function.
    rfl
  · push Not at hm
    refine ⟨0, ?_⟩
    rw [(ModuleCat.isZero_iff_subsingleton.1 (isZero_extend_X _ _ m hm)).elim x 0]
    exact zero_mem _

variable (hX : Monotone X)

/-- **The filtration of the abutment of an exhaustive filtration of a space is exhaustive**: every
class of `Hₙ(Y)` lies in some piece of its filtration. -/
theorem exists_mem_range_filteredSpaceAbutmentFiltrationι
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) {n : ℤ}
    (x : (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_singularChainFiltration M hX))).abutment n) :
    ∃ q, x ∈ LinearMap.range ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_singularChainFiltration M hX))).abutmentFiltrationι q n).hom :=
  CochainComplex.exists_mem_range_filtrationAbutmentFiltrationι _ _
    (exists_mem_range_singularChainFiltration_arrow M hX hK n) x

/-- **The filtration of the abutment reaches `Hₙ(Y)`.** For an exhaustive filtration of a space, if
the relative homology `Hₙ(X (i + 1), X i)` vanishes for every `i ≥ b`, then the `b`th piece of the
filtration of `Hₙ(Y)` is everything. -/
theorem isIso_filteredSpaceAbutmentFiltrationι_of_exhaustive
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) {b : ℤ} (n : ℕ)
    (hvanish : ∀ i, b ≤ i →
      IsZero ((TopPair.ofInclusion (hX (Int.le_add_one le_rfl) : X i ⊆ X (i + 1))).singularHomology
        M n)) :
    IsIso ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_singularChainFiltration M hX))).abutmentFiltrationι b (-n)) :=
  CochainComplex.isIso_filtrationAbutmentFiltrationι_of_exhaustive _ _
    (exists_mem_range_singularChainFiltration_arrow M hX hK _) fun i hi ↦
      isZero_homology_cokernel_singularChainFiltration M _ _ fun n' hn' ↦ by
        obtain rfl : n' = n := by lia
        exact hvanish i hi

/-- **Strong convergence of the spectral sequence of an exhaustive filtration of a space.** Suppose
that every compact subset of `Y` lies in some `X q` and that `X a = ∅`. Let `pq = (p, q)` and
`r ≥ 2` with `q - r + 2 ≤ a`, and suppose that the relative homology `Hₙ(X (i + 1), X i)` vanishes
for every `i ≥ q + r - 1`, where `p + q - 1 = -n`. Then the object at `(p, q)` on page `r` is the
graded piece `F_{q+1} H / F_q H` of the filtration of the abutment in degree `p + q`, which is
`H_{-(p+q)}(Y)` by `TauCeti.filteredSpaceAbutmentIso`. -/
def filteredSpaceSpectralSequencePageXIsoGradedOfExhaustive
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) {a : ℤ} (ha : X a = ∅)
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hvanish : ∀ i, pq.2 + r - 1 ≤ i → ∀ n : ℕ, pq.1 + pq.2 - 1 = -n →
      IsZero ((TopPair.ofInclusion (hX (Int.le_add_one le_rfl) : X i ⊆ X (i + 1))).singularHomology
        M n)) :
    ((filteredSpaceSpectralSequence M hX).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_singularChainFiltration M hX))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfExhaustive _ _ r hr pq
    (exists_mem_range_singularChainFiltration_arrow M hX hK _)
    ((singularChainFiltration M X _).isZero_homology_of_eq_bot
      (singularChainFiltration_eq_bot M (Set.subset_empty_iff.1 (ha ▸ hX hra))) _)
    fun i hi ↦ isZero_homology_cokernel_singularChainFiltration M _ _ (hvanish i hi)

end TauCeti
