/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.DirectedUnion
public import TauCeti.CategoryTheory.Limits.Constructions.EventuallyConstant
public import TauCeti.Topology.CWComplex.Classical.CompactSupport

/-!
# Twisted homology of a CW complex from its skeleta

Let `C` be a relative CW complex in `X` and `L` a local coefficient system on `X`. A compact
subset of `C` lies in a skeleton (`TauCeti.exists_subset_skeletonLT_of_isCompact`), so twisted
singular homology has compact supports along the skeleta: `Hₖ(C; L)` is the colimit of the twisted
homology groups `Hₖ(skeletonLT C n; L)`, with `L` restricted to each skeleton
(`TauCeti.isColimitSkeletonTwistedHomologyCocone`).

Attaching the cells of dimension `n` leaves twisted homology unchanged in degrees `k` with
`k ≠ n` and `k + 1 ≠ n`, since the relative groups of the pair of consecutive skeleta vanish
outside degree `n` (`TauCeti.isZero_twistedHomology_skeletonPair_of_ne`). So the diagram of the
`Hₖ(skeletonLT C n; L)` is constant from `n = k + 2` on, and the inclusion of the skeleton
`skeletonLT C m` into the complex induces an isomorphism on `Hₖ` for `k + 2 ≤ m`
(`TauCeti.isIso_homologyMap_subsetTwistedChainComplexMap_skeletonLT`). No bound on the dimension
of `C` is needed. For constant coefficients this is
`TauCeti.isIso_homologyMap_skeletonBasePairToComplex_fst`.

This is the input that identifies homology of an infinite-dimensional CW complex with local
coefficients with the homology of its cellular chain complex with local coefficients, for
instance for the local system of fibre homology of a fibration over a CW complex.

## Main results

* `TauCeti.isColimitSkeletonTwistedHomologyCocone`: `Hₖ(C; L)` is the colimit of the twisted
  homology of the skeleta.
* `TauCeti.isIso_homologyMap_subsetTwistedChainComplexMap_skeletonLT_succ`: attaching cells of
  dimension `n` leaves `Hₖ(-; L)` unchanged for `k ≠ n`, `k + 1 ≠ n`.
* `TauCeti.isIso_homologyMap_subsetTwistedChainComplexMap_skeletonLT`: the inclusion of the
  skeleton `skeletonLT C m` induces an isomorphism on `Hₖ(-; L)` for `k + 2 ≤ m`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Lemma 2.34, Section 3.H, and Proposition A.1 of
  the Appendix.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe u v w

namespace TauCeti

open LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of X))

/-- The cocone of twisted chain complexes of the skeleta `skeletonLT C n` of a relative CW
complex, with `L` restricted to each skeleton, over the twisted chains of the complex. -/
abbrev skeletonTwistedChainComplexCocone :=
  subsetTwistedChainComplexCocone L (U := fun n : ℕ ↦ (skeletonLT C (n : ℕ∞) : Set X))
    (fun _ _ h ↦ skeletonLT_mono (mod_cast h)) fun n ↦ (skeletonLT C (n : ℕ∞)).subset_complex

/-- **Twisted homology of a CW complex is the colimit over its skeleta.** For a relative CW
complex `C` and a local coefficient system `L` on the ambient space, `Hₖ(C; L)` is the colimit of
the twisted homology groups `Hₖ(skeletonLT C n; L)` under the maps induced by the inclusions. -/
def isColimitSkeletonTwistedHomologyCocone (k : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor _ _ k).mapCocone
      (skeletonTwistedChainComplexCocone C L)) :=
  isColimitSubsetTwistedHomologyMapCocone L _ _
    (fun _ hK hKC ↦ exists_subset_skeletonLT_of_isCompact hK hKC) k

/-- **Attaching cells of one dimension in twisted homology.** The inclusion
`skeletonLT C n ⊆ skeletonLT C (n + 1)` induces an isomorphism on twisted homology in every degree
`k` with `k ≠ n` and `k + 1 ≠ n`. -/
theorem isIso_homologyMap_subsetTwistedChainComplexMap_skeletonLT_succ {n k : ℕ} (hk : k ≠ n)
    (hk' : k + 1 ≠ n) :
    IsIso (HomologicalComplex.homologyMap
      (subsetTwistedChainComplexMap L (skeletonLT_subset_skeletonLT_succ C n)) k) := by
  -- The map is a change of coefficients followed by the map of the subspace of the pair of
  -- consecutive skeleta in its long exact sequence. The latter is an isomorphism because the
  -- relative groups in degrees `k` and `k + 1` vanish.
  set L' := (LocalCoefficientSystem.pullback
    (X := TopCat.of ↥(skeletonLT C ((n + 1 : ℕ) : ℕ∞))) (ContinuousMap.subtypeVal _)).obj L
  have : Mono (twistedHomologyMap (skeletonPair C n).map L' k) :=
    ((skeletonPair C n).twistedHomology_exact_subspace L' (k + 1) k).mono_g
      ((isZero_twistedHomology_skeletonPair_of_ne C hk' L').eq_of_src _ _)
  have : Epi (twistedHomologyMap (skeletonPair C n).map L' k) :=
    ((skeletonPair C n).twistedHomology_exact_space L' k).epi_f
      ((isZero_twistedHomology_skeletonPair_of_ne C hk L').eq_of_tgt _ _)
  have hP : IsIso (twistedHomologyMap (skeletonPair C n).map L' k) := isIso_of_mono_of_epi _
  let e := (pullbackCompIso
    (TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_subset_skeletonLT_succ C n))).hom
    (TopCat.ofHom (ContinuousMap.subtypeVal _)).hom).app L
  -- The map of the subspace of the pair of consecutive skeleta is the inclusion.
  have hmap : TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_subset_skeletonLT_succ C n)) =
      (skeletonPair C n).map := rfl
  rw [← hmap] at hP
  -- The two factors meet only up to unfolding the pulled-back coefficient systems, so their
  -- quasi-isomorphism instances are supplied by name.
  rw [subsetTwistedChainComplexMap_def]
  exact (quasiIsoAt_iff_isIso_homologyMap _ k).1 (quasiIsoAt_comp _ _ k
    (hφ := quasiIsoAt_of_isIso (twistedChainComplexCoefficientMap e.hom) k)
    (hφ' := (quasiIsoAt_iff_isIso_homologyMap _ k).2 hP))

/-- **Twisted homology of a relative CW complex from a skeleton.** For `k + 2 ≤ m`, the inclusion
of the skeleton `skeletonLT C m` into the complex induces an isomorphism
`Hₖ(skeletonLT C m; L) ≅ Hₖ(C; L)`, with no bound on the dimension of the complex. -/
theorem isIso_homologyMap_subsetTwistedChainComplexMap_skeletonLT {m k : ℕ} (hk : k + 2 ≤ m) :
    IsIso (HomologicalComplex.homologyMap
      (subsetTwistedChainComplexMap L (skeletonLT C (m : ℕ∞)).subset_complex) k) := by
  -- From the skeleton `skeletonLT C m` on, the diagram of homology groups in degree `k` is
  -- constant, so the colimit over the skeleta is attained there.
  have hconst : (subsetTwistedChainComplexDiagram L
      (U := fun n : ℕ ↦ (skeletonLT C (n : ℕ∞) : Set X)) (fun _ _ h ↦ skeletonLT_mono (mod_cast h))
      ⋙ HomologicalComplex.homologyFunctor _ _ k).IsEventuallyConstantFrom m :=
    -- The diagram sends `j ≤ j + 1` to the map induced by the inclusion of consecutive skeleta.
    Functor.isEventuallyConstantFrom_of_isIso_map_succ fun j hj ↦
      isIso_homologyMap_subsetTwistedChainComplexMap_skeletonLT_succ C L (by lia) (by lia)
  exact hconst.isIso_ι_of_isColimit (isColimitSkeletonTwistedHomologyCocone C L k)

end TauCeti
