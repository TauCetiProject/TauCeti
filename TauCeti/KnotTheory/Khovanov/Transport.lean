/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Resolution.Split
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Transport

/-!
# Transport of resolution saddle maps

The merge and split maps on actual resolved-circle tensors commute with transport of the
smoothed diagrams. The smoothing equivalences at the two endpoints must use the same
half-edge bijection and the same bijection of labelled isolated circles. This includes native
relabellings, slot rotations, mirror with complemented states, and isolated-circle permutations.
The resulting squares retain all factors, including the circles disjoint from the saddle.

These are unsigned identities over every commutative semiring. Cube-order signs belong to the
signed totalization, while circle reindexing contributes no sign. The combinatorial square is
`TauCeti.PDCode.SmoothingEquiv.resolvedCircleCongr_saddleResolvedCircleMap`; multiplication and
the adjoint split transport along that square by their existing composition laws.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
-/

public section

open PiTensorProduct DualNumber

namespace TauCeti.PDCode.SmoothingEquiv

variable {n m : ℕ} {D : PDCode n} {D' : PDCode m}
  {s t : Fin n → Bool} {s' t' : Fin m → Bool} {c : Fin n} {c' : Fin m}
  (es : D.SmoothingEquiv s D' s') (et : D.SmoothingEquiv t D' t')
  (hhalf : es.halfEdgeEquiv = et.halfEdgeEquiv)
  (hisolated : es.crossinglessEquiv = et.crossinglessEquiv)
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
  (hst' : ∀ j, j ≠ c' → s' j = t' j) (hc' : s' c' ≠ t' c')
  (R : Type*) [CommSemiring R]

include hhalf hisolated

/-- Reindexing the source and target circles commutes with an actual resolution merge.
The circle bijections retain every isolated-circle label. -/
theorem reindex_resolutionMergeMap
    (hs : (D.circlesAt s c).card = 2) (hs' : (D'.circlesAt s' c').card = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    reindex R (fun _ ↦ R[ε]) et.resolvedCircleCongr
        (D.resolutionMergeMap hst hc hs R x) =
      D'.resolutionMergeMap hst' hc' hs' R
        (reindex R (fun _ ↦ R[ε]) es.resolvedCircleCongr x) := by
  have hmap := funext (es.resolvedCircleCongr_saddleResolvedCircleMap et hhalf hisolated
    hst hst' (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs)
      (D'.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst' hc' hs'))
  rw [resolutionMergeMap_def, resolutionMergeMap_def]
  exact reindex_fiberwiseMul _ _ hmap x

/-- Reindexing the source and target circles commutes with an actual resolution split.
This uses the same endpoint transports as the reverse merge. -/
theorem reindex_resolutionSplitMap
    (ht : (D.circlesAt t c).card = 2) (ht' : (D'.circlesAt t' c').card = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    reindex R (fun _ ↦ R[ε]) et.resolvedCircleCongr
        (D.resolutionSplitMap hst hc ht R x) =
      D'.resolutionSplitMap hst' hc' ht' R
        (reindex R (fun _ ↦ R[ε]) es.resolvedCircleCongr x) := by
  have hmap := et.resolvedCircleCongr_saddleResolvedCircleMap es hhalf.symm hisolated.symm
    (fun j hj ↦ (hst j hj).symm) (fun j hj ↦ (hst' j hj).symm)
    (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm) hc.symm ht)
    (D'.card_circlesAt_eq_one_of_card_circlesAt_eq_two
      (fun j hj ↦ (hst' j hj).symm) hc'.symm ht')
  rw [resolutionSplitMap_def, resolutionSplitMap_def]
  exact Khovanov.reindex_fiberwiseSplit _ _ (funext hmap) x

end TauCeti.PDCode.SmoothingEquiv
