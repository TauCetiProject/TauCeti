/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Resolution.Edge
import TauCeti.KnotTheory.Khovanov.Mark

/-!
# Reverse saddles and neck cutting

An unsigned resolution saddle followed by the reverse saddle acts by the sum of the `X`
actions at slots `0` and `2` of the changing crossing. On the two-circle side this is the
neck-cutting identity `Δm = X ⊗ id + id ⊗ X`; on the one-circle side it is the handle identity
`mΔ = 2X`. These equations hold on the actual indexed resolution tensors, retaining all other
circle factors, including individually labelled crossing-free circles.

The saddle also intertwines `X` at slot `0` with `X` at slot `2` on the opposite resolution.
These are the local algebraic identities used in the reverse-saddle homotopy for sliding a
mark through a crossing. No signed-cube homotopy is asserted here. Planarity is unnecessary
once the local edge is known to be a merge or split.

## References

* M. Khovanov, *Patterns in knot cohomology I*, Experiment. Math. 12 (2003), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

open Finset PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
  (R : Type u) [CommSemiring R]

/-- Merging two resolution circles and splitting them back is the sum of `X` on the two
original circles. Every unaffected circle factor is retained. -/
theorem resolutionSplitMap_resolutionMergeMap (hs : #(D.circlesAt s c) = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionSplitMap (fun j hj ↦ (hst j hj).symm) hc.symm hs R
        (D.resolutionMergeMap hst hc hs R x) =
      Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) x +
        Khovanov.circleX R (.inl ⟦D.crossing c 2⟧) x := by
  classical
  have hproj : D.resolutionSplitMap (fun j hj ↦ (hst j hj).symm) hc.symm hs R
      (D.resolutionMergeMap hst hc hs R x) =
        x * D.resolutionSplitMap (fun j hj ↦ (hst j hj).symm) hc.symm hs R 1 := by
    rw [resolutionSplitMap_def, resolutionMergeMap_def, ← mul_one
      (fiberwiseMul (A := fun _ ↦ R[ε]) _ x), Khovanov.fiberwiseSplit_fiberwiseMul_mul]
  rw [hproj, resolutionSplitMap_one, Khovanov.circleX_apply, Khovanov.circleX_apply,
    mul_comm x]
  exact NonUnitalNonAssocSemiring.right_distrib _ _ x

/-- Splitting a resolution circle and merging the two outputs back gives `2X` on the
original circle, with the identity on all other factors. -/
theorem resolutionMergeMap_resolutionSplitMap (ht : #(D.circlesAt t c) = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionMergeMap (fun j hj ↦ (hst j hj).symm) hc.symm ht R
        (D.resolutionSplitMap hst hc ht R x) =
      2 • Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) x := by
  classical
  have hts : ∀ j, j ≠ c → t j = s j := fun j hj ↦ (hst j hj).symm
  have hs := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hts hc.symm ht
  have hhandle :
      D.resolutionMergeMap (fun j hj ↦ (hst j hj).symm) hc.symm ht R
          (D.resolutionSplitMap hst hc ht R 1) =
        2 • singleAlgHom (A := fun _ : D.ResolvedCircle s ↦ R[ε])
          (.inl ⟦D.crossing c 0⟧) ε := by
    simp only [resolutionSplitMap_one, map_add, resolutionMergeMap_def,
      fiberwiseMul_singleAlgHom,
      (D.saddleResolvedCircleMap_eq_crossing_iff hts hs (.inl ⟦D.crossing c 0⟧)).2 (.inl rfl),
      (D.saddleResolvedCircleMap_eq_crossing_iff hts hs (.inl ⟦D.crossing c 2⟧)).2 (.inr rfl),
      two_smul]
  have hproj :
      D.resolutionMergeMap (fun j hj ↦ (hst j hj).symm) hc.symm ht R
          (D.resolutionSplitMap hst hc ht R x) =
        x * D.resolutionMergeMap (fun j hj ↦ (hst j hj).symm) hc.symm ht R
          (D.resolutionSplitMap hst hc ht R 1) := by
    simp only [resolutionMergeMap_def, resolutionSplitMap_def]
    simpa only [fiberwiseMul_id, AlgHom.id_apply] using
      Khovanov.fiberwiseMul_fiberwiseSplit
        (D.saddleResolvedCircleMap_surjective hts hs)
        (g := D.saddleResolvedCircleMap hts hs) (h := id) rfl x
  rw [hproj, hhandle]
  simp only [two_smul, Khovanov.circleX_apply, mul_comm x]
  exact NonUnitalNonAssocSemiring.right_distrib _ _ x

variable (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)

/-- A saddle followed by its reverse is the sum of the two local dot actions. This single
formula includes both `Δm` on two circles and `mΔ` on one circle. -/
theorem resolutionEdgeMap_reverse_resolutionEdgeMap
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionEdgeMap (fun j hj ↦ (hst j hj).symm) hc.symm h.symm R
        (D.resolutionEdgeMap hst hc h R x) =
      Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) x +
        Khovanov.circleX R (.inl ⟦D.crossing c 2⟧) x := by
  rcases h with hs | ht
  · rw [resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ _ hs,
      resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ _ hs]
    exact D.resolutionSplitMap_resolutionMergeMap hst hc R hs x
  · have hs := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two
      (fun j hj ↦ (hst j hj).symm) hc.symm ht
    rw [resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ _ ht,
      resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ _ ht]
    rw [AlgHom.toLinearMap_apply, D.resolutionMergeMap_resolutionSplitMap hst hc R ht,
      ((D.card_circlesAt_eq_one_iff s c).mp hs).symm, two_smul]

/-- A resolution saddle carries `X` at slot `0` to `X` at slot `2` of the same crossing
on the other resolution. This is the dot-intertwining identity for a mark slide. -/
theorem resolutionEdgeMap_circleX_crossing
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionEdgeMap hst hc h R (Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) x) =
      Khovanov.circleX R (.inl ⟦D.crossing c 2⟧) (D.resolutionEdgeMap hst hc h R x) := by
  rcases h with hs | ht
  · have ht := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs
    simpa only [Mark.resolvedCircle_onArc, ((D.card_circlesAt_eq_one_iff t c).mp ht).symm] using
      D.resolutionEdgeMap_circleX (Mark.onArc D (D.crossing c 0)) hst hc R (Or.inl hs) x
  · have hs := D.card_circlesAt_eq_one_of_card_circlesAt_eq_two
      (fun j hj ↦ (hst j hj).symm) hc.symm ht
    simpa only [Mark.resolvedCircle_onArc, (D.card_circlesAt_eq_one_iff s c).mp hs] using
      D.resolutionEdgeMap_circleX (Mark.onArc D (D.crossing c 2)) hst hc R (Or.inr ht) x

end TauCeti.PDCode
