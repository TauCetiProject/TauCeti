/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Resolution.Edge
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Mark
import TauCeti.KnotTheory.Khovanov.Mark.Basic

/-!
# Reverse saddles and neck cutting

An unsigned resolution saddle followed by the reverse saddle acts by the sum of the `X`
actions at slots `0` and `2` of the changing crossing, and therefore by `X_p + X_q` for any
opposite arc marks `p` and `q` at the crossing
(`TauCeti.PDCode.resolutionEdgeMap_comp_resolutionEdgeMap_eq_circleX_add_circleX`). On the
two-circle side this is the neck-cutting identity `Δm = X ⊗ id + id ⊗ X`; on the one-circle side it
is the handle identity `mΔ = 2X`. These equations hold on the actual indexed resolution tensors,
retaining all other circle factors, including individually labelled crossing-free circles.

Every saddle at `c` also intertwines `X` at any slot `k` of `c` with `X` at
`oppositeCrossingSlot k` on the opposite resolution
(`TauCeti.PDCode.resolutionEdgeMap_circleX_oppositeCrossingSlot`). These are the local algebraic
identities used in the reverse-saddle homotopy for sliding a mark through a crossing. No
signed-cube homotopy is asserted here. Planarity is unnecessary once the local edge is known to be
a merge or split.

## References

* M. Khovanov, *Patterns in knot cohomology I*, Experiment. Math. 12 (2003), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

open Finset PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

/-- In any state `s`, the sum of the `X` actions at the two opposite slots `k` and
`oppositeCrossingSlot k` of `c` equals the sum of the `X` actions on the circles through slots `0`
and `2` of `c`. -/
theorem circleX_resolvedCircle_onArc_add_oppositeCrossingSlot {n : ℕ} (D : PDCode n)
    (R : Type u) [CommSemiring R] (s : Fin n → Bool) (c : Fin n) (k : Fin 4) :
    Khovanov.circleX R ((Mark.onArc D (D.crossing c k)).resolvedCircle s) +
      Khovanov.circleX R
        ((Mark.onArc D (D.crossing c (oppositeCrossingSlot k))).resolvedCircle s) =
    Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) +
      Khovanov.circleX R (.inl ⟦D.crossing c 2⟧) := by
  rw [Mark.resolvedCircle_onArc, Mark.resolvedCircle_onArc]
  rcases CrossingCircle.mk_crossing_oppositeCrossingSlot_pair (D := D) (s := s) c k with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, add_comm]

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

/-- Composing a saddle map at `c` with its reverse equals `X_p + X_q` for the two opposite arc marks
at any slot `k` of `c`. -/
theorem resolutionEdgeMap_comp_resolutionEdgeMap_eq_circleX_add_circleX (k : Fin 4) :
    D.resolutionEdgeMap (fun j hj ↦ (hst j hj).symm) hc.symm h.symm R ∘ₗ
        D.resolutionEdgeMap hst hc h R =
      Khovanov.circleX R ((Mark.onArc D (D.crossing c k)).resolvedCircle s) +
        Khovanov.circleX R
          ((Mark.onArc D (D.crossing c (oppositeCrossingSlot k))).resolvedCircle s) := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, D.resolutionEdgeMap_reverse_resolutionEdgeMap hst hc R h x,
    ← LinearMap.add_apply, D.circleX_resolvedCircle_onArc_add_oppositeCrossingSlot R s c k]

/-- **Every saddle at `c` intertwines `X` on opposite slots of `c`.** Because one of `s` or `t` has
a single circle passing through `c` (on which `k` and `oppositeCrossingSlot k` select the same
circle), applying `X` at slot `k` before the saddle equals applying `X` at `oppositeCrossingSlot k`
after it. -/
theorem resolutionEdgeMap_circleX_oppositeCrossingSlot (k : Fin 4)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionEdgeMap hst hc h R
        (Khovanov.circleX R ((Mark.onArc D (D.crossing c k)).resolvedCircle s) x) =
      Khovanov.circleX R
        ((Mark.onArc D (D.crossing c (oppositeCrossingSlot k))).resolvedCircle t)
        (D.resolutionEdgeMap hst hc h R x) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · have ht1 : #(D.circlesAt t c) = 1 :=
      D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs
    rw [← Mark.resolvedCircle_onArc_crossing_eq_oppositeCrossingSlot_of_card_circlesAt_eq_one
      D ht1 k]
    exact D.resolutionEdgeMap_circleX (Mark.onArc D (D.crossing c k)) hst hc R h x
  · have ht : #(D.circlesAt t c) = 2 := h.resolve_left hs
    have hs1 : #(D.circlesAt s c) = 1 :=
      D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm) hc.symm ht
    rw [Mark.resolvedCircle_onArc_crossing_eq_oppositeCrossingSlot_of_card_circlesAt_eq_one
      D hs1 k]
    exact D.resolutionEdgeMap_circleX
      (Mark.onArc D (D.crossing c (oppositeCrossingSlot k))) hst hc R h x

end TauCeti.PDCode
