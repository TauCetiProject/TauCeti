/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Reidemeister.Circle
public import TauCeti.KnotTheory.PDCode.Reidemeister.One.Basic
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Transport
public import TauCeti.KnotTheory.PDCode.VertexResolution

/-!
# Resolving the crossing of a first Reidemeister move

The crossing `Fin.last n` added by the first Reidemeister move has two resolutions
(`TauCeti.PDCode.resolveCrossing`). One runs along the kink and gives back the old diagram; the
other cuts the loop of the kink off and gives the old diagram together with one crossing-free
circle. For the kink `TauCeti.PDCode.reidemeisterOne D h b` inserted into an arc of `D`, the
loop is cut off by the smoothing `b`:

* `(D.reidemeisterOne h b).resolveCrossing (Fin.last n) (!b)` is `D`;
* `(D.reidemeisterOne h b).resolveCrossing (Fin.last n) b` is `D.adjoinCircle`.

For the isolated kink `TauCeti.PDCode.adjoinKink D b`, the smoothing `!b` leaves one
crossing-free circle and the smoothing `b` two:

* `(D.adjoinKink b).resolveCrossing (Fin.last n) (!b)` is `D.adjoinCircle`;
* `(D.adjoinKink b).resolveCrossing (Fin.last n) b` is `D.adjoinCircle.adjoinCircle`.

In each case the half-edges of the resolution are labelled by their positions, so the equality
is with the relabelling of the old diagram along `D.halfEdge.symm`, which sends the half-edge in
slot `k` of crossing `i` to the position of that slot. The crossings keep their order, and the
crossing-free circles detached from the kink come after those of `D`.

The resulting identifications of all smoothings (`TauCeti.PDCode.ResolutionEquiv`) transport the
cubes of resolutions and the Khovanov complexes of the two resolutions to those of `D` and of
`D` with adjoined circles. Together with the skein mapping cone of the crossing, this is the
starting point of the invariance of Khovanov homology under the first Reidemeister move.

## Main definitions

* `TauCeti.PDCode.ResolutionEquiv.resolveCrossingReidemeisterOneNot`,
  `TauCeti.PDCode.ResolutionEquiv.resolveCrossingReidemeisterOneSelf`,
  `TauCeti.PDCode.ResolutionEquiv.resolveCrossingAdjoinKinkNot`,
  `TauCeti.PDCode.ResolutionEquiv.resolveCrossingAdjoinKinkSelf`: the corresponding
  identifications of all smoothings.

## Main results

* `TauCeti.PDCode.detachedCircleCount_reidemeisterOne_last`,
  `TauCeti.PDCode.detachedCircleCount_adjoinKink_last`: the circles detached by each smoothing
  of the new crossing.
* `TauCeti.PDCode.resolveCrossing_reidemeisterOne_last_not`,
  `TauCeti.PDCode.resolveCrossing_reidemeisterOne_last_self`,
  `TauCeti.PDCode.resolveCrossing_adjoinKink_last_not`,
  `TauCeti.PDCode.resolveCrossing_adjoinKink_last_self`: the resolutions of the new crossing.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §5.2
  (invariance under the first Reidemeister move).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.5.
-/

public section

namespace TauCeti.PDCode

open Equiv

variable {n : ℕ} (D : PDCode n) (h : Fin (4 * n)) (b : Bool)

/-! ### The kink inserted into an arc -/

section ReidemeisterOne

private theorem reidemeisterOne_smoothing_last (t : Bool) :
    (bif t then (D.reidemeisterOne h b).overPair (Fin.last n)
      else !(D.reidemeisterOne h b).overPair (Fin.last n)) = (t == b) := by
  cases t <;> cases b <;> simp

/-- **The circles detached from a kink.** Resolving the crossing of a kink inserted into an arc
detaches the loop of the kink exactly for the smoothing `b`. -/
theorem detachedCircleCount_reidemeisterOne_last (t : Bool) :
    (D.reidemeisterOne h b).detachedCircleCount (Fin.last n) t = if t = b then 1 else 0 := by
  rw [detachedCircleCount_eq, reidemeisterOne_smoothing_last]
  simp only [crossing_apply, crossingSlotEquiv_succ_last, reidemeisterOne_crossing_last,
    reidemeisterOne_edgePair_inr_zero, reidemeisterOne_edgePair_inr_two,
    EmbeddingLike.apply_eq_iff_eq]
  cases t <;> cases b <;> simp [swap_apply_of_ne_of_ne]

/-- An arc of `D` is an arc of each resolution of the kink: the arc cut open by the kink is
closed up again through the smoothing of the new crossing, directly when the smoothing cuts off
the loop, and round the loop otherwise. -/
private theorem resolveCrossing_reidemeisterOne_edgePair (t : Bool) {i j : Fin n} {k l : Fin 4}
    (hij : D.edgePair.val (D.crossing i k) = D.crossing j l) :
    ((D.reidemeisterOne h b).resolveCrossing (Fin.last n) t).edgePair.val
      (crossingSlotEquiv n (i, k)) = crossingSlotEquiv n (j, l) := by
  set D' := D.reidemeisterOne h b
  have hσ := D.reidemeisterOne_smoothing_last h b t
  have hc (i : Fin n) (k : Fin 4) :
      D'.crossing ((Fin.last n).succAbove i) k = halfEdgeSuccEquiv n (.inl (D.crossing i k)) := by
    simp [D']
  have hl (k : Fin 4) : D'.crossing (Fin.last n) k = halfEdgeSuccEquiv n (.inr k) := by
    simp [D']
  by_cases hh : D.crossing i k = h
  · -- The arc enters the kink at slot `0` and leaves it at slot `1`.
    have h₁ : D'.edgePair.val (D'.crossing ((Fin.last n).succAbove i) k) =
        D'.crossing (Fin.last n) 0 := by
      rw [hc, hh, hl, reidemeisterOne_edgePair_inl_self]
    have h₂ : D'.edgePair.val (D'.crossing (Fin.last n) 1) =
        D'.crossing ((Fin.last n).succAbove j) l := by
      rw [hl, reidemeisterOne_edgePair_inr_one, ← hh, hij, hc]
    cases ht : (t == b)
    · -- Round the loop: slot `0`, slot `3`, slot `2`, slot `1`.
      refine D'.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing_twice (Fin.last n) t
        (m' := 2) h₁ ?_ ?_
      · rw [hσ, ht]
        simp [D', swap_apply_of_ne_of_ne]
      · rw [hσ, ht]
        simpa [swap_apply_of_ne_of_ne] using h₂
    · refine D'.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing (Fin.last n) t h₁ ?_
      rw [hσ, ht]
      simpa [swap_apply_of_ne_of_ne] using h₂
  by_cases hh' : D.crossing i k = D.edgePair.val h
  · -- The arc enters the kink at slot `1` and leaves it at slot `0`.
    have h₁ : D'.edgePair.val (D'.crossing ((Fin.last n).succAbove i) k) =
        D'.crossing (Fin.last n) 1 := by
      rw [hc, hh', hl, reidemeisterOne_edgePair_inl_edgePair]
    have h₂ : D'.edgePair.val (D'.crossing (Fin.last n) 0) =
        D'.crossing ((Fin.last n).succAbove j) l := by
      have hjl : h = D.crossing j l := by rw [← hij, hh', D.edgePair.apply_apply]
      rw [hl, reidemeisterOne_edgePair_inr_zero, hjl, hc]
    cases ht : (t == b)
    · -- Round the loop: slot `1`, slot `2`, slot `3`, slot `0`.
      refine D'.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing_twice (Fin.last n) t
        (m' := 3) h₁ ?_ ?_
      · rw [hσ, ht]
        simp [D', swap_apply_of_ne_of_ne]
      · rw [hσ, ht]
        simpa [swap_apply_of_ne_of_ne] using h₂
    · refine D'.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing (Fin.last n) t h₁ ?_
      rw [hσ, ht]
      simpa [swap_apply_of_ne_of_ne] using h₂
  -- The arc avoids the kink.
  refine D'.resolveCrossing_edgePair_val_of_edgePair_val_eq (Fin.last n) t ?_
  rw [hc, reidemeisterOne_edgePair_inl_of_ne _ _ _ hh hh', hij, hc]

/-- **Resolving a kink along it.** Resolving the crossing of the kink inserted into an arc of `D`
by the smoothing `!b`, which runs along the kink, gives back `D`, with its half-edges labelled
by their positions. -/
theorem resolveCrossing_reidemeisterOne_last_not :
    (D.reidemeisterOne h b).resolveCrossing (Fin.last n) (!b) =
      D.relabel D.halfEdge.symm (Equiv.refl _) := by
  apply PDCode.ext
  · rw [resolveCrossing_halfEdge, relabel_halfEdge_symm_halfEdge]
  · exact D.eq_relabel_edgePair_of_crossing fun _ _ _ _ ↦
      D.resolveCrossing_reidemeisterOne_edgePair h b _
  · simp [detachedCircleCount_reidemeisterOne_last]
  · funext i
    simp [Fin.succAbove_last]

/-- **Cutting off the loop of a kink.** Resolving the crossing of the kink inserted into an arc of
`D` by the smoothing `b`, which cuts off the loop of the kink, gives `D` together with one
crossing-free circle, with its half-edges labelled by their positions. -/
theorem resolveCrossing_reidemeisterOne_last_self :
    (D.reidemeisterOne h b).resolveCrossing (Fin.last n) b =
      D.adjoinCircle.relabel D.halfEdge.symm (Equiv.refl _) := by
  apply PDCode.ext
  · rw [resolveCrossing_halfEdge, ← adjoinCircle_halfEdge D,
      D.adjoinCircle.relabel_halfEdge_symm_halfEdge]
  · rw [← adjoinCircle_halfEdge D]
    exact D.adjoinCircle.eq_relabel_edgePair_of_crossing fun _ _ _ _ hij ↦
      D.resolveCrossing_reidemeisterOne_edgePair h b _ (by simpa using hij)
  · simp [detachedCircleCount_reidemeisterOne_last]
  · funext i
    simp [Fin.succAbove_last]

end ReidemeisterOne

/-! ### The isolated kink -/

section AdjoinKink

private theorem adjoinKink_smoothing_last (t : Bool) :
    (bif t then (D.adjoinKink b).overPair (Fin.last n)
      else !(D.adjoinKink b).overPair (Fin.last n)) = (t == b) := by
  cases t <;> cases b <;> simp

/-- **The circles detached from an isolated kink.** Resolving the crossing of an isolated kink
detaches both of its smoothing arcs as separate circles for the smoothing `b`, and joins them
into one circle for the smoothing `!b`. -/
theorem detachedCircleCount_adjoinKink_last (t : Bool) :
    (D.adjoinKink b).detachedCircleCount (Fin.last n) t = if t = b then 2 else 1 := by
  rw [detachedCircleCount_eq, adjoinKink_smoothing_last]
  simp only [adjoinKink_crossing_last, adjoinKink_edgePair_inr, EmbeddingLike.apply_eq_iff_eq]
  cases t <;> cases b <;> simp [swap_apply_of_ne_of_ne]

/-- An arc of `D` is an arc of each resolution of an isolated kink. -/
private theorem resolveCrossing_adjoinKink_edgePair (t : Bool) {i j : Fin n} {k l : Fin 4}
    (hij : D.edgePair.val (D.crossing i k) = D.crossing j l) :
    ((D.adjoinKink b).resolveCrossing (Fin.last n) t).edgePair.val
      (crossingSlotEquiv n (i, k)) = crossingSlotEquiv n (j, l) := by
  refine (D.adjoinKink b).resolveCrossing_edgePair_val_of_edgePair_val_eq (Fin.last n) t ?_
  rw [Fin.succAbove_last, adjoinKink_crossing_castSucc, adjoinKink_edgePair_inl, hij,
    adjoinKink_crossing_castSucc]

/-- **Resolving an isolated kink into one circle.** Resolving the crossing of an isolated kink
adjoined to `D` by the smoothing `!b` gives `D` together with one crossing-free circle, with its
half-edges labelled by their positions. -/
theorem resolveCrossing_adjoinKink_last_not :
    (D.adjoinKink b).resolveCrossing (Fin.last n) (!b) =
      D.adjoinCircle.relabel D.halfEdge.symm (Equiv.refl _) := by
  apply PDCode.ext
  · rw [resolveCrossing_halfEdge, ← adjoinCircle_halfEdge D,
      D.adjoinCircle.relabel_halfEdge_symm_halfEdge]
  · rw [← adjoinCircle_halfEdge D]
    exact D.adjoinCircle.eq_relabel_edgePair_of_crossing fun _ _ _ _ hij ↦
      D.resolveCrossing_adjoinKink_edgePair b _ (by simpa using hij)
  · simp [detachedCircleCount_adjoinKink_last]
  · funext i
    simp [Fin.succAbove_last]

/-- **Resolving an isolated kink into two circles.** Resolving the crossing of an isolated kink
adjoined to `D` by the smoothing `b` gives `D` together with two crossing-free circles, with its
half-edges labelled by their positions. -/
theorem resolveCrossing_adjoinKink_last_self :
    (D.adjoinKink b).resolveCrossing (Fin.last n) b =
      D.adjoinCircle.adjoinCircle.relabel D.halfEdge.symm (Equiv.refl _) := by
  apply PDCode.ext
  · rw [resolveCrossing_halfEdge, ← adjoinCircle_halfEdge D,
      ← adjoinCircle_halfEdge D.adjoinCircle,
      D.adjoinCircle.adjoinCircle.relabel_halfEdge_symm_halfEdge]
  · rw [← adjoinCircle_halfEdge D, ← adjoinCircle_halfEdge D.adjoinCircle]
    exact D.adjoinCircle.adjoinCircle.eq_relabel_edgePair_of_crossing fun _ _ _ _ hij ↦
      D.resolveCrossing_adjoinKink_edgePair b _ (by simpa using hij)
  · simp [detachedCircleCount_adjoinKink_last, Nat.add_assoc]
  · funext i
    simp [Fin.succAbove_last]

end AdjoinKink

/-! ### Identifications of all smoothings -/

namespace ResolutionEquiv

/-- The identification of all smoothings of `D` with those of the resolution of a kink inserted
into an arc of `D` along the kink (`TauCeti.PDCode.resolveCrossing_reidemeisterOne_last_not`).
It keeps the crossings and the crossing-free circles, and sends each half-edge to its position. -/
def resolveCrossingReidemeisterOneNot :
    D.ResolutionEquiv ((D.reidemeisterOne h b).resolveCrossing (Fin.last n) (!b)) :=
  (ResolutionEquiv.relabel D D.halfEdge.symm (Equiv.refl _)).trans
    (ofEq (resolveCrossing_reidemeisterOne_last_not D h b).symm)

/-- `resolveCrossingReidemeisterOneNot` keeps the crossings. -/
@[simp]
theorem resolveCrossingReidemeisterOneNot_crossingEquiv :
    (resolveCrossingReidemeisterOneNot D h b).crossingEquiv = Equiv.refl _ := by
  simp [resolveCrossingReidemeisterOneNot]

/-- `resolveCrossingReidemeisterOneNot` sends each half-edge to its position. -/
@[simp]
theorem resolveCrossingReidemeisterOneNot_halfEdgeEquiv :
    (resolveCrossingReidemeisterOneNot D h b).halfEdgeEquiv = D.halfEdge.symm := by
  simp [resolveCrossingReidemeisterOneNot]

/-- `resolveCrossingReidemeisterOneNot` keeps the labels of the crossing-free circles. -/
@[simp]
theorem resolveCrossingReidemeisterOneNot_crossinglessEquiv_val
    (i : Fin D.crossinglessComponentCount) :
    ((resolveCrossingReidemeisterOneNot D h b).crossinglessEquiv i : ℕ) = i := by
  simp [resolveCrossingReidemeisterOneNot]

/-- The identification of all smoothings of `D` with one adjoined circle with those of the
resolution of a kink inserted into an arc of `D` that cuts off its loop
(`TauCeti.PDCode.resolveCrossing_reidemeisterOne_last_self`). It keeps the crossings and the
labels of the crossing-free circles, the adjoined circle becoming the loop of the kink, and sends
each half-edge to its position. -/
def resolveCrossingReidemeisterOneSelf :
    D.adjoinCircle.ResolutionEquiv ((D.reidemeisterOne h b).resolveCrossing (Fin.last n) b) :=
  (ResolutionEquiv.relabel D.adjoinCircle D.halfEdge.symm (Equiv.refl _)).trans
    (ofEq (resolveCrossing_reidemeisterOne_last_self D h b).symm)

/-- `resolveCrossingReidemeisterOneSelf` keeps the crossings. -/
@[simp]
theorem resolveCrossingReidemeisterOneSelf_crossingEquiv :
    (resolveCrossingReidemeisterOneSelf D h b).crossingEquiv = Equiv.refl _ := by
  simp [resolveCrossingReidemeisterOneSelf]

/-- `resolveCrossingReidemeisterOneSelf` sends each half-edge to its position. -/
@[simp]
theorem resolveCrossingReidemeisterOneSelf_halfEdgeEquiv :
    (resolveCrossingReidemeisterOneSelf D h b).halfEdgeEquiv = D.halfEdge.symm := by
  simp [resolveCrossingReidemeisterOneSelf]

/-- `resolveCrossingReidemeisterOneSelf` keeps the labels of the crossing-free circles. -/
@[simp]
theorem resolveCrossingReidemeisterOneSelf_crossinglessEquiv_val
    (i : Fin D.adjoinCircle.crossinglessComponentCount) :
    ((resolveCrossingReidemeisterOneSelf D h b).crossinglessEquiv i : ℕ) = i := by
  simp [resolveCrossingReidemeisterOneSelf]

/-- The identification of all smoothings of `D` with one adjoined circle with those of the
resolution of an isolated kink adjoined to `D` that joins its two smoothing arcs
(`TauCeti.PDCode.resolveCrossing_adjoinKink_last_not`). It keeps the crossings and the labels of
the crossing-free circles, the adjoined circle becoming the resolved kink, and sends each
half-edge to its position. -/
def resolveCrossingAdjoinKinkNot :
    D.adjoinCircle.ResolutionEquiv ((D.adjoinKink b).resolveCrossing (Fin.last n) (!b)) :=
  (ResolutionEquiv.relabel D.adjoinCircle D.halfEdge.symm (Equiv.refl _)).trans
    (ofEq (resolveCrossing_adjoinKink_last_not D b).symm)

/-- `resolveCrossingAdjoinKinkNot` keeps the crossings. -/
@[simp]
theorem resolveCrossingAdjoinKinkNot_crossingEquiv :
    (resolveCrossingAdjoinKinkNot D b).crossingEquiv = Equiv.refl _ := by
  simp [resolveCrossingAdjoinKinkNot]

/-- `resolveCrossingAdjoinKinkNot` sends each half-edge to its position. -/
@[simp]
theorem resolveCrossingAdjoinKinkNot_halfEdgeEquiv :
    (resolveCrossingAdjoinKinkNot D b).halfEdgeEquiv = D.halfEdge.symm := by
  simp [resolveCrossingAdjoinKinkNot]

/-- `resolveCrossingAdjoinKinkNot` keeps the labels of the crossing-free circles. -/
@[simp]
theorem resolveCrossingAdjoinKinkNot_crossinglessEquiv_val
    (i : Fin D.adjoinCircle.crossinglessComponentCount) :
    ((resolveCrossingAdjoinKinkNot D b).crossinglessEquiv i : ℕ) = i := by
  simp [resolveCrossingAdjoinKinkNot]

/-- The identification of all smoothings of `D` with two adjoined circles with those of the
resolution of an isolated kink adjoined to `D` that detaches its two smoothing arcs
(`TauCeti.PDCode.resolveCrossing_adjoinKink_last_self`). It keeps the crossings and the labels of
the crossing-free circles, the two adjoined circles becoming the two smoothing arcs, and sends
each half-edge to its position. -/
def resolveCrossingAdjoinKinkSelf :
    D.adjoinCircle.adjoinCircle.ResolutionEquiv
      ((D.adjoinKink b).resolveCrossing (Fin.last n) b) :=
  (ResolutionEquiv.relabel D.adjoinCircle.adjoinCircle D.halfEdge.symm (Equiv.refl _)).trans
    (ofEq (resolveCrossing_adjoinKink_last_self D b).symm)

/-- `resolveCrossingAdjoinKinkSelf` keeps the crossings. -/
@[simp]
theorem resolveCrossingAdjoinKinkSelf_crossingEquiv :
    (resolveCrossingAdjoinKinkSelf D b).crossingEquiv = Equiv.refl _ := by
  simp [resolveCrossingAdjoinKinkSelf]

/-- `resolveCrossingAdjoinKinkSelf` sends each half-edge to its position. -/
@[simp]
theorem resolveCrossingAdjoinKinkSelf_halfEdgeEquiv :
    (resolveCrossingAdjoinKinkSelf D b).halfEdgeEquiv = D.halfEdge.symm := by
  simp [resolveCrossingAdjoinKinkSelf]

/-- `resolveCrossingAdjoinKinkSelf` keeps the labels of the crossing-free circles. -/
@[simp]
theorem resolveCrossingAdjoinKinkSelf_crossinglessEquiv_val
    (i : Fin D.adjoinCircle.adjoinCircle.crossinglessComponentCount) :
    ((resolveCrossingAdjoinKinkSelf D b).crossinglessEquiv i : ℕ) = i := by
  simp [resolveCrossingAdjoinKinkSelf]

end ResolutionEquiv

end TauCeti.PDCode
