/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Reidemeister.Three.Kauffman

/-!
# The third Reidemeister move on oriented PD-codes

`TauCeti.PDCode.reidemeisterThree` replaces the triangular tangle `σ₁ σ₂ σ₁` at three crossings of
a PD-code by `σ₂ σ₁ σ₂`, moving the twelve local half-edges by the permutation
`TauCeti.PDCode.reidemeisterThreePerm`. This file lifts the move to oriented codes. Each of the
three strands of the tangle keeps its direction, so every half-edge takes the orientation of the
half-edge it is moved from, and the oriented move takes no data beyond the unoriented one. The
strands may be oriented in any of the eight ways.

The three crossings of the new tangle carry the signs of the old ones, with the first and the
third crossing exchanging their signs, exactly as they exchange their over-pair indicators. So the
move keeps the writhe. Together with the invariance of the Kauffman bracket
(`TauCeti.PDCode.kauffmanBracket_reidemeisterThree`), this makes the writhe-normalized Kauffman
bracket invariant under the oriented third Reidemeister move. The sign and writhe statements only
use the three internal arcs of the triangle, not the height order of its strands.

## Main definitions

* `TauCeti.OrientedPDCode.reidemeisterThree`: the third Reidemeister move on an oriented code.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_reidemeisterThree`: the move exchanges the signs of the
  first and third crossing of the triangle and keeps every other sign.
* `TauCeti.OrientedPDCode.writhe_reidemeisterThree`: the move keeps the writhe.
* `TauCeti.OrientedPDCode.normalizedKauffmanBracket_reidemeisterThree`: the writhe-normalized
  Kauffman bracket is invariant under the move.
* `TauCeti.OrientedPDCode.mirror_reidemeisterThree` and
  `TauCeti.OrientedPDCode.reverse_reidemeisterThree`: the move commutes with reflection and with
  reversal.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1
  (oriented Reidemeister moves) and Chapter 3 (the writhe and the Jones polynomial from the
  bracket).
-/

public section

namespace TauCeti

namespace OrientedPDCode

open PDCode

variable {n : ℕ}

/-- **The third Reidemeister move on an oriented PD-code**: the rewire
`TauCeti.PDCode.reidemeisterThree` at the crossings `c 0`, `c 1`, `c 2`, with every half-edge
oriented as the half-edge that `TauCeti.PDCode.reidemeisterThreePerm` moves to it, so that each
strand of the tangle keeps its direction. It is a Reidemeister move when the three crossings
satisfy `TauCeti.PDCode.HasReidemeisterThreeTriangle`. -/
def reidemeisterThree (D : OrientedPDCode n) (c : Fin 3 ↪ Fin n) : OrientedPDCode n where
  toPDCode := D.toPDCode.reidemeisterThree c
  orientation x := D.orientation ((D.reidemeisterThreePerm c).symm x)
  orientation_edgePair := by
    intro x
    obtain ⟨y, rfl⟩ := (D.reidemeisterThreePerm c).surjective x
    rw [reidemeisterThree_edgePair_transport]
    simp
  orientation_oppositeCrossingSlot := by
    intro i slot
    -- The rewire commutes with the crossing turn, which reverses orientations.
    have hturn (x : Fin (4 * n)) :
        (D.reidemeisterThreePerm c).symm (D.crossingTurn x) =
          D.crossingTurn ((D.reidemeisterThreePerm c).symm x) := by
      rw [Equiv.symm_apply_eq, ← Equiv.permCongr_apply, D.reidemeisterThreePerm_crossingTurn c]
    simp only [reidemeisterThree_halfEdge, ← crossing_apply]
    rw [← crossingTurn_crossing, hturn, orientation_crossingTurn, crossing_apply]
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := by simp

variable (D : OrientedPDCode n) (c : Fin 3 ↪ Fin n)

/-- Forgetting the orientation of the oriented third Reidemeister move gives the unoriented
one. -/
@[simp]
theorem toPDCode_reidemeisterThree :
    (D.reidemeisterThree c).toPDCode = D.toPDCode.reidemeisterThree c :=
  (rfl)

/-- The oriented third Reidemeister move orients each half-edge as the half-edge moved to it. -/
@[simp]
theorem orientation_reidemeisterThree (x : Fin (4 * n)) :
    (D.reidemeisterThree c).orientation x = D.orientation ((D.reidemeisterThreePerm c).symm x) :=
  (rfl)

/-- The oriented third Reidemeister move transports the orientation of every half-edge along the
local rewire. -/
theorem orientation_reidemeisterThree_reidemeisterThreePerm (x : Fin (4 * n)) :
    (D.reidemeisterThree c).orientation (D.reidemeisterThreePerm c x) = D.orientation x := by
  simp

/-- The orientation of a slot of one of the three crossings of the new tangle, read off the slot
of the old tangle that the local rewire moves to it. -/
theorem orientation_reidemeisterThree_crossing (i : Fin 3) (s : Fin 4) :
    (D.reidemeisterThree c).orientation (D.crossing (c i) s) =
      D.orientation (D.crossing (c (reidemeisterThreeSlots.symm (i, s)).1)
        (reidemeisterThreeSlots.symm (i, s)).2) := by
  have hx : D.crossing (c i) s = D.reidemeisterThreePerm c
      (D.crossing (c (reidemeisterThreeSlots.symm (i, s)).1)
        (reidemeisterThreeSlots.symm (i, s)).2) := by
    rw [reidemeisterThreePerm_apply_crossing, Equiv.apply_symm_apply]
  rw [hx, orientation_reidemeisterThree_reidemeisterThreePerm]

/-- The oriented third Reidemeister move keeps the orientation of every slot of a crossing outside
the triangle. -/
theorem orientation_reidemeisterThree_crossing_of_notMem {i : Fin n} (hi : i ∉ Set.range c)
    (s : Fin 4) :
    (D.reidemeisterThree c).orientation (D.crossing i s) = D.orientation (D.crossing i s) := by
  have h := orientation_reidemeisterThree_reidemeisterThreePerm D c (D.crossing i s)
  rwa [reidemeisterThreePerm_crossing_of_notMem D.toPDCode c hi s] at h

/-- The oriented third Reidemeister move keeps the oriented crossing-free components. -/
@[simp]
theorem crossinglessComponents_reidemeisterThree :
    (D.reidemeisterThree c).crossinglessComponents = D.crossinglessComponents :=
  (rfl)

/-- On the three crossings of the triangle, the oriented third Reidemeister move exchanges the
signs of the first and the third crossing. -/
private theorem crossingSign_reidemeisterThree_triangle (h : D.HasReidemeisterThreeTriangleArcs c)
    (j : Fin 3) :
    (D.reidemeisterThree c).crossingSign (c j) = D.crossingSign (c (Equiv.swap 0 2 j)) := by
  -- The new orientation of a slot of the triangle is the old orientation of the slot moved
  -- to it.
  have hnew (k : Fin 3) (s : Fin 4) (l : Fin 3) (t : Fin 4)
      (hlt : reidemeisterThreeSlots (l, t) = (k, s)) :
      (D.reidemeisterThree c).orientation (D.crossing (c k) s) =
        D.orientation (D.crossing (c l) t) := by
    rw [orientation_reidemeisterThree_crossing, ← hlt, Equiv.symm_apply_apply]
  have hslot (k l : Fin 3) (s t : Fin 4) (hst : ![![(1, 0), (0, 2), (1, 2), (0, 0)],
      ![(2, 0), (0, 1), (2, 2), (0, 3)], ![(2, 3), (1, 1), (2, 1), (1, 3)]] k s = (l, t)) :
      reidemeisterThreeSlots (k, s) = (l, t) := by
    rw [reidemeisterThreeSlots_apply, hst]
  -- Each arc of the triangle and each local strand reverses the orientation.
  have harc (x y : Fin (4 * n)) (hxy : D.edgePair.val x = y) :
      D.orientation y = !D.orientation x := by
    rw [← hxy, orientation_edgePair]
  have hopp (k : Fin 3) (s t : Fin 4) (hst : oppositeCrossingSlot s = t) :
      D.orientation (D.crossing (c k) t) = !D.orientation (D.crossing (c k) s) := by
    rw [← hst, crossing_apply, crossing_apply, orientation_oppositeCrossingSlot]
  have hopp₀ : oppositeCrossingSlot 0 = 2 := by rw [oppositeCrossingSlot_apply]; decide
  have hopp₁ : oppositeCrossingSlot 1 = 3 := by rw [oppositeCrossingSlot_apply]; decide
  obtain ⟨ha, hb, hc⟩ := (hasReidemeisterThreeTriangleArcs_iff D.toPDCode c).mp h
  -- Express the orientations of the slots involved through those of the slots `(0, 0)`,
  -- `(0, 1)` and `(1, 1)` of the triangle.
  have h₀₃ := hopp 0 1 3 hopp₁
  have h₁₀ : D.orientation (D.crossing (c 1) 0) = D.orientation (D.crossing (c 0) 0) := by
    rw [harc _ _ ha, hopp 0 0 2 hopp₀, Bool.not_not]
  have h₂₀ : D.orientation (D.crossing (c 2) 0) = !D.orientation (D.crossing (c 0) 1) :=
    harc _ _ hc
  have h₂₁ : D.orientation (D.crossing (c 2) 1) = D.orientation (D.crossing (c 1) 1) := by
    rw [← Bool.not_inj_iff, ← hopp 2 1 3 hopp₁, harc _ _ hb]
  have h₂₂ : D.orientation (D.crossing (c 2) 2) = D.orientation (D.crossing (c 0) 1) := by
    rw [hopp 2 0 2 hopp₀, h₂₀, Bool.not_not]
  -- The sign of a crossing of the new tangle is that of the old crossing whose name it takes,
  -- as soon as the old slots moved to its slots `0` and `1` have the same orientation parity.
  have hsign (j j' l₀ l₁ : Fin 3) (t₀ t₁ : Fin 4) (hj : Equiv.swap 0 2 j = j')
      (h₀ : reidemeisterThreeSlots (l₀, t₀) = (j, 0))
      (h₁ : reidemeisterThreeSlots (l₁, t₁) = (j, 1))
      (hxor : Bool.xor (D.orientation (D.crossing (c l₀) t₀))
          (D.orientation (D.crossing (c l₁) t₁)) =
        Bool.xor (D.orientation (D.crossing (c j') 0)) (D.orientation (D.crossing (c j') 1))) :
      (D.reidemeisterThree c).crossingSign (c j) = D.crossingSign (c j') := by
    rw [crossingSign_def, crossingSign_def, toPDCode_reidemeisterThree, reidemeisterThree_crossing,
      reidemeisterThree_crossing, reidemeisterThree_overPair, ← c.injective.map_swap, hj,
      hnew j 0 l₀ t₀ h₀, hnew j 1 l₁ t₁ h₁, hxor]
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · exact hsign 0 2 0 1 3 1 (by decide) (hslot _ _ _ _ rfl) (hslot _ _ _ _ rfl)
      (by simp only [h₀₃, h₂₀, h₂₁])
  · exact hsign 1 1 0 2 0 1 (by decide) (hslot _ _ _ _ rfl) (hslot _ _ _ _ rfl)
      (by simp only [h₁₀, h₂₁])
  · exact hsign 2 0 1 2 0 2 (by decide) (hslot _ _ _ _ rfl) (hslot _ _ _ _ rfl)
      (by simp only [h₁₀, h₂₂])

/-- **The oriented third Reidemeister move permutes the crossing signs**: the first and the third
crossing of the triangle exchange their signs, and every other crossing keeps its sign. Only the
three internal arcs of the triangle are needed, not the height order of its strands. -/
@[simp]
theorem crossingSign_reidemeisterThree (h : D.HasReidemeisterThreeTriangleArcs c) (i : Fin n) :
    (D.reidemeisterThree c).crossingSign i = D.crossingSign (Equiv.swap (c 0) (c 2) i) := by
  by_cases hi : i ∈ Set.range c
  · obtain ⟨j, rfl⟩ := hi
    rw [← c.injective.map_swap]
    exact crossingSign_reidemeisterThree_triangle D c h j
  · have h₀ : i ≠ c 0 := fun h ↦ hi ⟨0, h.symm⟩
    have h₂ : i ≠ c 2 := fun h ↦ hi ⟨2, h.symm⟩
    simp only [crossingSign_def, toPDCode_reidemeisterThree, reidemeisterThree_crossing,
      orientation_reidemeisterThree_crossing_of_notMem D c hi, reidemeisterThree_overPair,
      Equiv.swap_apply_of_ne_of_ne h₀ h₂]

/-- **The oriented third Reidemeister move keeps the writhe.** -/
@[simp]
theorem writhe_reidemeisterThree (h : D.HasReidemeisterThreeTriangleArcs c) :
    (D.reidemeisterThree c).writhe = D.writhe := by
  simp only [writhe_def, crossingSign_reidemeisterThree D c h]
  exact Equiv.sum_comp (Equiv.swap (c 0) (c 2)) D.crossingSign

/-- **The writhe-normalized Kauffman bracket is invariant under the oriented third Reidemeister
move**, for every surrounding diagram and all six height orders of the three strands. -/
@[simp]
theorem normalizedKauffmanBracket_reidemeisterThree (h : D.HasReidemeisterThreeTriangle c)
    {R : Type*} [CommRing R] (a : Rˣ) :
    (D.reidemeisterThree c).normalizedKauffmanBracket a = D.normalizedKauffmanBracket a := by
  rw [normalizedKauffmanBracket_def, normalizedKauffmanBracket_def,
    writhe_reidemeisterThree D c h.arcs, toPDCode_reidemeisterThree,
    kauffmanBracket_reidemeisterThree D.toPDCode c h]

/-- Reflecting the oriented third Reidemeister move performs the move on the reflected code. -/
@[simp]
theorem mirror_reidemeisterThree :
    (D.reidemeisterThree c).mirror = D.mirror.reidemeisterThree c := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    simp
  · simp

/-- Reversing the oriented third Reidemeister move performs the move on the reversed code. -/
@[simp]
theorem reverse_reidemeisterThree :
    (D.reidemeisterThree c).reverse = D.reverse.reidemeisterThree c := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    simp
  · simp

end OrientedPDCode

end TauCeti
