/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.RotateCrossing

/-!
# Switching a crossing of a PD-code

Switching the over- and under-strands at a single crossing `i` of a PD-code while keeping the
half-edges in their slots, the arcs, the crossing-free circles, and all other crossings unchanged
gives `TauCeti.PDCode.changeCrossing D i`. Unlike `TauCeti.PDCode.rotateCrossing`, which shifts the
slots of `i` and flips `overPair i` together so as to describe the same diagram, `changeCrossing`
keeps the slot numbering and flips `overPair i` alone, performing an actual crossing change.

Changing a crossing preserves the underlying `4`-valent graph, its faces, planarity, and the
component traversal. At the switched crossing the `A`- and `B`-smoothings exchange roles, so
flipping the state bit at `i` (`TauCeti.PDCode.flipStateEquiv i`) matches the smoothed diagrams and
their circle counts bijectively. On an oriented code (`TauCeti.OrientedPDCode.changeCrossing`),
switching crossing `i` negates `crossingSign i`, leaves all other crossing signs unchanged, shifts
`negativeCrossingCount` by `±1`, and therefore preserves the parity of
`#{j | s j = false} + negativeCrossingCount` along `flipStateEquiv i`.

## Main definitions

* `TauCeti.PDCode.changeCrossing`: switch the over- and under-strands at one crossing of a PD-code.
* `TauCeti.PDCode.flipStateEquiv`: the involution on states flipping the smoothing choice at one
  crossing.
* `TauCeti.OrientedPDCode.changeCrossing`: switch one crossing of an oriented PD-code, keeping
  every arc and crossing-free circle orientation.

## Main results

* `TauCeti.PDCode.toPermutationTriple_changeCrossing`,
  `TauCeti.PDCode.isPlanar_changeCrossing`, and `TauCeti.PDCode.componentCount_changeCrossing`:
  switching a crossing preserves the underlying graph, planarity, and the number of components.
* `TauCeti.PDCode.statePerm_changeCrossing_flipStateEquiv` and
  `TauCeti.PDCode.stateLoopCount_changeCrossing_flipStateEquiv`: flipping the state bit at `i`
  identifies the smoothed diagrams before and after switching crossing `i`.
* `TauCeti.OrientedPDCode.crossingSign_changeCrossing_self` and
  `TauCeti.OrientedPDCode.crossingSign_changeCrossing_of_ne`: switching crossing `i` negates its
  sign and preserves every other crossing sign.
* `TauCeti.OrientedPDCode.card_false_flipStateEquiv_add_negativeCrossingCount_mod_two`: flipping
  the state bit at `i` preserves the parity of `#{j | s j = false} + n₋` across a crossing change.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1
  (crossing changes and crossing signs).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm Finset

namespace PDCode

variable {n : ℕ}

/-- Switch the over- and under-strands at crossing `i` of a PD-code, keeping the half-edges in
their slots, the arcs, the crossing-free circles, and every other crossing unchanged. -/
def changeCrossing (D : PDCode n) (i : Fin n) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Function.update D.overPair i (!D.overPair i)

/-- The involution on states that flips the `A`/`B` choice at crossing `i` and leaves all other
crossings unchanged. Across `TauCeti.PDCode.changeCrossing D i` it matches each state with the
state producing the same smoothed diagram. -/
def flipStateEquiv (i : Fin n) : Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun s ↦ Function.update s i (!s i)) fun s ↦ by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

/-- Applying `flipStateEquiv i` updates the state at `i` by negation. -/
theorem flipStateEquiv_apply (i : Fin n) (s : Fin n → Bool) :
    flipStateEquiv i s = Function.update s i (!s i) :=
  congrFun (Function.Involutive.coe_toPerm _) s

/-- At crossing `i`, `flipStateEquiv i` negates the state bit. -/
@[simp] theorem flipStateEquiv_apply_self (i : Fin n) (s : Fin n → Bool) :
    flipStateEquiv i s i = !s i := by
  simp [flipStateEquiv_apply]

/-- Away from crossing `i`, `flipStateEquiv i` leaves the state bit unchanged. -/
@[simp] theorem flipStateEquiv_apply_of_ne (i : Fin n) (s : Fin n → Bool) {j : Fin n}
    (hj : j ≠ i) : flipStateEquiv i s j = s j := by
  simp [flipStateEquiv_apply, hj]

/-- Flipping the state at `i` twice returns the original state. -/
@[simp] theorem flipStateEquiv_flipStateEquiv (i : Fin n) (s : Fin n → Bool) :
    flipStateEquiv i (flipStateEquiv i s) = s := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- `flipStateEquiv i` is its own inverse. -/
@[simp] theorem flipStateEquiv_symm (i : Fin n) :
    (flipStateEquiv i).symm = flipStateEquiv i := by
  ext s j
  exact congrFun ((flipStateEquiv i).injective
    (by rw [apply_symm_apply, flipStateEquiv_flipStateEquiv])) j

/-- Flipping a state at `i` increases the count of `false` entries by one when `s i = true`. -/
theorem card_false_flipStateEquiv_of_true (i : Fin n) {s : Fin n → Bool} (hs : s i = true) :
    #{j | flipStateEquiv i s j = false} = #{j | s j = false} + 1 := by
  have hmem : i ∉ filter (fun j ↦ s j = false) univ := by simp [hs]
  have hset : filter (fun j ↦ flipStateEquiv i s j = false) univ =
      insert i (filter (fun j ↦ s j = false) univ) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hs]
    · simp [hj]
  rw [hset, card_insert_of_notMem hmem]

/-- Flipping a state at `i` decreases the count of `false` entries by one when `s i = false`. -/
theorem card_false_flipStateEquiv_of_false (i : Fin n) {s : Fin n → Bool} (hs : s i = false) :
    #{j | flipStateEquiv i s j = false} + 1 = #{j | s j = false} := by
  have hmem : i ∈ filter (fun j ↦ s j = false) univ := by simp [hs]
  have hset : filter (fun j ↦ flipStateEquiv i s j = false) univ =
      (filter (fun j ↦ s j = false) univ).erase i := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hs]
    · simp [hj]
  rw [hset, card_erase_add_one hmem]

section ChangeCrossing

variable (D : PDCode n) (i : Fin n)

/-- Switching a crossing leaves the half-edge labelling unchanged. -/
@[simp] theorem changeCrossing_halfEdge : (D.changeCrossing i).halfEdge = D.halfEdge := (rfl)

/-- Switching a crossing leaves the arcs unchanged. -/
@[simp] theorem changeCrossing_edgePair : (D.changeCrossing i).edgePair = D.edgePair := (rfl)

/-- Switching a crossing leaves the number of crossing-free circles unchanged. -/
@[simp] theorem changeCrossing_crossinglessComponentCount :
    (D.changeCrossing i).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- The over-pair function of `D.changeCrossing i` updates `D.overPair` at `i` by negation. -/
theorem changeCrossing_overPair :
    (D.changeCrossing i).overPair = Function.update D.overPair i (!D.overPair i) := (rfl)

/-- The over-pair indicator at the switched crossing flips. -/
@[simp] theorem changeCrossing_overPair_self :
    (D.changeCrossing i).overPair i = !D.overPair i := by
  simp [changeCrossing]

/-- Every crossing other than the switched one keeps its over-pair indicator. -/
@[simp] theorem changeCrossing_overPair_of_ne {j : Fin n} (hj : j ≠ i) :
    (D.changeCrossing i).overPair j = D.overPair j := by
  simp [changeCrossing, hj]

-- Not `@[simp]`: `crossing_apply` and `changeCrossing_halfEdge` already rewrite the LHS.
/-- Switching a crossing keeps every half-edge in its crossing slot. -/
theorem crossing_changeCrossing (j : Fin n) (slot : Fin 4) :
    (D.changeCrossing i).crossing j slot = D.crossing j slot := by
  simp

/-- At the switched crossing, over- and under-slots exchange roles. -/
@[simp] theorem isOver_changeCrossing_self (slot : Fin 4) :
    (D.changeCrossing i).isOver i slot = !D.isOver i slot := by
  fin_cases slot <;> simp

/-- Away from the switched crossing, over- and under-slots are unchanged. -/
@[simp] theorem isOver_changeCrossing_of_ne {j : Fin n} (hj : j ≠ i) (slot : Fin 4) :
    (D.changeCrossing i).isOver j slot = D.isOver j slot := by
  fin_cases slot <;> simp [hj]

/-- Switching the same crossing twice returns the original PD-code. -/
@[simp] theorem changeCrossing_changeCrossing :
    (D.changeCrossing i).changeCrossing i = D := by
  ext j
  · rfl
  · rfl
  · rfl
  · by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

/-- Switching two crossings commutes. -/
theorem changeCrossing_comm (j : Fin n) :
    (D.changeCrossing i).changeCrossing j = (D.changeCrossing j).changeCrossing i := by
  ext k
  · rfl
  · rfl
  · rfl
  · by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- Mirroring commutes with switching a crossing. -/
@[simp] theorem mirror_changeCrossing :
    (D.changeCrossing i).mirror = D.mirror.changeCrossing i := by
  ext j
  · simp
  · simp
  · simp
  · by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

/-- Relabelling transports a crossing change to the image crossing. -/
@[simp] theorem relabel_changeCrossing {m : ℕ} (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) :
    (D.changeCrossing i).relabel half cross = (D.relabel half cross).changeCrossing (cross i) := by
  ext j
  · simp
  · simp
  · simp
  · by_cases hj : j = cross i
    · subst hj
      simp
    · have hj' : cross.symm j ≠ i := fun h ↦ hj (by simpa using congrArg cross h)
      simp [hj, hj']

/-- Reading a crossing from its next slot commutes with switching a crossing. -/
@[simp] theorem rotateCrossing_changeCrossing (j : Fin n) :
    (D.changeCrossing i).rotateCrossing j = (D.rotateCrossing j).changeCrossing i := by
  ext1
  · ext x
    obtain ⟨⟨k, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
    by_cases hkj : k = j
    · subst hkj
      simp
    · simp [hkj]
  · simp
  · simp
  · funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- Switching a crossing keeps the counterclockwise slot rotation at every crossing. -/
@[simp] theorem crossingRotation_changeCrossing :
    (D.changeCrossing i).crossingRotation = D.crossingRotation := by
  ext h
  obtain ⟨x, rfl⟩ := (D.changeCrossing i).halfEdge.surjective h
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  rw [crossingRotation_crossing]
  simp [crossingRotation_crossing]

/-- Switching a crossing keeps the face traversal. -/
@[simp] theorem facePerm_changeCrossing : (D.changeCrossing i).facePerm = D.facePerm := by
  simp [facePerm_def]

/-- Switching a crossing keeps the permutation triple of the underlying `4`-valent graph. -/
@[simp] theorem toPermutationTriple_changeCrossing :
    (D.changeCrossing i).toPermutationTriple = D.toPermutationTriple :=
  PermutationTriple.ext_of_two (by simp) (by simp)

/-- Switching a crossing preserves planarity. -/
@[simp] theorem isPlanar_changeCrossing : (D.changeCrossing i).IsPlanar ↔ D.IsPlanar := by
  simp [isPlanar_def]

/-- Switching a crossing keeps the opposite-slot turn at every crossing. -/
@[simp] theorem crossingTurn_changeCrossing :
    (D.changeCrossing i).crossingTurn = D.crossingTurn := by
  simp [crossingTurn_def]

/-- Switching a crossing keeps the component traversal. -/
@[simp] theorem componentPerm_changeCrossing :
    (D.changeCrossing i).componentPerm = D.componentPerm := by
  simp [componentPerm_def]

/-- Switching a crossing keeps the number of crossing-bearing components. -/
@[simp] theorem crossingComponentCount_changeCrossing :
    (D.changeCrossing i).crossingComponentCount = D.crossingComponentCount := by
  simp [crossingComponentCount_def]

-- Not `@[simp]`: `componentCount` is an `abbrev` and its two summands simplify individually.
/-- Switching a crossing keeps the total number of components. -/
theorem componentCount_changeCrossing :
    (D.changeCrossing i).componentCount = D.componentCount := by
  simp [componentCount_eq]

/-- Switching a crossing does not change how a prescribed family of local smoothings reconnects the
half-edges; only which of the two local smoothings at `i` is the `A`-smoothing flips. -/
@[simp] theorem smoothingTurn_changeCrossing (b : Fin n → Bool) :
    (D.changeCrossing i).smoothingTurn b = D.smoothingTurn b := by
  simp [smoothingTurn_def]

/-- On `D.changeCrossing i`, a state `s` selects the same local smoothings as `flipStateEquiv i s`
on `D`. -/
theorem smoothingChoice_changeCrossing (s : Fin n → Bool) :
    (D.changeCrossing i).smoothingChoice s = D.smoothingChoice (flipStateEquiv i s) := by
  funext j
  by_cases hj : j = i
  · subst hj
    cases hs : s j <;> simp [hs]
  · cases hs : s j <;> simp [hs, hj]

/-- Flipping the state bit at `i` matches the local smoothings of `D.changeCrossing i` with those
of `D`. -/
@[simp] theorem smoothingChoice_changeCrossing_flipStateEquiv (s : Fin n → Bool) :
    (D.changeCrossing i).smoothingChoice (flipStateEquiv i s) = D.smoothingChoice s := by
  rw [smoothingChoice_changeCrossing, flipStateEquiv_flipStateEquiv]

/-- On `D.changeCrossing i`, a state `s` traverses the same smoothed circles as
`flipStateEquiv i s` on `D`. -/
theorem statePerm_changeCrossing (s : Fin n → Bool) :
    (D.changeCrossing i).statePerm s = D.statePerm (flipStateEquiv i s) := by
  simp [statePerm_def, smoothingChoice_changeCrossing]

/-- Flipping the state bit at `i` preserves the smoothed traversal across a crossing change. -/
@[simp] theorem statePerm_changeCrossing_flipStateEquiv (s : Fin n → Bool) :
    (D.changeCrossing i).statePerm (flipStateEquiv i s) = D.statePerm s := by
  rw [statePerm_changeCrossing, flipStateEquiv_flipStateEquiv]

/-- On `D.changeCrossing i`, a state `s` produces the same number of circles as
`flipStateEquiv i s` on `D`. -/
theorem stateLoopCount_changeCrossing (s : Fin n → Bool) :
    (D.changeCrossing i).stateLoopCount s = D.stateLoopCount (flipStateEquiv i s) := by
  simp [stateLoopCount_def, statePerm_changeCrossing]

/-- Flipping the state bit at `i` preserves the circle count across a crossing change. -/
@[simp] theorem stateLoopCount_changeCrossing_flipStateEquiv (s : Fin n → Bool) :
    (D.changeCrossing i).stateLoopCount (flipStateEquiv i s) = D.stateLoopCount s := by
  rw [stateLoopCount_changeCrossing, flipStateEquiv_flipStateEquiv]

end ChangeCrossing

end PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-- Switch the over- and under-strands at crossing `i` of an oriented PD-code, keeping the
orientation of every half-edge and crossing-free circle. -/
def changeCrossing (D : OrientedPDCode n) (i : Fin n) : OrientedPDCode n where
  toPDCode := D.toPDCode.changeCrossing i
  orientation := D.orientation
  orientation_edgePair := D.orientation_edgePair
  orientation_oppositeCrossingSlot := D.orientation_oppositeCrossingSlot
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := D.card_crossinglessComponents

section ChangeCrossing

variable (D : OrientedPDCode n) (i : Fin n)

/-- Forgetting orientation after switching a crossing gives the crossing change of the underlying
PD-code. -/
@[simp] theorem toPDCode_changeCrossing :
    (D.changeCrossing i).toPDCode = D.toPDCode.changeCrossing i := (rfl)

/-- Switching a crossing preserves the orientation of every half-edge. -/
@[simp] theorem changeCrossing_orientation :
    (D.changeCrossing i).orientation = D.orientation := (rfl)

/-- Switching a crossing preserves the oriented crossing-free circles. -/
@[simp] theorem changeCrossing_crossinglessComponents :
    (D.changeCrossing i).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Switching the same crossing twice returns the original oriented PD-code. -/
@[simp] theorem changeCrossing_changeCrossing :
    (D.changeCrossing i).changeCrossing i = D := by
  apply OrientedPDCode.ext <;> simp

/-- Switching two crossings of an oriented PD-code commutes. -/
theorem changeCrossing_comm (j : Fin n) :
    (D.changeCrossing i).changeCrossing j = (D.changeCrossing j).changeCrossing i := by
  apply OrientedPDCode.ext
  · exact D.toPDCode.changeCrossing_comm i j
  · rfl
  · rfl

/-- Mirroring commutes with switching a crossing of an oriented PD-code. -/
@[simp] theorem mirror_changeCrossing :
    (D.changeCrossing i).mirror = D.mirror.changeCrossing i := by
  apply OrientedPDCode.ext <;> simp

/-- Reversing component orientations commutes with switching a crossing. -/
@[simp] theorem reverse_changeCrossing :
    (D.changeCrossing i).reverse = D.reverse.changeCrossing i := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    simp
  · simp

/-- Relabelling transports an oriented crossing change to the image crossing. -/
@[simp] theorem relabel_changeCrossing {m : ℕ} (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) :
    (D.changeCrossing i).relabel half cross = (D.relabel half cross).changeCrossing (cross i) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    simp
  · simp

/-- Reading a crossing from its next slot commutes with switching an oriented crossing. -/
@[simp] theorem rotateCrossing_changeCrossing (j : Fin n) :
    (D.changeCrossing i).rotateCrossing j = (D.rotateCrossing j).changeCrossing i := by
  apply OrientedPDCode.ext <;> simp

/-- **Switching crossing `i` negates its crossing sign.** -/
@[simp] theorem crossingSign_changeCrossing_self :
    (D.changeCrossing i).crossingSign i = -D.crossingSign i := by
  rw [crossingSign_def, crossingSign_def]
  simp only [toPDCode_changeCrossing, PDCode.crossing_changeCrossing, changeCrossing_orientation,
    PDCode.changeCrossing_overPair_self]
  cases Bool.xor (D.orientation (D.crossing i 0)) (D.orientation (D.crossing i 1)) <;>
    cases D.overPair i <;> simp

/-- **Switching crossing `i` leaves the sign of every other crossing unchanged.** -/
@[simp] theorem crossingSign_changeCrossing_of_ne {j : Fin n} (hj : j ≠ i) :
    (D.changeCrossing i).crossingSign j = D.crossingSign j := by
  simp [crossingSign_def, hj]

/-- Switching crossing `i` shifts the writhe by `-2 * D.crossingSign i`. -/
theorem writhe_changeCrossing :
    (D.changeCrossing i).writhe = D.writhe - 2 * D.crossingSign i := by
  have h0 := Finset.add_sum_erase univ (D.changeCrossing i).crossingSign (mem_univ i)
  have h1 := Finset.add_sum_erase univ D.crossingSign (mem_univ i)
  have herase : ∑ j ∈ univ.erase i, (D.changeCrossing i).crossingSign j =
      ∑ j ∈ univ.erase i, D.crossingSign j :=
    Finset.sum_congr rfl fun j hj ↦ D.crossingSign_changeCrossing_of_ne i (ne_of_mem_erase hj)
  rw [writhe_def, writhe_def, ← h0, ← h1, herase, crossingSign_changeCrossing_self]
  ring

/-- Switching a positive crossing increases `negativeCrossingCount` by one. -/
theorem negativeCrossingCount_changeCrossing_of_eq_one (hi : D.crossingSign i = 1) :
    (D.changeCrossing i).negativeCrossingCount = D.negativeCrossingCount + 1 := by
  rw [negativeCrossingCount_def, negativeCrossingCount_def]
  have hmem : i ∉ filter (fun j ↦ D.crossingSign j = -1) univ := by
    simp only [mem_filter, mem_univ, true_and, hi]
    decide
  have hset : filter (fun j ↦ (D.changeCrossing i).crossingSign j = -1) univ =
      insert i (filter (fun j ↦ D.crossingSign j = -1) univ) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp only [mem_filter, mem_univ, true_and, mem_insert_self,
        crossingSign_changeCrossing_self, hi]
    · simp only [mem_filter, mem_univ, true_and, mem_insert, hj, false_or,
        D.crossingSign_changeCrossing_of_ne i hj]
  rw [hset, card_insert_of_notMem hmem]

/-- Switching a negative crossing decreases `negativeCrossingCount` by one. -/
theorem negativeCrossingCount_changeCrossing_of_eq_neg_one (hi : D.crossingSign i = -1) :
    (D.changeCrossing i).negativeCrossingCount + 1 = D.negativeCrossingCount := by
  have h := (D.changeCrossing i).negativeCrossingCount_changeCrossing_of_eq_one i (by simp [hi])
  simpa using h.symm

/-- Switching a positive crossing decreases `positiveCrossingCount` by one. -/
theorem positiveCrossingCount_changeCrossing_of_eq_one (hi : D.crossingSign i = 1) :
    (D.changeCrossing i).positiveCrossingCount + 1 = D.positiveCrossingCount := by
  have h1 := D.positiveCrossingCount_add_negativeCrossingCount
  have h2 := (D.changeCrossing i).positiveCrossingCount_add_negativeCrossingCount
  have hneg := D.negativeCrossingCount_changeCrossing_of_eq_one i hi
  omega

/-- Switching a negative crossing increases `positiveCrossingCount` by one. -/
theorem positiveCrossingCount_changeCrossing_of_eq_neg_one (hi : D.crossingSign i = -1) :
    (D.changeCrossing i).positiveCrossingCount = D.positiveCrossingCount + 1 := by
  have h1 := D.positiveCrossingCount_add_negativeCrossingCount
  have h2 := (D.changeCrossing i).positiveCrossingCount_add_negativeCrossingCount
  have hneg := D.negativeCrossingCount_changeCrossing_of_eq_neg_one i hi
  omega

/-- **Across a crossing change, flipping the state bit at `i` preserves the parity of
`#{j | s j = false} + n₋`.** Both `#{j | s j = false}` and `n₋` change by `±1`, so their sum
changes by `-2`, `0`, or `2`. -/
theorem card_false_flipStateEquiv_add_negativeCrossingCount_mod_two (s : Fin n → Bool) :
    (#{j | PDCode.flipStateEquiv i s j = false} + (D.changeCrossing i).negativeCrossingCount) % 2 =
      (#{j | s j = false} + D.negativeCrossingCount) % 2 := by
  rcases D.crossingSign_eq_one_or_neg_one i with hi | hi
  · have hn := D.negativeCrossingCount_changeCrossing_of_eq_one i hi
    rcases hsi : s i with _ | _
    · have hs := PDCode.card_false_flipStateEquiv_of_false i hsi
      omega
    · have hs := PDCode.card_false_flipStateEquiv_of_true i hsi
      omega
  · have hn := D.negativeCrossingCount_changeCrossing_of_eq_neg_one i hi
    rcases hsi : s i with _ | _
    · have hs := PDCode.card_false_flipStateEquiv_of_false i hsi
      omega
    · have hs := PDCode.card_false_flipStateEquiv_of_true i hsi
      omega

end ChangeCrossing

end OrientedPDCode

end TauCeti
