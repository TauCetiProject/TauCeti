/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.RotateCrossing

/-!
# Switching a crossing of a PD-code

Switching the over- and under-strands at a single crossing `i` of a PD-code `D` gives a new code
`TauCeti.PDCode.changeCrossing D i`: its half-edges at every crossing, its arcs, and its
crossing-free circles are those of `D`, while the over-pair indicator `overPair i` flips and all
other over-pair indicators stay unchanged. Switching every crossing at once is
`TauCeti.PDCode.mirror`.

Because the half-edge blocks and arcs do not change, a crossing change preserves the underlying
`4`-valent ribbon graph (crossing rotation, faces, and planarity) as well as the component
traversal and component count. At the switched crossing `i`, the `A`- and `B`-smoothings swap
roles, so toggling `s i` matches the states of `D.changeCrossing i` bijectively with those of `D`
while preserving the smoothed traversal `statePerm` and the circle count `stateLoopCount`.

On an oriented code (`TauCeti.OrientedPDCode.changeCrossing`), keeping the orientation of every
half-edge negates `crossingSign i`, leaves all other crossing signs unchanged, and shifts the
writhe by `-2 * D.crossingSign i`.

## Main definitions

* `TauCeti.PDCode.changeCrossing`: switch the over- and under-strands at crossing `i`.
* `TauCeti.OrientedPDCode.changeCrossing`: switch crossing `i` of an oriented PD-code while
  preserving all component orientations.

## Main results

* `TauCeti.PDCode.changeCrossing_changeCrossing`: switching the same crossing twice gives the
  original code.
* `TauCeti.PDCode.toPermutationTriple_changeCrossing` and
  `TauCeti.PDCode.isPlanar_changeCrossing`: switching a crossing preserves the underlying ribbon
  graph and planarity.
* `TauCeti.PDCode.componentCount_changeCrossing`: switching a crossing preserves the number of
  components.
* `TauCeti.PDCode.statePerm_changeCrossing` and `TauCeti.PDCode.stateLoopCount_changeCrossing`:
  toggling a state at `i` preserves its smoothed circles across the crossing change.
* `TauCeti.OrientedPDCode.crossingSign_changeCrossing_self` and
  `TauCeti.OrientedPDCode.writhe_changeCrossing`: switching crossing `i` negates its sign and
  changes the writhe by `-2 * D.crossingSign i`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2-3.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm Finset

namespace PDCode

variable {n : ℕ}

/-- Switch the over- and under-strands at crossing `i` of a PD-code, keeping the half-edges at
each crossing, the arcs, and the crossing-free circles unchanged. -/
def changeCrossing (D : PDCode n) (i : Fin n) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Function.update D.overPair i (!D.overPair i)

section ChangeCrossing

variable (D : PDCode n) (i : Fin n)

/-- Switching a crossing keeps the half-edge labelling at every crossing slot. -/
@[simp] theorem changeCrossing_halfEdge : (D.changeCrossing i).halfEdge = D.halfEdge := (rfl)

/-- Switching a crossing keeps the arcs. -/
@[simp] theorem changeCrossing_edgePair : (D.changeCrossing i).edgePair = D.edgePair := (rfl)

/-- Switching a crossing keeps the crossing-free circles. -/
@[simp] theorem changeCrossing_crossinglessComponentCount :
    (D.changeCrossing i).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- The over-pair indicator flips at the switched crossing. -/
@[simp] theorem changeCrossing_overPair_self :
    (D.changeCrossing i).overPair i = !D.overPair i := by
  simp [changeCrossing]

/-- Every other crossing keeps its over-pair indicator. -/
@[simp] theorem changeCrossing_overPair_of_ne {j : Fin n} (hj : j ≠ i) :
    (D.changeCrossing i).overPair j = D.overPair j := by
  simp [changeCrossing, hj]

-- Not `@[simp]`: `crossing_apply` and `changeCrossing_halfEdge` already prove it.
/-- Switching a crossing keeps every half-edge in the same crossing slot. -/
theorem crossing_changeCrossing (j : Fin n) (slot : Fin 4) :
    (D.changeCrossing i).crossing j slot = D.crossing j slot := by
  simp [crossing_apply]

/-- Switching the same crossing twice returns the original PD-code. -/
@[simp] theorem changeCrossing_changeCrossing :
    (D.changeCrossing i).changeCrossing i = D := by
  ext1
  · rfl
  · rfl
  · rfl
  · funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

/-- Crossing changes at distinct crossings commute. -/
theorem changeCrossing_comm {j : Fin n} (hij : i ≠ j) :
    (D.changeCrossing i).changeCrossing j = (D.changeCrossing j).changeCrossing i := by
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hij.symm]
      · simp [hki, hkj]

/-- Mirroring commutes with switching a crossing. -/
@[simp] theorem mirror_changeCrossing :
    (D.changeCrossing i).mirror = D.mirror.changeCrossing i := by
  ext1
  · simp
  · simp
  · simp
  · funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

/-- Relabelling transports a crossing change to the image crossing. -/
@[simp] theorem relabel_changeCrossing {m : ℕ} (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) :
    (D.changeCrossing i).relabel half cross = (D.relabel half cross).changeCrossing (cross i) := by
  ext1
  · simp
  · simp
  · simp
  · funext j
    by_cases hj : j = cross i
    · subst hj
      simp
    · have hj' : cross.symm j ≠ i := fun h ↦ hj (by rw [← h, Equiv.apply_symm_apply])
      simp [hj, hj']

/-- Reading a crossing from its next slot commutes with switching a crossing. -/
@[simp] theorem rotateCrossing_changeCrossing (j : Fin n) :
    (D.changeCrossing i).rotateCrossing j = (D.rotateCrossing j).changeCrossing i := by
  ext1
  · ext x
    obtain ⟨⟨k, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  · simp
  · simp
  · funext k
    by_cases hki : k = i
    · subst hki
      by_cases hkj : k = j
      · subst hkj
        simp
      · simp [hkj]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · simp [hki, hkj]

/-- Switching a crossing keeps the counterclockwise rotation of the slots at every crossing. -/
@[simp] theorem crossingRotation_changeCrossing :
    (D.changeCrossing i).crossingRotation = D.crossingRotation := by
  ext h
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  rw [← changeCrossing_halfEdge D i, crossingRotation_crossing]
  simp [crossing_apply]

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

/-- Switching a crossing keeps the passage to the opposite slot at every crossing. -/
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

/-- Switching a crossing keeps the total number of components. -/
@[simp] theorem componentCount_changeCrossing :
    (D.changeCrossing i).componentCount = D.componentCount := by
  simp [componentCount_eq]

/-- Switching a crossing keeps every family of local smoothings indexed by over-pair parities. -/
@[simp] theorem smoothingTurn_changeCrossing (b : Fin n → Bool) :
    (D.changeCrossing i).smoothingTurn b = D.smoothingTurn b := by
  ext h
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  rw [← changeCrossing_halfEdge D i, smoothingTurn_crossing]
  simp [crossing_apply]

/-- Switching crossing `i` exchanges the `A`- and `B`-smoothings at `i`, so a state `s` of the
switched code selects the same local smoothings as `Function.update s i (!s i)` on `D`. -/
@[simp] theorem smoothingChoice_changeCrossing (s : Fin n → Bool) :
    (D.changeCrossing i).smoothingChoice s = D.smoothingChoice (Function.update s i (!s i)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    cases hs : s j <;> simp [hs]
  · cases hs : s j <;> simp [hs, hj]

/-- Toggling a state at `i` matches the smoothed traversal of `D.changeCrossing i` with that of
`D`. -/
@[simp] theorem statePerm_changeCrossing (s : Fin n → Bool) :
    (D.changeCrossing i).statePerm s = D.statePerm (Function.update s i (!s i)) := by
  simp [statePerm_def]

/-- Toggling a state at `i` preserves the number of circles of the smoothed diagram across a
crossing change. -/
@[simp] theorem stateLoopCount_changeCrossing (s : Fin n → Bool) :
    (D.changeCrossing i).stateLoopCount s = D.stateLoopCount (Function.update s i (!s i)) := by
  simp [stateLoopCount_def]

end ChangeCrossing

end PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-- Switch the over- and under-strands at crossing `i` of an oriented PD-code, keeping the
orientation of every half-edge and every crossing-free circle unchanged. -/
def changeCrossing (D : OrientedPDCode n) (i : Fin n) : OrientedPDCode n where
  toPDCode := D.toPDCode.changeCrossing i
  orientation := D.orientation
  orientation_edgePair := D.orientation_edgePair
  orientation_oppositeCrossingSlot := D.orientation_oppositeCrossingSlot
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := D.card_crossinglessComponents

section ChangeCrossing

variable (D : OrientedPDCode n) (i : Fin n)

/-- Forgetting orientation after a crossing change gives the crossing change of the underlying
code. -/
@[simp] theorem toPDCode_changeCrossing :
    (D.changeCrossing i).toPDCode = D.toPDCode.changeCrossing i := (rfl)

/-- Switching a crossing keeps the orientation of every half-edge. -/
@[simp] theorem changeCrossing_orientation :
    (D.changeCrossing i).orientation = D.orientation := (rfl)

/-- Switching a crossing keeps the oriented crossing-free circles. -/
@[simp] theorem changeCrossing_crossinglessComponents :
    (D.changeCrossing i).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Switching the same crossing twice returns the original oriented PD-code. -/
@[simp] theorem changeCrossing_changeCrossing :
    (D.changeCrossing i).changeCrossing i = D := by
  apply OrientedPDCode.ext <;> simp

/-- Crossing changes at distinct crossings of an oriented code commute. -/
theorem changeCrossing_comm {j : Fin n} (hij : i ≠ j) :
    (D.changeCrossing i).changeCrossing j = (D.changeCrossing j).changeCrossing i := by
  apply OrientedPDCode.ext
  · exact D.toPDCode.changeCrossing_comm i hij
  · rfl
  · rfl

/-- Mirroring commutes with switching a crossing of an oriented code. -/
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
  simp only [crossingSign_def, PDCode.crossing_apply, toPDCode_changeCrossing,
    PDCode.changeCrossing_halfEdge, PDCode.changeCrossing_overPair_self,
    changeCrossing_orientation]
  cases Bool.xor (D.orientation (D.halfEdge (PDCode.crossingSlotEquiv n (i, 0))))
    (D.orientation (D.halfEdge (PDCode.crossingSlotEquiv n (i, 1)))) <;>
    cases D.overPair i <;> simp

/-- Switching crossing `i` leaves the sign of every other crossing unchanged. -/
@[simp] theorem crossingSign_changeCrossing_of_ne {j : Fin n} (hj : j ≠ i) :
    (D.changeCrossing i).crossingSign j = D.crossingSign j := by
  simp [crossingSign_def, hj]

/-- Switching a positive crossing decreases the positive crossing count by one. -/
theorem positiveCrossingCount_changeCrossing_add_one_of_crossingSign_eq_one
    (hi : D.crossingSign i = 1) :
    (D.changeCrossing i).positiveCrossingCount + 1 = D.positiveCrossingCount := by
  have himem : i ∈ ({j | D.crossingSign j = 1} : Finset (Fin n)) := by
    simp [-crossingSign_eq_one_iff, hi]
  have hset : ({j | (D.changeCrossing i).crossingSign j = 1} : Finset (Fin n)) =
      ({j | D.crossingSign j = 1} : Finset (Fin n)).erase i := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [-crossingSign_eq_one_iff, hi]
    · simp [-crossingSign_eq_one_iff, hj]
  rw [positiveCrossingCount_def, positiveCrossingCount_def, hset, Finset.card_erase_add_one himem]

/-- Switching a negative crossing increases the positive crossing count by one. -/
theorem positiveCrossingCount_changeCrossing_of_crossingSign_eq_neg_one
    (hi : D.crossingSign i = -1) :
    (D.changeCrossing i).positiveCrossingCount = D.positiveCrossingCount + 1 := by
  have hi' : (D.changeCrossing i).crossingSign i = 1 := by simp [hi]
  have h := (D.changeCrossing i).positiveCrossingCount_changeCrossing_add_one_of_crossingSign_eq_one
    i hi'
  simpa using h.symm

/-- Switching a positive crossing increases the negative crossing count by one. -/
theorem negativeCrossingCount_changeCrossing_of_crossingSign_eq_one
    (hi : D.crossingSign i = 1) :
    (D.changeCrossing i).negativeCrossingCount = D.negativeCrossingCount + 1 := by
  have h₁ := D.positiveCrossingCount_add_negativeCrossingCount
  have h₂ := (D.changeCrossing i).positiveCrossingCount_add_negativeCrossingCount
  have h₃ := D.positiveCrossingCount_changeCrossing_add_one_of_crossingSign_eq_one i hi
  omega

/-- Switching a negative crossing decreases the negative crossing count by one. -/
theorem negativeCrossingCount_changeCrossing_add_one_of_crossingSign_eq_neg_one
    (hi : D.crossingSign i = -1) :
    (D.changeCrossing i).negativeCrossingCount + 1 = D.negativeCrossingCount := by
  have hi' : (D.changeCrossing i).crossingSign i = 1 := by simp [hi]
  have h := (D.changeCrossing i).negativeCrossingCount_changeCrossing_of_crossingSign_eq_one i hi'
  simpa using h.symm

/-- **Switching crossing `i` changes the writhe by `-2 * D.crossingSign i`.** -/
theorem writhe_changeCrossing :
    (D.changeCrossing i).writhe = D.writhe - 2 * D.crossingSign i := by
  have hne : ∀ j ∈ ({i}ᶜ : Finset (Fin n)),
      (D.changeCrossing i).crossingSign j = D.crossingSign j :=
    fun j hj ↦ D.crossingSign_changeCrossing_of_ne i (by simpa using hj)
  rw [writhe_def, writhe_def, Fintype.sum_eq_add_sum_compl i,
    Fintype.sum_eq_add_sum_compl i D.crossingSign, Finset.sum_congr rfl hne,
    crossingSign_changeCrossing_self]
  ring

end ChangeCrossing

end OrientedPDCode

end TauCeti
