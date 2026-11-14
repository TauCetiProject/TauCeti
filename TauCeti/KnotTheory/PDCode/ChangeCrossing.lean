/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.KnotTheory.PDCode.Planar
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert

/-!
# Switching a single crossing of a PD-code

`TauCeti.PDCode.changeCrossing D c` switches the over- and under-strands at a single crossing `c`
of a PD-code `D`, leaving all other crossings, all arcs, and all crossing-free circles unchanged.
It preserves the underlying `4`-valent ribbon graph, planarity, and component count, while
exchanging the `A`- and `B`-smoothings at `c` via the involutive state permutation
`TauCeti.PDCode.changeCrossingStateEquiv c`.

On an oriented PD-code (`TauCeti.OrientedPDCode.changeCrossing`), switching `c` keeps all
half-edge directions and crossing-free circle orientations unchanged, negates `crossingSign` at `c`
while preserving all other crossing signs, transforms `seifertState` by
`changeCrossingStateEquiv c`, and flips the parity sign `(-1) ^ n₋` of `negativeCrossingCount`.

## Main definitions

* `TauCeti.PDCode.changeCrossing`: switch the over- and under-strands at crossing `c`.
* `TauCeti.PDCode.changeCrossingStateEquiv`: the involutive permutation of `Fin n → Bool`
  complementing the state at `c`.
* `TauCeti.OrientedPDCode.changeCrossing`: switch over- and under-strands at `c` on an oriented
  PD-code.

## Main results

* `TauCeti.PDCode.toPermutationTriple_changeCrossing`, `TauCeti.PDCode.isPlanar_changeCrossing`,
  `TauCeti.PDCode.componentCount_changeCrossing`: changing a crossing preserves the ribbon graph,
  planarity, and component count.
* `TauCeti.PDCode.stateLoopCount_changeCrossing_changeCrossingStateEquiv`: the `A`/`B` state
  bijection preserves the number of state loops in every state.
* `TauCeti.PDCode.negOnePow_card_false_changeCrossingStateEquiv`: complementing a state at `c`
  flips `(-1) ^ |S|`.
* `TauCeti.OrientedPDCode.seifertState_changeCrossing`,
  `TauCeti.OrientedPDCode.negOnePow_negativeCrossingCount_changeCrossing`: switching `c` flips the
  Seifert state at `c` and negates `(-1) ^ n₋`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 and
  Chapter 3.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm
open scoped Finset

namespace PDCode

variable {n : ℕ}

/-- **Crossing change.** Switch the over- and under-strands at crossing `c`, leaving all other
crossings, all arcs, and all crossing-free circles unchanged. -/
def changeCrossing (D : PDCode n) (c : Fin n) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Function.update D.overPair c (!D.overPair c)

/-- Changing a crossing preserves the half-edge enumeration. -/
@[simp] theorem changeCrossing_halfEdge (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).halfEdge = D.halfEdge := (rfl)

/-- Changing a crossing preserves the arc pairing. -/
@[simp] theorem changeCrossing_edgePair (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).edgePair = D.edgePair := (rfl)

/-- Changing a crossing preserves the number of crossing-free circles. -/
@[simp] theorem changeCrossing_crossinglessComponentCount (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- Changing crossing `c` complements `overPair` at `c`. -/
@[simp] theorem changeCrossing_overPair_self (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).overPair c = !D.overPair c := by
  simp [changeCrossing]

/-- Changing crossing `c` leaves `overPair` unchanged at every other crossing. -/
@[simp] theorem changeCrossing_overPair_of_ne (D : PDCode n) {c i : Fin n} (hi : i ≠ c) :
    (D.changeCrossing c).overPair i = D.overPair i := by
  simp [changeCrossing, hi]

/-- Changing a crossing preserves the half-edges at every crossing slot. -/
theorem crossing_changeCrossing (D : PDCode n) (c i : Fin n) (k : Fin 4) :
    (D.changeCrossing c).crossing i k = D.crossing i k := by
  rw [crossing_apply, crossing_apply, changeCrossing_halfEdge]

/-- Changing the same crossing twice recovers the original PD-code. -/
@[simp] theorem changeCrossing_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).changeCrossing c = D := by
  ext : 1 <;> simp [changeCrossing]

/-- Reflection commutes with switching a crossing. -/
@[simp] theorem mirror_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).mirror = D.mirror.changeCrossing c := by
  apply PDCode.ext <;> try simp
  funext i
  by_cases hi : i = c
  · subst hi; simp
  · simp [hi]

/-- Changing a crossing preserves the opposite-slot involution `crossingTurn`. -/
@[simp] theorem crossingTurn_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).crossingTurn = D.crossingTurn := by
  rw [crossingTurn_def, crossingTurn_def, changeCrossing_halfEdge]

/-- Changing a crossing preserves the directed component traversal permutation. -/
@[simp] theorem componentPerm_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).componentPerm = D.componentPerm := by
  rw [componentPerm_def, componentPerm_def, crossingTurn_changeCrossing, changeCrossing_edgePair]

/-- Changing a crossing preserves the number of crossing-bearing components. -/
@[simp] theorem crossingComponentCount_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).crossingComponentCount = D.crossingComponentCount := by
  rw [crossingComponentCount_def, crossingComponentCount_def, componentPerm_changeCrossing]

/-- Changing a crossing preserves the total number of link components. -/
@[simp] theorem componentCount_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).componentCount = D.componentCount := by
  rw [componentCount_eq, componentCount_eq, crossingComponentCount_changeCrossing,
    changeCrossing_crossinglessComponentCount]

/-- Changing a crossing preserves the cyclic crossing rotation. -/
@[simp] theorem crossingRotation_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).crossingRotation = D.crossingRotation := by
  rw [crossingRotation_def, crossingRotation_def, changeCrossing_halfEdge]

/-- Changing a crossing preserves the face permutation. -/
@[simp] theorem facePerm_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).facePerm = D.facePerm := by
  rw [facePerm_def, facePerm_def, changeCrossing_edgePair, crossingRotation_changeCrossing]

/-- Changing a crossing preserves the underlying ribbon-graph permutation triple. -/
@[simp] theorem toPermutationTriple_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).toPermutationTriple = D.toPermutationTriple := by
  apply PermutationTriple.ext_of_two <;> simp

/-- Changing a crossing preserves planarity. -/
@[simp] theorem isPlanar_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).IsPlanar ↔ D.IsPlanar := by
  rw [isPlanar_def, isPlanar_def, toPermutationTriple_changeCrossing]

/-- **The `A`/`B` state bijection of a crossing change**: exchange the `A`- and `B`-smoothings at
crossing `c` while leaving the state unchanged at every other crossing. -/
def changeCrossingStateEquiv (c : Fin n) : Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun s ↦ Function.update s c (!s c)) fun s ↦ by simp

/-- Applying `changeCrossingStateEquiv c` updates the state at `c` by its Boolean negation. -/
theorem changeCrossingStateEquiv_apply (c : Fin n) (s : Fin n → Bool) :
    changeCrossingStateEquiv c s = Function.update s c (!s c) :=
  congrFun (Function.Involutive.coe_toPerm _) s

/-- At the changed crossing `c`, `changeCrossingStateEquiv` complements the state value. -/
@[simp] theorem changeCrossingStateEquiv_apply_self (c : Fin n) (s : Fin n → Bool) :
    changeCrossingStateEquiv c s c = !s c := by
  simp [changeCrossingStateEquiv_apply]

/-- Away from `c`, `changeCrossingStateEquiv` leaves the state value unchanged. -/
@[simp] theorem changeCrossingStateEquiv_apply_of_ne {c i : Fin n} (hi : i ≠ c)
    (s : Fin n → Bool) :
    changeCrossingStateEquiv c s i = s i := by
  simp [changeCrossingStateEquiv_apply, hi]

/-- `changeCrossingStateEquiv` is its own inverse. -/
@[simp] theorem changeCrossingStateEquiv_symm (c : Fin n) :
    (changeCrossingStateEquiv c).symm = changeCrossingStateEquiv c :=
  Function.Involutive.toPerm_symm _

/-- Applying `changeCrossingStateEquiv c` twice recovers the original state. -/
@[simp] theorem changeCrossingStateEquiv_apply_apply (c : Fin n) (s : Fin n → Bool) :
    changeCrossingStateEquiv c (changeCrossingStateEquiv c s) = s := by
  ext i
  by_cases hi : i = c
  · subst hi; simp
  · simp [hi]

/-- Composing `changeCrossingStateEquiv c` with itself gives the identity equivalence. -/
@[simp] theorem changeCrossingStateEquiv_trans_self (c : Fin n) :
    (changeCrossingStateEquiv c).trans (changeCrossingStateEquiv c) = Equiv.refl _ := by
  ext s i
  simp

/-- Complementing the state at `c` selects the same local smoothings in `D.changeCrossing c` as the
original state selects in `D`. -/
@[simp] theorem smoothingChoice_changeCrossing_changeCrossingStateEquiv (D : PDCode n) (c : Fin n)
    (s : Fin n → Bool) :
    (D.changeCrossing c).smoothingChoice (changeCrossingStateEquiv c s) = D.smoothingChoice s := by
  funext i
  by_cases hi : i = c
  · subst hi
    cases hs : s i <;> simp [hs]
  · cases hs : s i <;> simp [hs, hi]

/-- The `A`/`B` state bijection preserves the smoothed traversal permutation. -/
@[simp] theorem statePerm_changeCrossing_changeCrossingStateEquiv (D : PDCode n) (c : Fin n)
    (s : Fin n → Bool) :
    (D.changeCrossing c).statePerm (changeCrossingStateEquiv c s) = D.statePerm s := by
  simp [statePerm_def, smoothingTurn_def]

/-- The `A`/`B` state bijection preserves the number of circles in every state. -/
@[simp] theorem stateLoopCount_changeCrossing_changeCrossingStateEquiv (D : PDCode n) (c : Fin n)
    (s : Fin n → Bool) :
    (D.changeCrossing c).stateLoopCount (changeCrossingStateEquiv c s) = D.stateLoopCount s := by
  simp [stateLoopCount_def]

/-- Complementing a state at `c` flips the sign `(-1) ^ |S|` of the `B`-smoothing count. -/
theorem negOnePow_card_false_changeCrossingStateEquiv (c : Fin n) (s : Fin n → Bool) :
    (#{i | changeCrossingStateEquiv c s i = false} : ℤ).negOnePow =
      -(#{i | s i = false} : ℤ).negOnePow := by
  apply Int.negOnePow_eq_neg_of_odd_sub
  have hcompl : ∀ j ∈ ({c}ᶜ : Finset (Fin n)),
      (if changeCrossingStateEquiv c s j = false then (1 : ℤ) else 0) =
        if s j = false then 1 else 0 :=
    fun j hj ↦ by rw [changeCrossingStateEquiv_apply_of_ne (by simpa using hj)]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, Fintype.sum_eq_add_sum_compl c,
    Fintype.sum_eq_add_sum_compl c (fun i ↦ if s i = false then (1 : ℤ) else 0),
    Finset.sum_congr rfl hcompl, add_sub_add_right_eq_sub, changeCrossingStateEquiv_apply_self]
  cases s c
  · exact ⟨-1, by decide⟩
  · exact ⟨0, by decide⟩

end PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-- **Oriented crossing change.** Switch the over- and under-strands at crossing `c` while keeping
every half-edge direction and every crossing-free component orientation unchanged. -/
def changeCrossing (D : OrientedPDCode n) (c : Fin n) : OrientedPDCode n where
  toPDCode := D.toPDCode.changeCrossing c
  orientation := D.orientation
  orientation_edgePair := D.orientation_edgePair
  orientation_oppositeCrossingSlot := D.orientation_oppositeCrossingSlot
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := D.card_crossinglessComponents

/-- Forgetting orientation commutes with `changeCrossing`. -/
@[simp] theorem toPDCode_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).toPDCode = D.toPDCode.changeCrossing c := (rfl)

/-- Changing an oriented crossing keeps all half-edge directions unchanged. -/
@[simp] theorem orientation_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).orientation = D.orientation := (rfl)

/-- Changing an oriented crossing keeps the crossing-free component orientations unchanged. -/
@[simp] theorem crossinglessComponents_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Changing the same oriented crossing twice recovers the original oriented PD-code. -/
@[simp] theorem changeCrossing_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).changeCrossing c = D := by
  ext <;> simp

/-- Reflection commutes with switching an oriented crossing. -/
@[simp] theorem mirror_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).mirror = D.mirror.changeCrossing c := by
  ext <;> simp

/-- Reversing all component orientations commutes with switching an oriented crossing. -/
@[simp] theorem reverse_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).reverse = D.reverse.changeCrossing c := by
  ext <;> simp

/-- Changing crossing `c` negates its crossing sign. -/
@[simp] theorem crossingSign_changeCrossing_self (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).crossingSign c = -D.crossingSign c := by
  rw [crossingSign_def, crossingSign_def]
  simp only [toPDCode_changeCrossing, PDCode.crossing_changeCrossing, orientation_changeCrossing,
    PDCode.changeCrossing_overPair_self]
  cases Bool.xor (D.orientation (D.crossing c 0)) (D.orientation (D.crossing c 1)) <;>
    cases D.overPair c <;> decide

/-- Changing crossing `c` preserves the sign of every other crossing. -/
@[simp] theorem crossingSign_changeCrossing_of_ne (D : OrientedPDCode n) {c i : Fin n}
    (hi : i ≠ c) :
    (D.changeCrossing c).crossingSign i = D.crossingSign i := by
  rw [crossingSign_def, crossingSign_def]
  simp [hi]

/-- Switching crossing `c` complements the Seifert state at `c` and leaves it unchanged
elsewhere. -/
@[simp] theorem seifertState_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).seifertState = PDCode.changeCrossingStateEquiv c D.seifertState := by
  funext i
  rw [Bool.eq_iff_iff]
  by_cases hi : i = c
  · subst hi
    rcases D.crossingSign_eq_one_or_neg_one i with h | h <;> simp [h]
  · simp [hi]

/-- Changing a single crossing flips the parity sign `(-1) ^ n₋` of the negative crossing count. -/
theorem negOnePow_negativeCrossingCount_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    ((D.changeCrossing c).negativeCrossingCount : ℤ).negOnePow =
      -(D.negativeCrossingCount : ℤ).negOnePow := by
  have hneg (E : OrientedPDCode n) :
      E.negativeCrossingCount = #{i | E.seifertState i = false} := by
    simp only [negativeCrossingCount_def, seifertState_eq_false_iff]
  rw [hneg, hneg, seifertState_changeCrossing]
  exact PDCode.negOnePow_card_false_changeCrossingStateEquiv c D.seifertState

end OrientedPDCode

end TauCeti
