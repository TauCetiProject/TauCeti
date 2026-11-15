/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Kauffman
import Mathlib.Tactic.LinearCombination

/-!
# A trefoil PD-code and its Kauffman bracket

This file gives the standard oriented PD-code of the right-handed trefoil. All three crossings
are positive, and traversing the arc matching reads the alternating Gauss word

```
O0, U1, O2, U0, O1, U2.
```

The writhe-normalized Kauffman bracket of this diagram is then evaluated directly from its eight
states.  The result fixes the Jones-polynomial convention: after the substitution `t = A⁻⁴`, the
value is `t + t³ - t⁴`.

## Main definitions

* `TauCeti.rightHandedTrefoilArcPair`: the six arcs in crossing-slot coordinates.
* `TauCeti.rightHandedTrefoilPDCode`: the standard three-crossing oriented PD-code.

## Main results

* `TauCeti.rightHandedTrefoilPDCode_writhe`: the diagram has writhe three.
* `TauCeti.rightHandedTrefoilPDCode_componentCount`: the diagram is a knot.
* `TauCeti.normalizedKauffmanBracket_rightHandedTrefoilPDCode`: its normalized bracket is
  `A⁻⁴ + A⁻¹² - A⁻¹⁶`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3.
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

/-- The six arcs of the standard trefoil diagram, expressed directly on crossing-slot pairs. -/
def rightHandedTrefoilArcPair : PerfectMatching (Fin 3 × Fin 4) :=
  PerfectMatching.mk
    (Equiv.swap (0, 2) (1, 1) * Equiv.swap (1, 3) (2, 0) *
      Equiv.swap (2, 2) (0, 1) * Equiv.swap (0, 3) (1, 0) *
      Equiv.swap (1, 2) (2, 1) * Equiv.swap (2, 3) (0, 0))
    (by decide) (by decide)

/-- The six arcs paired by `rightHandedTrefoilArcPair`, stated in both directions so that the
partner of each of the twelve crossing slots is available to `simp`. -/
@[simp]
theorem rightHandedTrefoilArcPair_pairs :
    rightHandedTrefoilArcPair.val (0, 2) = (1, 1) ∧
      rightHandedTrefoilArcPair.val (1, 1) = (0, 2) ∧
      rightHandedTrefoilArcPair.val (1, 3) = (2, 0) ∧
      rightHandedTrefoilArcPair.val (2, 0) = (1, 3) ∧
      rightHandedTrefoilArcPair.val (2, 2) = (0, 1) ∧
      rightHandedTrefoilArcPair.val (0, 1) = (2, 2) ∧
      rightHandedTrefoilArcPair.val (0, 3) = (1, 0) ∧
      rightHandedTrefoilArcPair.val (1, 0) = (0, 3) ∧
      rightHandedTrefoilArcPair.val (1, 2) = (2, 1) ∧
      rightHandedTrefoilArcPair.val (2, 1) = (1, 2) ∧
      rightHandedTrefoilArcPair.val (2, 3) = (0, 0) ∧
      rightHandedTrefoilArcPair.val (0, 0) = (2, 3) := by
  simp [rightHandedTrefoilArcPair, PerfectMatching.val_mk, Equiv.swap_apply_def]

/-- The slot matching transported to the twelve finite half-edge labels used by `PDCode`. -/
private def trefoilEdgePair : PerfectMatching (Fin 12) :=
  PerfectMatching.congr (PDCode.crossingSlotEquiv 3) rightHandedTrefoilArcPair

private theorem trefoilSlotPair_orientation (p : Fin 3 × Fin 4) :
    decide (2 ≤ (rightHandedTrefoilArcPair.val p).2.val) = !decide (2 ≤ p.2.val) := by
  rcases p with ⟨i, slot⟩
  fin_cases i <;> fin_cases slot <;>
    simp [rightHandedTrefoilArcPair, PerfectMatching.val_mk, Equiv.swap_apply_def]

/-- The standard three-crossing oriented PD-code of the right-handed trefoil. Crossing slots are
numbered consecutively, slots zero and two form the over-strand, and slots two and three point out
of each crossing. The arc matching gives the alternating Gauss word `O0, U1, O2, U0, O1, U2`. -/
def rightHandedTrefoilPDCode : OrientedPDCode 3 where
  halfEdge := 1
  edgePair := trefoilEdgePair
  crossinglessComponentCount := 0
  overPair := fun _ => false
  orientation := fun h => decide (2 ≤ h.val % 4)
  orientation_edgePair := by
    intro h
    let p := (PDCode.crossingSlotEquiv 3).symm h
    have hp : h = PDCode.crossingSlotEquiv 3 p :=
      ((PDCode.crossingSlotEquiv 3).apply_symm_apply h).symm
    rw [hp]
    rw [trefoilEdgePair, PerfectMatching.congr_val_apply_apply,
      PDCode.crossingSlotEquiv_apply_val_mod_four, PDCode.crossingSlotEquiv_apply_val_mod_four]
    exact trefoilSlotPair_orientation p
  orientation_oppositeCrossingSlot := by
    intro i slot
    rw [one_apply, one_apply, PDCode.crossingSlotEquiv_apply_val_mod_four,
      PDCode.crossingSlotEquiv_apply_val_mod_four, ← decide_not]
    exact Bool.decide_congr (PDCode.two_le_oppositeCrossingSlot_val_iff slot)
  crossinglessComponents := 0
  card_crossinglessComponents := rfl

/-- The trefoil code numbers half-edges consecutively by their crossing slots. -/
@[simp]
theorem rightHandedTrefoilPDCode_halfEdge : rightHandedTrefoilPDCode.halfEdge = 1 :=
  (rfl)

/-- The trefoil code has no crossing-free component. -/
@[simp]
theorem rightHandedTrefoilPDCode_crossinglessComponentCount :
    rightHandedTrefoilPDCode.crossinglessComponentCount = 0 :=
  (rfl)

/-- Slots zero and two form the over-strand at each crossing of the trefoil code. -/
@[simp]
theorem rightHandedTrefoilPDCode_overPair (i : Fin 3) :
    rightHandedTrefoilPDCode.overPair i = false :=
  (rfl)

/-- The arc partner of a crossing slot is the partner prescribed by
`rightHandedTrefoilArcPair`. -/
@[simp]
theorem rightHandedTrefoilPDCode_edgePair_apply (i : Fin 3) (slot : Fin 4) :
    rightHandedTrefoilPDCode.edgePair.val (PDCode.crossingSlotEquiv 3 (i, slot)) =
      PDCode.crossingSlotEquiv 3 (rightHandedTrefoilArcPair.val (i, slot)) := by
  simp only [rightHandedTrefoilPDCode]
  rw [trefoilEdgePair, PerfectMatching.congr_val_apply_apply]

/-- At every crossing, slots zero and one point into the crossing while slots two and three point
out of it. -/
@[simp]
theorem rightHandedTrefoilPDCode_orientation_crossing (i : Fin 3) (slot : Fin 4) :
    rightHandedTrefoilPDCode.orientation (PDCode.crossingSlotEquiv 3 (i, slot)) =
      decide (2 ≤ slot.val) := by
  simp only [rightHandedTrefoilPDCode]
  rw [PDCode.crossingSlotEquiv_apply_val_mod_four]

/-- Every crossing of the right-handed trefoil PD-code is positive. -/
@[simp]
theorem rightHandedTrefoilPDCode_crossingSign (i : Fin 3) :
    rightHandedTrefoilPDCode.crossingSign i = 1 := by
  apply (OrientedPDCode.crossingSign_eq_one_iff _ _).mpr
  simp only [PDCode.crossing_apply, rightHandedTrefoilPDCode_halfEdge,
    one_apply, rightHandedTrefoilPDCode_overPair]
  rw [rightHandedTrefoilPDCode_orientation_crossing,
    rightHandedTrefoilPDCode_orientation_crossing]
  decide

/-- The standard right-handed trefoil diagram has writhe three. -/
@[simp]
theorem rightHandedTrefoilPDCode_writhe : rightHandedTrefoilPDCode.writhe = 3 := by
  rw [OrientedPDCode.writhe_def]
  simp

private theorem rightHandedTrefoilPDCode_smoothingChoice (s : Fin 3 → Bool) :
    rightHandedTrefoilPDCode.toPDCode.smoothingChoice s = fun i ↦ !(s i) := by
  funext i
  cases hs : s i <;> simp [hs]

private theorem rightHandedTrefoilPDCode_statePerm (s : Fin 3 → Bool) :
    rightHandedTrefoilPDCode.toPDCode.statePerm s =
      (PDCode.crossingSlotEquiv 3).permCongr
        ((Equiv.prodCongrRight fun i : Fin 3 ↦ PDCode.slotSmoothing (!(s i))) *
          rightHandedTrefoilArcPair.val) := by
  rw [PDCode.statePerm_def, PDCode.smoothingTurn_def,
    rightHandedTrefoilPDCode_smoothingChoice]
  simp [rightHandedTrefoilPDCode, trefoilEdgePair, PerfectMatching.congr_val,
    ← Equiv.permCongr_mul]

private theorem trefoilSlotSmoothing (b₀ b₁ b₂ : Bool) :
    (fun i : Fin 3 ↦ PDCode.slotSmoothing (!(![b₀, b₁, b₂] i))) =
      ![PDCode.slotSmoothing (!b₀), PDCode.slotSmoothing (!b₁),
        PDCode.slotSmoothing (!b₂)] := by
  funext i
  fin_cases i <;> rfl

private def trefoilStateForest (b₀ b₁ b₂ : Bool) :
    List ((Fin 3 × Fin 4) × (Fin 3 × Fin 4)) :=
  match b₀, b₁, b₂ with
  | false, false, false =>
      [((1, 3), (2, 1)), ((1, 2), (2, 0)), ((0, 3), (1, 1)), ((0, 2), (1, 0)),
        ((0, 1), (2, 3)), ((0, 0), (2, 2))]
  | false, false, true =>
      [((0, 3), (1, 1)), ((0, 2), (1, 0)), ((1, 3), (2, 3)), ((2, 1), (1, 3)),
        ((0, 1), (2, 1)), ((1, 2), (2, 2)), ((2, 0), (1, 2)), ((0, 0), (2, 0))]
  | false, true, false =>
      [((2, 1), (1, 1)), ((1, 3), (2, 1)), ((0, 3), (1, 3)), ((2, 0), (1, 0)),
        ((1, 2), (2, 0)), ((0, 2), (1, 2)), ((0, 1), (2, 3)), ((0, 0), (2, 2))]
  | false, true, true =>
      [((1, 3), (2, 3)), ((0, 3), (1, 3)), ((1, 1), (0, 3)), ((2, 1), (1, 1)),
        ((0, 1), (2, 1)), ((1, 2), (2, 2)), ((0, 2), (1, 2)), ((1, 0), (0, 2)),
        ((2, 0), (1, 0)), ((0, 0), (2, 0))]
  | true, false, false =>
      [((1, 3), (2, 1)), ((1, 2), (2, 0)), ((0, 3), (1, 1)), ((2, 3), (0, 3)),
        ((0, 1), (2, 3)), ((0, 2), (1, 0)), ((2, 2), (0, 2)), ((0, 0), (2, 2))]
  | true, false, true =>
      [((0, 3), (1, 1)), ((2, 3), (0, 3)), ((1, 3), (2, 3)), ((2, 1), (1, 3)),
        ((0, 1), (2, 1)), ((0, 2), (1, 0)), ((2, 2), (0, 2)), ((1, 2), (2, 2)),
        ((2, 0), (1, 2)), ((0, 0), (2, 0))]
  | true, true, false =>
      [((2, 1), (1, 1)), ((1, 3), (2, 1)), ((0, 3), (1, 3)), ((2, 3), (0, 3)),
        ((0, 1), (2, 3)), ((2, 0), (1, 0)), ((1, 2), (2, 0)), ((0, 2), (1, 2)),
        ((2, 2), (0, 2)), ((0, 0), (2, 2))]
  | true, true, true =>
      [((1, 3), (2, 3)), ((0, 3), (1, 3)), ((1, 2), (2, 2)), ((0, 2), (1, 2)),
        ((2, 1), (1, 1)), ((0, 1), (2, 1)), ((2, 0), (1, 0)), ((0, 0), (2, 0))]

private theorem trefoilStateForest_isForest (b₀ b₁ b₂ : Bool) :
    (trefoilStateForest b₀ b₁ b₂).IsSwapForest := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;>
    simp [trefoilStateForest, Equiv.swap_apply_def]

private theorem trefoilStatePerm_eq_prod_swap (b₀ b₁ b₂ : Bool) :
    (Equiv.prodCongrRight ![PDCode.slotSmoothing (!b₀), PDCode.slotSmoothing (!b₁),
        PDCode.slotSmoothing (!b₂)]) * rightHandedTrefoilArcPair.val =
      ((trefoilStateForest b₀ b₁ b₂).reverse.map (Function.uncurry Equiv.swap)).prod := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;>
    simp only [Bool.not_false, Bool.not_true, PDCode.slotSmoothing_false,
      PDCode.slotSmoothing_true, rightHandedTrefoilArcPair, PerfectMatching.val_mk,
      trefoilStateForest] <;>
    decide

private theorem trefoilStateForest_orbitCount (b₀ b₁ b₂ : Bool) :
    orbitCount ((trefoilStateForest b₀ b₁ b₂).reverse.map (Function.uncurry Equiv.swap)).prod +
      (trefoilStateForest b₀ b₁ b₂).length = 12 := by
  simpa using (trefoilStateForest_isForest b₀ b₁ b₂).orbitCount_add_length

private def trefoilComponentForest : List ((Fin 3 × Fin 4) × (Fin 3 × Fin 4)) :=
  [((1, 2), (2, 3)), ((0, 3), (1, 2)), ((2, 2), (0, 3)), ((1, 3), (2, 2)),
    ((0, 2), (1, 3)), ((2, 0), (1, 1)), ((0, 1), (2, 0)), ((1, 0), (0, 1)),
    ((2, 1), (1, 0)), ((0, 0), (2, 1))]

private theorem trefoilComponentForest_isForest : trefoilComponentForest.IsSwapForest := by
  simp [trefoilComponentForest, Equiv.swap_apply_def]

private theorem trefoilComponentSlotPerm_eq_prod_swap :
    (Equiv.prodCongr (Equiv.refl (Fin 3)) PDCode.oppositeCrossingSlot) *
      rightHandedTrefoilArcPair.val =
      (trefoilComponentForest.reverse.map (Function.uncurry Equiv.swap)).prod := by
  rw [PDCode.oppositeCrossingSlot_eq_swap_mul_swap]
  apply Equiv.ext
  rintro ⟨i, slot⟩
  fin_cases i <;> fin_cases slot <;>
    simp [rightHandedTrefoilArcPair,
      PerfectMatching.val_mk, trefoilComponentForest, Equiv.swap_apply_def]

private theorem trefoilComponentPerm_eq_prod_swap :
    rightHandedTrefoilPDCode.toPDCode.componentPerm =
      (PDCode.crossingSlotEquiv 3).permCongr
        (trefoilComponentForest.reverse.map (Function.uncurry Equiv.swap)).prod := by
  rw [PDCode.componentPerm_def, PDCode.crossingTurn_def]
  simp [rightHandedTrefoilPDCode, trefoilEdgePair, PerfectMatching.congr_val,
    trefoilComponentSlotPerm_eq_prod_swap, ← Equiv.permCongr_mul]

/-- The standard trefoil PD-code represents one link component. -/
@[simp]
theorem rightHandedTrefoilPDCode_componentCount :
    rightHandedTrefoilPDCode.toPDCode.componentCount = 1 := by
  rw [PDCode.componentCount_eq, PDCode.crossingComponentCount_def,
    trefoilComponentPerm_eq_prod_swap, Equiv.orbitCount_permCongr,
    rightHandedTrefoilPDCode_crossinglessComponentCount]
  have hcount := trefoilComponentForest_isForest.orbitCount_add_length
  norm_num [trefoilComponentForest] at hcount ⊢
  omega

private theorem rightHandedTrefoilPDCode_stateLoopCount (b₀ b₁ b₂ : Bool) :
    rightHandedTrefoilPDCode.toPDCode.stateLoopCount ![b₀, b₁, b₂] =
      match b₀, b₁, b₂ with
      | false, false, false => 3
      | false, false, true => 2
      | false, true, false => 2
      | false, true, true => 1
      | true, false, false => 2
      | true, false, true => 1
      | true, true, false => 1
      | true, true, true => 2 := by
  have hcount := trefoilStateForest_orbitCount b₀ b₁ b₂
  cases b₀ <;> cases b₁ <;> cases b₂ <;>
    rw [PDCode.stateLoopCount_def, rightHandedTrefoilPDCode_statePerm,
      trefoilSlotSmoothing, Equiv.orbitCount_permCongr,
      rightHandedTrefoilPDCode_crossinglessComponentCount] <;>
    rw [trefoilStatePerm_eq_prod_swap] <;>
    norm_num [trefoilStateForest] at hcount ⊢ <;>
    omega

/-- The Kauffman bracket of the standard right-handed trefoil is
`-A⁵ - A⁻³ + A⁻⁷`. -/
@[simp]
theorem kauffmanBracket_rightHandedTrefoilPDCode {R : Type*} [CommRing R] (a : Rˣ) :
    rightHandedTrefoilPDCode.toPDCode.kauffmanBracket a =
      -(a : R) ^ 5 - ((a⁻¹ : Rˣ) : R) ^ 3 + ((a⁻¹ : Rˣ) : R) ^ 7 := by
  let stateEquiv := (Fin.consEquiv fun _ : Fin 3 ↦ Bool).symm.trans
    (Equiv.prodCongr (Equiv.refl Bool) (finTwoArrowEquiv Bool))
  have stateEquiv_symm_apply (b : Bool × (Bool × Bool)) :
      stateEquiv.symm b = ![b.1, b.2.1, b.2.2] := by
    rcases b with ⟨b₀, b₁, b₂⟩
    rfl
  rw [PDCode.kauffmanBracket_def, ← stateEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, stateEquiv_symm_apply,
    rightHandedTrefoilPDCode_stateLoopCount, PDCode.stateWeight_def,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.isValue, Bool.cond_false,
    Bool.cond_true, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Nat.reduceSub, pow_zero, pow_one, mul_one,
    TemperleyLieb.jonesDelta_def]
  simp [mul_assoc]
  linear_combination
    ((a : R) ^ 3 * ((a⁻¹ : Rˣ) : R) ^ 2 +
      2 * (a : R) * ((a⁻¹ : Rˣ) : R) ^ 4 - 3 * (a : R) +
      2 * ((a⁻¹ : Rˣ) : R) ^ 3) * a.mul_inv

/-- The writhe-normalized Kauffman bracket of the right-handed trefoil is
`A⁻⁴ + A⁻¹² - A⁻¹⁶`. With `t = A⁻⁴`, this is `t + t³ - t⁴`. -/
@[simp]
theorem normalizedKauffmanBracket_rightHandedTrefoilPDCode {R : Type*} [CommRing R]
    (a : Rˣ) :
    rightHandedTrefoilPDCode.normalizedKauffmanBracket a =
      ((a⁻¹ : Rˣ) : R) ^ 4 + ((a⁻¹ : Rˣ) : R) ^ 12 -
        ((a⁻¹ : Rˣ) : R) ^ 16 := by
  rw [OrientedPDCode.normalizedKauffmanBracket_def,
    rightHandedTrefoilPDCode_writhe, kauffmanBracket_rightHandedTrefoilPDCode]
  norm_num [zpow_neg, mul_assoc]
  have hunit : (a⁻¹ : Rˣ) ^ 9 * a ^ 5 = a⁻¹ ^ 4 := by
    group
  have hcoe := congrArg (fun u : Rˣ ↦ (u : R)) hunit
  norm_num at hcoe
  ring_nf
  rw [hcoe]

end TauCeti
