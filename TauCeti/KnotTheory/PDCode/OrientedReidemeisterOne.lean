/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ReidemeisterOne

/-!
# The first Reidemeister move on oriented PD-codes

The first Reidemeister move inserts a kink into an oriented planar-diagram code.  The old arc
orientation uniquely determines the orientations of the four new half-edges.  This file lifts
`PDCode.reidemeisterOne` to oriented codes and computes the sign of the new crossing and the
resulting change in writhe.

The Kauffman bracket is invariant under the second and third Reidemeister moves, but acquires a
factor `-A^3` or `-A⁻³` under the first.  Multiplication by `(-A^3) ^ (-writhe)` cancels that
factor.  The resulting `normalizedKauffmanBracket` is therefore invariant under the oriented
first Reidemeister move.  This is the normalization used to obtain the Jones polynomial from the
bracket.

The conventions follow L. H. Kauffman, *State models and the Jones polynomial*, Topology 26
(1987), and W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 3.

## Main definitions

* `TauCeti.OrientedPDCode.reidemeisterOne`: insert an oriented kink.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_reidemeisterOne_last`: the new crossing has sign `+1`
  exactly when its over-pair indicator is true.
* `TauCeti.OrientedPDCode.writhe_reidemeisterOne`: inserting the kink changes writhe by its
  crossing sign.
* `TauCeti.OrientedPDCode.normalizedKauffmanBracket_reidemeisterOne`: the normalized bracket is
  invariant under the move.
-/

public section

namespace TauCeti

namespace OrientedPDCode

variable {n : ℕ}

/-- The orientation of the four slots of a kink cut into an arc whose terminal half-edge has
orientation `o`.  Slots `0` and `3` point opposite to `o`; slots `1` and `2` point with `o`. -/
private def kinkOrientation (o : Bool) (slot : Fin 4) : Bool :=
  if slot = 0 ∨ slot = 3 then !o else o

private theorem kinkOrientation_oppositeCrossingSlot (o : Bool) (slot : Fin 4) :
    kinkOrientation o (PDCode.oppositeCrossingSlot slot) = !kinkOrientation o slot := by
  have hopposite : PDCode.oppositeCrossingSlot slot = slot + 2 := by
    apply Fin.ext
    exact PDCode.oppositeCrossingSlot_apply slot
  rw [hopposite]
  fin_cases slot <;> simp [kinkOrientation]

/-- Insert an oriented kink into the arc ending at `h`.  The Boolean `b` selects which opposite
pair at the new crossing is the over-strand, as for `PDCode.reidemeisterOne`. -/
def reidemeisterOne (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    OrientedPDCode (n + 1) where
  toPDCode := D.toPDCode.reidemeisterOne h b
  orientation x :=
    match (PDCode.halfEdgeSuccEquiv n).symm x with
    | .inl y => D.orientation y
    | .inr slot => kinkOrientation (D.orientation h) slot
  orientation_edgePair := by
    intro x
    obtain ⟨x, rfl⟩ := (PDCode.halfEdgeSuccEquiv n).surjective x
    rcases x with x | slot
    · by_cases hx : x = h
      · subst x
        simp [kinkOrientation]
      · by_cases hx' : x = D.edgePair.val h
        · subst x
          have horient := D.orientation_edgePair h
          simp [kinkOrientation, horient]
        · rw [D.toPDCode.reidemeisterOne_edgePair_inl_of_ne h b hx hx']
          simp
    · fin_cases slot <;> simp [kinkOrientation]
  orientation_oppositeCrossingSlot := by
    intro i slot
    induction i using Fin.lastCases with
    | last => simpa using (kinkOrientation_oppositeCrossingSlot (D.orientation h) slot)
    | cast i =>
        simp
  crossinglessComponents := D.crossinglessComponents
  crossinglessComponents_card := by simp

/-- Forgetting orientation after inserting an oriented kink gives the underlying unoriented
first Reidemeister move. -/
@[simp]
theorem reidemeisterOne_toPDCode (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    (D.reidemeisterOne h b).toPDCode = D.toPDCode.reidemeisterOne h b :=
  (rfl)

/-- Inserting an oriented kink preserves the orientation of every old half-edge. -/
@[simp]
theorem reidemeisterOne_orientation_inl (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool)
    (x : Fin (4 * n)) :
    (D.reidemeisterOne h b).orientation (PDCode.halfEdgeSuccEquiv n (.inl x)) =
      D.orientation x := by
  simp [reidemeisterOne]

/-- Slot zero of the inserted crossing points opposite to the terminal orientation of the cut
arc. -/
@[simp]
theorem reidemeisterOne_orientation_zero (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    (D.reidemeisterOne h b).orientation (PDCode.halfEdgeSuccEquiv n (.inr 0)) =
      !D.orientation h := by
  simp [reidemeisterOne, kinkOrientation]

/-- Slot one of the inserted crossing has the terminal orientation of the cut arc. -/
@[simp]
theorem reidemeisterOne_orientation_one (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    (D.reidemeisterOne h b).orientation (PDCode.halfEdgeSuccEquiv n (.inr 1)) =
      D.orientation h := by
  simp [reidemeisterOne, kinkOrientation]

/-- Slot two of the inserted crossing has the terminal orientation of the cut arc. -/
@[simp]
theorem reidemeisterOne_orientation_two (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    (D.reidemeisterOne h b).orientation (PDCode.halfEdgeSuccEquiv n (.inr 2)) =
      D.orientation h := by
  simp [reidemeisterOne, kinkOrientation]

/-- Slot three of the inserted crossing points opposite to the terminal orientation of the cut
arc. -/
@[simp]
theorem reidemeisterOne_orientation_three (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    (D.reidemeisterOne h b).orientation (PDCode.halfEdgeSuccEquiv n (.inr 3)) =
      !D.orientation h := by
  simp [reidemeisterOne, kinkOrientation]

/-- The first Reidemeister move preserves the oriented crossing-free components. -/
@[simp]
theorem reidemeisterOne_crossinglessComponents (D : OrientedPDCode n) (h : Fin (4 * n))
    (b : Bool) :
    (D.reidemeisterOne h b).crossinglessComponents = D.crossinglessComponents :=
  (rfl)

/-- Every old crossing keeps its sign after insertion of an oriented kink. -/
@[simp]
theorem crossingSign_reidemeisterOne_castSucc (D : OrientedPDCode n) (h : Fin (4 * n))
    (b : Bool) (i : Fin n) :
    (D.reidemeisterOne h b).crossingSign i.castSucc = D.crossingSign i := by
  rcases D.crossingSign_eq_one_or_neg_one i with hi | hi
  · rw [hi]
    apply (crossingSign_eq_one_iff _ _).mpr
    simpa using (D.crossingSign_eq_one_iff i).mp hi
  · rw [hi]
    apply (crossingSign_eq_neg_one_iff _ _).mpr
    simpa using (D.crossingSign_eq_neg_one_iff i).mp hi

/-- The new crossing in an oriented kink is positive exactly when its over-pair indicator is
true. -/
@[simp]
theorem crossingSign_reidemeisterOne_last (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    (D.reidemeisterOne h b).crossingSign (Fin.last n) = if b then 1 else -1 := by
  cases b
  · apply (crossingSign_eq_neg_one_iff _ _).mpr
    simp
  · apply (crossingSign_eq_one_iff _ _).mpr
    simp

/-- Inserting an oriented kink changes the writhe by the sign of the new crossing. -/
@[simp]
theorem writhe_reidemeisterOne (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    (D.reidemeisterOne h b).writhe = D.writhe + if b then 1 else -1 := by
  rw [writhe_def, writhe_def, Fin.sum_univ_castSucc]
  simp

/-- **The writhe-normalized Kauffman bracket is invariant under the oriented first Reidemeister
move.** -/
@[simp]
theorem normalizedKauffmanBracket_reidemeisterOne {R : Type*} [CommRing R]
    (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) (a : Rˣ) :
    (D.reidemeisterOne h b).normalizedKauffmanBracket a = D.normalizedKauffmanBracket a := by
  simp only [normalizedKauffmanBracket_def]
  rw [writhe_reidemeisterOne, reidemeisterOne_toPDCode,
    PDCode.kauffmanBracket_reidemeisterOne]
  have hpositive : (-((a : R) ^ 3) : R) = ((-a ^ 3 : Rˣ) : R) := by simp
  have hnegative : (-(((a⁻¹ : Rˣ) : R) ^ 3) : R) = (((-a ^ 3)⁻¹ : Rˣ) : R) := by simp
  have hcancel : (a : R) ^ 3 * ((a⁻¹ : Rˣ) : R) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    simp
  have hcancel' : ((a⁻¹ : Rˣ) : R) ^ 3 * (a : R) ^ 3 = 1 := by
    rw [mul_comm, hcancel]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
    have hexponent : -(D.writhe + -1) = -D.writhe + 1 := by omega
    rw [hexponent, zpow_add, hnegative, Units.val_mul, mul_assoc]
    simp only [zpow_neg, zpow_ofNat, pow_one, Units.val_neg, Units.val_pow_eq_pow_val,
      inv_neg, Units.inv_pow_eq_pow_inv, neg_mul, mul_neg, neg_neg, Units.mul_right_inj]
    rw [← mul_assoc, hcancel, one_mul]
  · simp only [↓reduceIte, Bool.cond_true]
    have hexponent : -(D.writhe + 1) = -D.writhe + -1 := by omega
    rw [hexponent, zpow_add, hpositive, Units.val_mul, mul_assoc]
    simp only [zpow_neg, Int.reduceNeg, zpow_ofNat, pow_one, inv_neg, Units.val_neg,
      Units.inv_pow_eq_pow_inv, Units.val_pow_eq_pow_val, neg_mul, mul_neg, neg_neg,
      Units.mul_right_inj]
    rw [← mul_assoc, hcancel', one_mul]

end OrientedPDCode

end TauCeti
