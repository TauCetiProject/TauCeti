/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import TauCeti.Algebra.Cluster.BFZ.Word

/-!
# The extended exchange matrix of a BFZ double word

The rows are the prefixed positions of the signed word and the columns are the exchangeable
positions. Horizontal edges join a position to its successor of the same colour. Inclined edges
are governed by the order of the successors and the signs at the later endpoint and the first
successor. The entry uses the Cartan coefficient with column colour first, converting the BFZ
paper's convention to that of `RootPairing.Base.cartanMatrix`.

## References

* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Mathematical Journal 126 (2005), Definitions 2.2–2.3 and Remark 2.4.
-/

public section

namespace List

variable {r : ℕ}

/-- The ordered endpoints, interval and sign condition for an inclined edge. The weight of such
an edge is supplied separately by the corresponding Cartan entry. -/
def IsBfzInclinedPair (w : List (Fin r × Bool)) (k l : Fin (r + w.length)) : Prop :=
  k < l ∧ ∃ j : Fin (r + w.length), l < j ∧
    ((bfzSuccessor w k = j ∧ (j : WithTop (Fin (r + w.length))) < bfzSuccessor w l ∧
        (bfzLetter w l).2 = (bfzLetter w j).2) ∨
      (bfzSuccessor w l = j ∧ (j : WithTop (Fin (r + w.length))) < bfzSuccessor w k ∧
        (bfzLetter w l).2 ≠ (bfzLetter w j).2))

/-- An inclined pair is strictly ordered and has a genuine first successor after the later
position, with equal signs when the left successor comes first and opposite signs otherwise. -/
theorem isBfzInclinedPair_iff (w : List (Fin r × Bool)) (k l : Fin (r + w.length)) :
    IsBfzInclinedPair w k l ↔
      k < l ∧ ∃ j : Fin (r + w.length), l < j ∧
        ((bfzSuccessor w k = j ∧ (j : WithTop (Fin (r + w.length))) < bfzSuccessor w l ∧
            (bfzLetter w l).2 = (bfzLetter w j).2) ∨
          (bfzSuccessor w l = j ∧ (j : WithTop (Fin (r + w.length))) < bfzSuccessor w k ∧
            (bfzLetter w l).2 ≠ (bfzLetter w j).2)) :=
  Iff.rfl

/-- Inclined-edge pairs are decidable. -/
instance (w : List (Fin r × Bool)) (k l : Fin (r + w.length)) :
    Decidable (IsBfzInclinedPair w k l) :=
  decidable_of_iff _ (isBfzInclinedPair_iff w k l).symm

/-- The first position of an inclined pair precedes the second. -/
theorem IsBfzInclinedPair.lt {w : List (Fin r × Bool)} {k l : Fin (r + w.length)}
    (h : IsBfzInclinedPair w k l) : k < l :=
  ((isBfzInclinedPair_iff w k l).mp h).1

/-- The second position of an inclined pair is strictly before the first one's successor. -/
theorem IsBfzInclinedPair.lt_bfzSuccessor {w : List (Fin r × Bool)}
    {k l : Fin (r + w.length)} (h : IsBfzInclinedPair w k l) : l < bfzSuccessor w k := by
  obtain ⟨j, hj, hLeft | hRight⟩ := ((isBfzInclinedPair_iff w k l).mp h).2
  · rw [hLeft.1]
    exact WithTop.coe_lt_coe.mpr hj
  · exact (WithTop.coe_lt_coe.mpr hj).trans hRight.2.1

/-- An inclined pair cannot also be a horizontal successor pair. -/
theorem IsBfzInclinedPair.bfzSuccessor_ne {w : List (Fin r × Bool)}
    {k l : Fin (r + w.length)} (h : IsBfzInclinedPair w k l) : bfzSuccessor w k ≠ l :=
  h.lt_bfzSuccessor.ne.symm

/-- The signed contribution for an edge in increasing position order. -/
private def bfzOrderedEntry (w : List (Fin r × Bool)) (a : ℤ) (k l : Fin (r + w.length)) : ℤ :=
  (if (bfzLetter w l).2 then 1 else -1) *
    (if bfzSuccessor w k = l then 1 else if IsBfzInclinedPair w k l then a else 0)

/-- The extended BFZ exchange matrix, with rows at all positions and columns at the
exchangeable positions. Its Cartan parameter follows the transpose convention relative to the
BFZ paper. The formula makes sense for every signed word and integer colour matrix. -/
def bfzExchangeMatrix (w : List (Fin r × Bool)) (A : Matrix (Fin r) (Fin r) ℤ) :
    Matrix (Fin (r + w.length)) {l : Fin (r + w.length) // IsBfzExchangeable w l} ℤ :=
  fun k l ↦
    let a := A (bfzLetter w l).1 (bfzLetter w k).1
    if k < l.val then bfzOrderedEntry w a k l
    else if l.val < k then -bfzOrderedEntry w a l k else 0

/-- When the row precedes the column, horizontal edges use the column letter's sign. Inclined
edges multiply that sign by the transposed Cartan entry. -/
theorem bfzExchangeMatrix_apply_of_lt (w : List (Fin r × Bool)) (A : Matrix (Fin r) (Fin r) ℤ)
    (k : Fin (r + w.length)) (l : {l : Fin (r + w.length) // IsBfzExchangeable w l})
    (h : k < l.val) :
    bfzExchangeMatrix w A k l = (if (bfzLetter w l).2 then 1 else -1) *
      (if bfzSuccessor w k = l.val then 1
        else if IsBfzInclinedPair w k l then A (bfzLetter w l).1 (bfzLetter w k).1 else 0) := by
  simp only [bfzExchangeMatrix, ite_eq_left h, bfzOrderedEntry]

/-- At a row after the column, the edge rule has the reverse orientation, with the Cartan
entry still indexed by column colour then row colour. -/
theorem bfzExchangeMatrix_apply_of_gt (w : List (Fin r × Bool)) (A : Matrix (Fin r) (Fin r) ℤ)
    (k : Fin (r + w.length)) (l : {l : Fin (r + w.length) // IsBfzExchangeable w l})
    (h : l.val < k) :
    bfzExchangeMatrix w A k l = -((if (bfzLetter w k).2 then 1 else -1) *
      (if bfzSuccessor w l = k then 1
        else if IsBfzInclinedPair w l k then A (bfzLetter w l).1 (bfzLetter w k).1 else 0)) := by
  simp only [bfzExchangeMatrix, ite_eq_right h.not_gt, ite_eq_left h, bfzOrderedEntry]

/-- An inclined pair from the row to the column contributes the column letter's sign
times the Cartan entry. -/
theorem bfzExchangeMatrix_apply_of_isBfzInclinedPair (w : List (Fin r × Bool))
    (A : Matrix (Fin r) (Fin r) ℤ) (k : Fin (r + w.length))
    (l : {l : Fin (r + w.length) // IsBfzExchangeable w l}) (h : IsBfzInclinedPair w k l) :
    bfzExchangeMatrix w A k l =
      (if (bfzLetter w l).2 then 1 else -1) * A (bfzLetter w l).1 (bfzLetter w k).1 := by
  rw [bfzExchangeMatrix_apply_of_lt w A k l h.lt, ite_eq_right h.bfzSuccessor_ne, ite_eq_left h]

/-- An inclined pair from the column to the row contributes the negative of the row letter's
sign times the Cartan entry. The Cartan indices are still column then row. -/
theorem bfzExchangeMatrix_apply_of_isBfzInclinedPair_swap (w : List (Fin r × Bool))
    (A : Matrix (Fin r) (Fin r) ℤ) (k : Fin (r + w.length))
    (l : {l : Fin (r + w.length) // IsBfzExchangeable w l}) (h : IsBfzInclinedPair w l k) :
    bfzExchangeMatrix w A k l =
      -((if (bfzLetter w k).2 then 1 else -1) * A (bfzLetter w l).1 (bfzLetter w k).1) := by
  rw [bfzExchangeMatrix_apply_of_gt w A k l h.lt, ite_eq_right h.bfzSuccessor_ne, ite_eq_left h]

/-- The exchangeable row and column at the same position have zero entry. -/
@[simp]
theorem bfzExchangeMatrix_apply_self (w : List (Fin r × Bool)) (A : Matrix (Fin r) (Fin r) ℤ)
    (l : {l : Fin (r + w.length) // IsBfzExchangeable w l}) :
    bfzExchangeMatrix w A l l = 0 := by
  simp [bfzExchangeMatrix]

/-- The row at the predecessor of a mutable column gives a horizontal entry of magnitude one,
with sign given by the letter of the column. -/
@[simp]
theorem bfzExchangeMatrix_apply_of_bfzSuccessor_eq (w : List (Fin r × Bool))
    (A : Matrix (Fin r) (Fin r) ℤ) (k : Fin (r + w.length))
    (l : {l : Fin (r + w.length) // IsBfzExchangeable w l}) (h : bfzSuccessor w k = l.val) :
    bfzExchangeMatrix w A k l = if (bfzLetter w l).2 then 1 else -1 := by
  rw [bfzExchangeMatrix_apply_of_lt w A k l (lt_and_bfzLetter_fst_eq_of_bfzSuccessor_eq w h).1,
    ite_eq_left h, mul_one]

/-- A row whose successor precedes the mutable column has zero in that column. Together with
the horizontal entries, this gives the triangular pattern of the predecessor minor. -/
@[simp]
theorem bfzExchangeMatrix_apply_of_bfzSuccessor_lt (w : List (Fin r × Bool))
    (A : Matrix (Fin r) (Fin r) ℤ) (k : Fin (r + w.length))
    (l : {l : Fin (r + w.length) // IsBfzExchangeable w l}) (h : bfzSuccessor w k < l.val) :
    bfzExchangeMatrix w A k l = 0 := by
  obtain ⟨j, hj, hjl⟩ := WithTop.lt_iff_exists_coe.mp h
  have hkl := (lt_and_bfzLetter_fst_eq_of_bfzSuccessor_eq w hj).1.trans
    (WithTop.coe_lt_coe.mp hjl)
  have hInclined : ¬ IsBfzInclinedPair w k l := fun hi ↦ lt_asymm h hi.lt_bfzSuccessor
  rw [bfzExchangeMatrix_apply_of_lt w A k l hkl, ite_eq_right h.ne,
    ite_eq_right hInclined, mul_zero]

end List
