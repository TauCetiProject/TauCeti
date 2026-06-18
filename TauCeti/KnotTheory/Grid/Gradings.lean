/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import TauCeti.KnotTheory.Grid.JFunction

/-!
# Maslov and Alexander gradings for grid states

This file records the rational-valued grading formulas for the grid-combinatorial lane of the
Heegaard Floer roadmap. The point-set `J`-function was developed separately; here we add its
bilinear extension to formal differences of point sets and use it to define the `O`- and
`X`-Maslov gradings and the Alexander grading of a grid state.

The definitions are intentionally formula-level. The later integer-valuedness and
rectangle-change theorems can refer to these names without unfolding the point-pair count.

## Main definitions

* `TauCeti.GridPoint.JDiff`: the value of `J` on formal differences `s - a` and `t - b`.
* `TauCeti.GridDiagram.maslovO`, `TauCeti.GridDiagram.maslovX`: the two Maslov grading
  formulas attached to the `O` and `X` markings.
* `TauCeti.GridDiagram.alexander`: the Alexander grading formula.

## References

This supplies the grading-definition part of `TauCetiRoadmap/HeegaardFloer/README.md`,
Lane G.2, "Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`;
grading-change formulas across a rectangle." The formulas follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.2:
`M_O(x) = J(x - O, x - O) + 1`, `M_X(x) = J(x - X, x - X) + 1`, and
`A(x) = (M_O(x) - M_X(x)) / 2 - (n - 1) / 2`.
-/

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- The bilinear extension of the grid `J`-function to formal differences of point sets.

`JDiff s a t b` means `J(s - a, t - b)`, expanded as
`J s t - J s b - J a t + J a b`. -/
def JDiff (s a t b : Finset (Fin n × Fin n)) : ℚ :=
  GridPoint.J s t - GridPoint.J s b - GridPoint.J a t + GridPoint.J a b

/-- The definition of `JDiff` as the expanded four-term formula. -/
theorem JDiff_def (s a t b : Finset (Fin n × Fin n)) :
    JDiff s a t b =
      GridPoint.J s t - GridPoint.J s b - GridPoint.J a t + GridPoint.J a b :=
  rfl

/-- `JDiff` is symmetric in its two formal-difference inputs. -/
theorem JDiff_comm (s a t b : Finset (Fin n × Fin n)) :
    JDiff s a t b = JDiff t b s a := by
  rw [JDiff, JDiff, GridPoint.J_comm t s, GridPoint.J_comm t a,
    GridPoint.J_comm b s, GridPoint.J_comm b a]
  ring

/-- The formal difference of a point set with itself has zero `J`-pairing on the left. -/
@[simp]
theorem JDiff_self_left (s t b : Finset (Fin n × Fin n)) : JDiff s s t b = 0 := by
  simp [JDiff]

/-- The formal difference of a point set with itself has zero `J`-pairing on the right. -/
@[simp]
theorem JDiff_self_right (s a t : Finset (Fin n × Fin n)) : JDiff s a t t = 0 := by
  rw [JDiff_comm, JDiff_self_left]

/-- Pairing an ordinary point set with a formal difference is the corresponding difference of
two `J`-values. -/
@[simp]
theorem JDiff_empty_left (s t b : Finset (Fin n × Fin n)) :
    JDiff s ∅ t b = GridPoint.J s t - GridPoint.J s b := by
  simp [JDiff]

/-- Pairing a formal difference with an ordinary point set is the corresponding difference of
two `J`-values. -/
@[simp]
theorem JDiff_empty_right (s a t : Finset (Fin n × Fin n)) :
    JDiff s a t ∅ = GridPoint.J s t - GridPoint.J a t := by
  simp [JDiff]

/-- The self-pairing of `s - a` expanded in symmetric form. -/
theorem JDiff_self_eq (s a : Finset (Fin n × Fin n)) :
    JDiff s a s a = GridPoint.J s s - 2 * GridPoint.J s a + GridPoint.J a a := by
  rw [JDiff, GridPoint.J_comm a s]
  ring

/-- `JDiff` is additive in the left positive point set over disjoint unions. -/
theorem JDiff_union_left {s₁ s₂ a t b : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    JDiff (s₁ ∪ s₂) a t b =
      JDiff s₁ a t b + JDiff s₂ ∅ t b := by
  rw [JDiff, JDiff, JDiff, GridPoint.J_union_left h, GridPoint.J_union_left h]
  simp
  ring

/-- `JDiff` is additive in the right positive point set over disjoint unions. -/
theorem JDiff_union_right {s a t₁ t₂ b : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    JDiff s a (t₁ ∪ t₂) b =
      JDiff s a t₁ b + JDiff s a t₂ ∅ := by
  rw [JDiff_comm s a (t₁ ∪ t₂) b, JDiff_union_left h,
    JDiff_comm t₁ b s a, JDiff_comm t₂ ∅ s a]

end GridPoint

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The `J`-function self-pairing of the `O` markings. -/
def JOO : ℚ :=
  GridPoint.J G.OSet G.OSet

/-- `JOO` is the point-set `J`-function of the `O` markings with themselves. -/
@[simp]
theorem JOO_def : G.JOO = GridPoint.J G.OSet G.OSet :=
  rfl

/-- The `J`-function self-pairing of the `X` markings. -/
def JXX : ℚ :=
  GridPoint.J G.XSet G.XSet

/-- `JXX` is the point-set `J`-function of the `X` markings with themselves. -/
@[simp]
theorem JXX_def : G.JXX = GridPoint.J G.XSet G.XSet :=
  rfl

/-- The `O`-Maslov grading of a grid state.

This is the formula `M_O(x) = J(x - O, x - O) + 1`. -/
def maslovO (x : GridState n) : ℚ :=
  GridPoint.JDiff x.pointSet G.OSet x.pointSet G.OSet + 1

/-- The `O`-Maslov grading as a `JDiff` self-pairing plus one. -/
theorem maslovO_def (x : GridState n) :
    G.maslovO x = GridPoint.JDiff x.pointSet G.OSet x.pointSet G.OSet + 1 :=
  rfl

/-- The expanded `O`-Maslov grading formula. -/
theorem maslovO_eq (x : GridState n) :
    G.maslovO x = GridState.J x x - 2 * G.JO x + G.JOO + 1 := by
  rw [maslovO, GridPoint.JDiff_self_eq, GridState.J_def, JO_def, JOO_def]

/-- The `X`-Maslov grading of a grid state.

This is the formula `M_X(x) = J(x - X, x - X) + 1`. -/
def maslovX (x : GridState n) : ℚ :=
  GridPoint.JDiff x.pointSet G.XSet x.pointSet G.XSet + 1

/-- The `X`-Maslov grading as a `JDiff` self-pairing plus one. -/
theorem maslovX_def (x : GridState n) :
    G.maslovX x = GridPoint.JDiff x.pointSet G.XSet x.pointSet G.XSet + 1 :=
  rfl

/-- The expanded `X`-Maslov grading formula. -/
theorem maslovX_eq (x : GridState n) :
    G.maslovX x = GridState.J x x - 2 * G.JX x + G.JXX + 1 := by
  rw [maslovX, GridPoint.JDiff_self_eq, GridState.J_def, JX_def, JXX_def]

/-- The Alexander grading of a grid state.

This is the formula `A(x) = (M_O(x) - M_X(x)) / 2 - (n - 1) / 2`. The shift is cast
through `ℤ`, so the formula remains literal at `n = 0`; integer-valuedness is a later grading
theorem. -/
def alexander (x : GridState n) : ℚ :=
  (G.maslovO x - G.maslovX x) / 2 - (((n : ℤ) - 1 : ℤ) : ℚ) / 2

/-- The Alexander grading as the difference of the two Maslov gradings with the standard
normalization shift. -/
theorem alexander_def (x : GridState n) :
    G.alexander x =
      (G.maslovO x - G.maslovX x) / 2 - (((n : ℤ) - 1 : ℤ) : ℚ) / 2 :=
  rfl

/-- The Alexander grading with the two Maslov formulas expanded. -/
theorem alexander_eq (x : GridState n) :
    G.alexander x =
      (2 * (G.JX x - G.JO x) + (G.JOO - G.JXX) - (((n : ℤ) - 1 : ℤ) : ℚ)) / 2 := by
  rw [alexander, maslovO_eq, maslovX_eq]
  ring

/-- The difference of the two Maslov gradings is twice the Alexander grading plus the
normalization shift. -/
theorem maslovO_sub_maslovX_eq (x : GridState n) :
    G.maslovO x - G.maslovX x =
      2 * G.alexander x + (((n : ℤ) - 1 : ℤ) : ℚ) := by
  rw [alexander]
  ring

/-- Replacing the two Maslov gradings by the same value leaves only the normalization shift in
the Alexander formula. -/
theorem alexander_eq_neg_shift_of_maslov_eq {x : GridState n} (h : G.maslovO x = G.maslovX x) :
    G.alexander x = -(((n : ℤ) - 1 : ℤ) : ℚ) / 2 := by
  rw [alexander, h]
  ring

end GridDiagram

end TauCeti
