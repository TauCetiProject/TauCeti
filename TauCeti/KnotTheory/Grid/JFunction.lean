/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import TauCeti.KnotTheory.Grid.Diagram

/-!
# The grid `J`-function

This file adds the finite point-pair count used in the Maslov and Alexander gradings of grid
homology. For finite sets of grid points, `GridPoint.I s t` counts ordered pairs
`(p, q) ∈ s × t` with `p` strictly southwest of `q`, and `GridPoint.J s t` is the symmetrized
half-count.

The API is deliberately point-set level: later grading definitions apply it to grid-state and
marking point sets, and then extend it to the formal differences appearing in `M_O`, `M_X`,
and `A`.

## Main definitions

* `TauCeti.GridPoint.IsSouthWest`: the strict southwest relation on grid squares.
* `TauCeti.GridPoint.I`: the ordered southwest pair count.
* `TauCeti.GridPoint.JNum`: the numerator of the symmetrized `J`-function.
* `TauCeti.GridPoint.J`: the rational-valued symmetrized `J`-function.
* `TauCeti.GridPoint.JDiff`: the value of `J` on formal differences `s - a` and `t - b`.
* `TauCeti.GridState.J`, `TauCeti.GridDiagram.JO`, and `TauCeti.GridDiagram.JX`: specialized
  forms for grid states and markings.

## References

This supplies a prerequisite for `HeegaardFloer/README.md` in TauCetiRoadmap, Lane G.2,
"Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change
formulas across a rectangle." The definition follows Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Chapter 3.2, where `J` is the symmetrization of the northeast/southwest
point-pair count.
-/

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- A grid point is strictly southwest of another when both its column and row coordinates are
strictly smaller. This is the affine point-pair relation used in the grid `J`-function; it is
not the toroidal cyclic order used for rectangles. -/
def IsSouthWest (p q : Fin n × Fin n) : Prop :=
  p.1.val < q.1.val ∧ p.2.val < q.2.val

/-- The strict southwest relation has a decidable instance. -/
instance decidableIsSouthWest (p q : Fin n × Fin n) : Decidable (IsSouthWest p q) :=
  inferInstanceAs (Decidable (p.1.val < q.1.val ∧ p.2.val < q.2.val))

/-- The southwest relation in coordinate form. -/
@[simp, grind =]
theorem isSouthWest_iff (p q : Fin n × Fin n) :
    IsSouthWest p q ↔ p.1.val < q.1.val ∧ p.2.val < q.2.val :=
  Iff.rfl

/-- A point is not strictly southwest of itself. -/
@[simp]
theorem not_isSouthWest_self (p : Fin n × Fin n) : ¬ IsSouthWest p p := by
  intro h
  exact (lt_self_iff_false p.1.val).mp h.1

/-- A strictly southwest pair has distinct endpoints. -/
theorem ne_of_isSouthWest {p q : Fin n × Fin n} (h : IsSouthWest p q) : p ≠ q := by
  intro hpq
  subst hpq
  exact not_isSouthWest_self p h

/-- The strict southwest relation is asymmetric. -/
theorem not_isSouthWest_swap {p q : Fin n × Fin n} (h : IsSouthWest p q) :
    ¬ IsSouthWest q p := by
  intro hqp
  exact (not_lt_of_gt h.1) hqp.1

/-- The ordered count of pairs `(p, q) ∈ s × t` with `p` strictly southwest of `q`. -/
def I (s t : Finset (Fin n × Fin n)) : ℕ :=
  ((s ×ˢ t).filter fun pq : (Fin n × Fin n) × (Fin n × Fin n) =>
    IsSouthWest pq.1 pq.2).card

/-- The ordered southwest count as the cardinality of the filtered product of point sets. -/
theorem I_def (s t : Finset (Fin n × Fin n)) :
    I s t =
      ((s ×ˢ t).filter fun pq : (Fin n × Fin n) × (Fin n × Fin n) =>
        IsSouthWest pq.1 pq.2).card :=
  rfl

/-- Membership in the finite set counted by `GridPoint.I`. -/
@[simp]
theorem mem_filter_product_isSouthWest (s t : Finset (Fin n × Fin n))
  (pq : (Fin n × Fin n) × (Fin n × Fin n)) :
    pq ∈ (s ×ˢ t).filter (fun pq => IsSouthWest pq.1 pq.2) ↔
      pq.1 ∈ s ∧ pq.2 ∈ t ∧ IsSouthWest pq.1 pq.2 := by
  simp only [Finset.mem_filter, Finset.mem_product]
  tauto

/-- The ordered southwest count is zero when the left point set is empty. -/
@[simp]
theorem I_empty_left (s : Finset (Fin n × Fin n)) : I ∅ s = 0 := by
  simp [I]

/-- The ordered southwest count is zero when the right point set is empty. -/
@[simp]
theorem I_empty_right (s : Finset (Fin n × Fin n)) : I s ∅ = 0 := by
  simp [I]

/-- The ordered southwest count of singleton point sets is one exactly for a southwest pair. -/
@[simp]
theorem I_singleton_singleton (p q : Fin n × Fin n) :
    I {p} {q} = if IsSouthWest p q then 1 else 0 := by
  simp only [I, Finset.singleton_product_singleton, Finset.filter_singleton]
  by_cases h : IsSouthWest p q
  · simp only [h, if_true, Finset.card_singleton]
  · simp only [h, if_false, Finset.card_empty]

/-- No point contributes a southwest pair with itself. -/
@[simp]
theorem I_singleton_self (p : Fin n × Fin n) : I {p} {p} = 0 := by
  simp

/-- The ordered southwest count is additive in the left point set over disjoint unions. -/
theorem I_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    I (s₁ ∪ s₂) t = I s₁ t + I s₂ t := by
  dsimp [I]
  rw [Finset.union_product, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inl h))

/-- The ordered southwest count is additive in the right point set over disjoint unions. -/
theorem I_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    I s (t₁ ∪ t₂) = I s t₁ + I s t₂ := by
  dsimp [I]
  rw [Finset.product_union, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inr h))

/-- The ordered southwest count after inserting a fresh point on the left. -/
theorem I_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    I (insert p s) t = I {p} t + I s t := by
  rw [← Finset.singleton_union, I_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The ordered southwest count after inserting a fresh point on the right. -/
theorem I_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    I s (insert p t) = I s {p} + I s t := by
  rw [← Finset.singleton_union, I_union_right]
  exact Finset.disjoint_singleton_left.mpr h

/-- The numerator of the symmetrized `J`-function. Keeping the numerator as a natural number is
convenient for parity and integrality lemmas before passing to rational values. -/
def JNum (s t : Finset (Fin n × Fin n)) : ℕ :=
  I s t + I t s

/-- The numerator of `J` is the sum of the two ordered southwest counts. -/
theorem JNum_def (s t : Finset (Fin n × Fin n)) : JNum s t = I s t + I t s :=
  rfl

/-- The rational-valued symmetrized grid `J`-function. -/
def J (s t : Finset (Fin n × Fin n)) : ℚ :=
  ((JNum s t : ℕ) : ℚ) / 2

/-- The rational-valued `J`-function is half of its symmetrized numerator. -/
theorem J_def (s t : Finset (Fin n × Fin n)) : GridPoint.J s t = ((JNum s t : ℕ) : ℚ) / 2 :=
  rfl

/-- The numerator of `J` is symmetric. -/
theorem JNum_comm (s t : Finset (Fin n × Fin n)) : JNum s t = JNum t s := by
  rw [JNum, JNum, Nat.add_comm]

/-- The grid `J`-function is symmetric. -/
theorem J_comm (s t : Finset (Fin n × Fin n)) : GridPoint.J s t = GridPoint.J t s := by
  simp [GridPoint.J, JNum_comm s t]

/-- The numerator of `J` vanishes when the left point set is empty. -/
@[simp]
theorem JNum_empty_left (s : Finset (Fin n × Fin n)) : JNum ∅ s = 0 := by
  simp [JNum]

/-- The numerator of `J` vanishes when the right point set is empty. -/
@[simp]
theorem JNum_empty_right (s : Finset (Fin n × Fin n)) : JNum s ∅ = 0 := by
  simp [JNum]

/-- The numerator of `J` is additive in the left point set over disjoint unions. -/
theorem JNum_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    JNum (s₁ ∪ s₂) t = JNum s₁ t + JNum s₂ t := by
  simp only [JNum, I_union_left h, I_union_right h]
  ac_rfl

/-- The numerator of `J` is additive in the right point set over disjoint unions. -/
theorem JNum_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    JNum s (t₁ ∪ t₂) = JNum s t₁ + JNum s t₂ := by
  rw [JNum_comm s (t₁ ∪ t₂), JNum_union_left h, JNum_comm t₁ s, JNum_comm t₂ s]

/-- The numerator of `J` after inserting a fresh point on the left. -/
theorem JNum_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    JNum (insert p s) t = JNum {p} t + JNum s t := by
  rw [← Finset.singleton_union, JNum_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The numerator of `J` after inserting a fresh point on the right. -/
theorem JNum_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    JNum s (insert p t) = JNum s {p} + JNum s t := by
  rw [← Finset.singleton_union, JNum_union_right]
  exact Finset.disjoint_singleton_left.mpr h

/-- `J` vanishes when the left point set is empty. -/
@[simp]
theorem J_empty_left (s : Finset (Fin n × Fin n)) : GridPoint.J ∅ s = 0 := by
  simp [GridPoint.J]

/-- `J` vanishes when the right point set is empty. -/
@[simp]
theorem J_empty_right (s : Finset (Fin n × Fin n)) : GridPoint.J s ∅ = 0 := by
  simp [GridPoint.J]

/-- The grid `J`-function is additive in the left point set over disjoint unions. -/
theorem J_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    GridPoint.J (s₁ ∪ s₂) t = GridPoint.J s₁ t + GridPoint.J s₂ t := by
  simp only [GridPoint.J, JNum_union_left h, Nat.cast_add]
  exact add_div ((JNum s₁ t : ℕ) : ℚ) ((JNum s₂ t : ℕ) : ℚ) (2 : ℚ)

/-- The grid `J`-function is additive in the right point set over disjoint unions. -/
theorem J_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    GridPoint.J s (t₁ ∪ t₂) = GridPoint.J s t₁ + GridPoint.J s t₂ := by
  rw [J_comm s (t₁ ∪ t₂), J_union_left h, J_comm t₁ s, J_comm t₂ s]

/-- The grid `J`-function after inserting a fresh point on the left. -/
theorem J_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    GridPoint.J (insert p s) t = GridPoint.J {p} t + GridPoint.J s t := by
  rw [← Finset.singleton_union, J_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The grid `J`-function after inserting a fresh point on the right. -/
theorem J_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    GridPoint.J s (insert p t) = GridPoint.J s {p} + GridPoint.J s t := by
  rw [← Finset.singleton_union, J_union_right]
  exact Finset.disjoint_singleton_left.mpr h

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
theorem JDiff_left_sub_empty (s t b : Finset (Fin n × Fin n)) :
    JDiff s ∅ t b = GridPoint.J s t - GridPoint.J s b := by
  simp [JDiff]

/-- Pairing a formal difference with an ordinary point set is the corresponding difference of
two `J`-values. -/
@[simp]
theorem JDiff_right_sub_empty (s a t : Finset (Fin n × Fin n)) :
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

/-- The numerator of `J` on singleton point sets records whether either point is southwest of
the other. -/
@[simp]
theorem JNum_singleton_singleton (p q : Fin n × Fin n) :
    JNum {p} {q} =
      (if IsSouthWest p q then 1 else 0) + (if IsSouthWest q p then 1 else 0) := by
  simp [JNum]

/-- The `J`-function on singleton point sets is half the number of southwest comparisons
between the two points. -/
@[simp]
theorem J_singleton_singleton (p q : Fin n × Fin n) :
    GridPoint.J {p} {q} =
      (((if IsSouthWest p q then 1 else 0) +
        (if IsSouthWest q p then 1 else 0) : ℕ) : ℚ) / 2 := by
  simp [GridPoint.J]

/-- The `J`-function of two comparable singleton point sets is `1 / 2`. -/
theorem J_singleton_singleton_of_isSouthWest_or_isSouthWest {p q : Fin n × Fin n}
    (h : IsSouthWest p q ∨ IsSouthWest q p) :
    GridPoint.J {p} {q} = (1 : ℚ) / 2 := by
  rcases h with hpq | hqp
  · have hpqcoord : p.1.val < q.1.val ∧ p.2.val < q.2.val := by
      simpa using hpq
    have hqpcoord : ¬ (q.1.val < p.1.val ∧ q.2.val < p.2.val) := by
      simpa using not_isSouthWest_swap hpq
    have hqpfin : ¬ (q.1 < p.1 ∧ q.2 < p.2) := by
      intro h
      exact hqpcoord ⟨Fin.lt_def.mp h.1, Fin.lt_def.mp h.2⟩
    simp [J_singleton_singleton, hpqcoord, hqpfin]
  · have hqpcoord : q.1.val < p.1.val ∧ q.2.val < p.2.val := by
      simpa using hqp
    have hpqcoord : ¬ (p.1.val < q.1.val ∧ p.2.val < q.2.val) := by
      simpa using not_isSouthWest_swap hqp
    have hpqfin : ¬ (p.1 < q.1 ∧ p.2 < q.2) := by
      intro h
      exact hpqcoord ⟨Fin.lt_def.mp h.1, Fin.lt_def.mp h.2⟩
    simp [J_singleton_singleton, hpqfin, hqpcoord]

/-- The `J`-function of a singleton with itself is zero. -/
@[simp]
theorem J_singleton_self (p : Fin n × Fin n) : GridPoint.J {p} {p} = 0 := by
  simp [GridPoint.J]

/-- The ordered southwest count is monotone in its left point set. -/
theorem I_mono_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : s₁ ⊆ s₂) :
    I s₁ t ≤ I s₂ t := by
  dsimp [I]
  exact Finset.card_le_card fun pq hpq => by
    simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
    exact ⟨⟨h hpq.1.1, hpq.1.2⟩, hpq.2⟩

/-- The ordered southwest count is monotone in its right point set. -/
theorem I_mono_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : t₁ ⊆ t₂) :
    I s t₁ ≤ I s t₂ := by
  dsimp [I]
  exact Finset.card_le_card fun pq hpq => by
    simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
    exact ⟨⟨hpq.1.1, h hpq.1.2⟩, hpq.2⟩

/-- The numerator of `J` is monotone in its left point set. -/
theorem JNum_mono_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : s₁ ⊆ s₂) :
    JNum s₁ t ≤ JNum s₂ t :=
  Nat.add_le_add (I_mono_left h) (I_mono_right h)

/-- The numerator of `J` is monotone in its right point set. -/
theorem JNum_mono_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : t₁ ⊆ t₂) :
    JNum s t₁ ≤ JNum s t₂ := by
  rw [JNum_comm s t₁, JNum_comm s t₂]
  exact JNum_mono_left h

end GridPoint

namespace GridState

variable {n : ℕ}

/-- The grid `J`-function applied to the point sets of two grid states. -/
def J (x y : GridState n) : ℚ :=
  GridPoint.J x.pointSet y.pointSet

/-- The state-level grid `J`-function is the point-set `J`-function on state point sets. -/
@[simp]
theorem J_def (x y : GridState n) : GridState.J x y = GridPoint.J x.pointSet y.pointSet :=
  rfl

/-- The state-level grid `J`-function is symmetric. -/
theorem J_comm (x y : GridState n) : GridState.J x y = GridState.J y x :=
  GridPoint.J_comm x.pointSet y.pointSet

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The grid `J`-function against the `O`-markings of a grid diagram. -/
def JO (x : GridState n) : ℚ :=
  GridPoint.J x.pointSet G.OSet

/-- `JO` is the point-set `J`-function of a state against the `O`-markings. -/
@[simp]
theorem JO_def (x : GridState n) : GridDiagram.JO G x = GridPoint.J x.pointSet G.OSet :=
  rfl

/-- The grid `J`-function against the `X`-markings of a grid diagram. -/
def JX (x : GridState n) : ℚ :=
  GridPoint.J x.pointSet G.XSet

/-- `JX` is the point-set `J`-function of a state against the `X`-markings. -/
@[simp]
theorem JX_def (x : GridState n) : GridDiagram.JX G x = GridPoint.J x.pointSet G.XSet :=
  rfl

/-- `JO` may equivalently be read with the `O`-markings as the left input. -/
theorem JO_comm (x : GridState n) : GridDiagram.JO G x = GridPoint.J G.OSet x.pointSet := by
  rw [JO, GridPoint.J_comm]

/-- `JX` may equivalently be read with the `X`-markings as the left input. -/
theorem JX_comm (x : GridState n) : GridDiagram.JX G x = GridPoint.J G.XSet x.pointSet := by
  rw [JX, GridPoint.J_comm]

end GridDiagram

end TauCeti
