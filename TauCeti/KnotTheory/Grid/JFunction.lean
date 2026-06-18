/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.Lemmas
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

/-- The southwest relation is decidable because it is a pair of inequalities of natural
coordinates. -/
instance decidableIsSouthWest (p q : Fin n × Fin n) : Decidable (IsSouthWest p q) :=
  inferInstanceAs (Decidable (p.1.val < q.1.val ∧ p.2.val < q.2.val))

/-- The southwest relation in coordinate form. -/
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
  by_cases h : IsSouthWest p q
  · rw [if_pos h]
    have hfilter :
        ({(p, q)} : Finset ((Fin n × Fin n) × (Fin n × Fin n))).filter
            (fun pq => IsSouthWest pq.1 pq.2) = {(p, q)} := by
      apply Finset.filter_eq_self.mpr
      intro pq hpq
      rw [Finset.mem_singleton] at hpq
      subst pq
      exact h
    simp [I, hfilter]
  · simp [I, h]

/-- No point contributes a southwest pair with itself. -/
@[simp]
theorem I_singleton_self (p : Fin n × Fin n) : I {p} {p} = 0 := by
  simp

/-- The numerator of the symmetrized `J`-function. Keeping the numerator as a natural number is
convenient for parity and integrality lemmas before passing to rational values. -/
def JNum (s t : Finset (Fin n × Fin n)) : ℕ :=
  I s t + I t s

/-- The rational-valued symmetrized grid `J`-function. -/
def J (s t : Finset (Fin n × Fin n)) : ℚ :=
  ((JNum s t : ℕ) : ℚ) / 2

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

/-- `J` vanishes when the left point set is empty. -/
@[simp]
theorem J_empty_left (s : Finset (Fin n × Fin n)) : GridPoint.J ∅ s = 0 := by
  simp [GridPoint.J]

/-- `J` vanishes when the right point set is empty. -/
@[simp]
theorem J_empty_right (s : Finset (Fin n × Fin n)) : GridPoint.J s ∅ = 0 := by
  simp [GridPoint.J]

/-- The numerator of `J` on singleton point sets records whether either point is southwest of
the other. -/
@[simp]
theorem JNum_singleton_singleton (p q : Fin n × Fin n) :
    JNum {p} {q} =
      (if IsSouthWest p q then 1 else 0) + (if IsSouthWest q p then 1 else 0) := by
  simp [JNum]

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

/-- The state-level grid `J`-function is symmetric. -/
theorem J_comm (x y : GridState n) : GridState.J x y = GridState.J y x :=
  GridPoint.J_comm x.pointSet y.pointSet

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The grid `J`-function against the `O`-markings of a grid diagram. -/
def JO (x : GridState n) : ℚ :=
  GridPoint.J x.pointSet G.OSet

/-- The grid `J`-function against the `X`-markings of a grid diagram. -/
def JX (x : GridState n) : ℚ :=
  GridPoint.J x.pointSet G.XSet

/-- `JO` may equivalently be read with the `O`-markings as the left input. -/
theorem JO_comm (x : GridState n) : GridDiagram.JO G x = GridPoint.J G.OSet x.pointSet := by
  rw [JO, GridPoint.J_comm]

/-- `JX` may equivalently be read with the `X`-markings as the left input. -/
theorem JX_comm (x : GridState n) : GridDiagram.JX G x = GridPoint.J G.XSet x.pointSet := by
  rw [JX, GridPoint.J_comm]

end GridDiagram

end TauCeti
