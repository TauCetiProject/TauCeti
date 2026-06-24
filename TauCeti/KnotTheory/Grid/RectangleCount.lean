/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Complex
public import TauCeti.KnotTheory.Grid.RectangleSwap

/-!
# Exactly two oriented rectangles connect grid states that differ by a column transposition

An oriented rectangle `R : GridRectangleBetween x y` is determined by its two side columns
`R.left`, `R.right`: away from those columns the two states agree, and at those columns they
exchange rows (`RectangleSwap.lean`). This file pins down how many such rectangles there are
between two fixed grid states.

The key observation is purely about the side columns. A column `c` is a side column of `R`
exactly when the two states differ there: if `c` is neither `R.left` nor `R.right` then
`y c = x c`, and at a side column the states genuinely disagree because the source permutation
is injective. So the *unordered* pair of side columns is forced — it is the set of columns where
`x` and `y` differ — and a rectangle between `x` and `y` is determined up to the *order* of its
two side columns. Reversing the two side columns gives the other oriented rectangle
(`swapSides`), so there are exactly two oriented rectangles when the states differ by a
transposition and none otherwise.

This is the finiteness backbone of the grid differential: the coefficient of `y` in the fully
blocked differential of `x` counts a sub-collection of these at-most-two rectangles, so the
differential of a generator is supported on the column-transposition neighbours of that
generator.

## Main definitions

* `TauCeti.GridRectangleBetween.swapSides`: the oriented rectangle from `x` to `y` with its two
  side columns exchanged.

## Main results

* `TauCeti.GridRectangleBetween.apply_ne_iff`: a column is a side column exactly when the two
  states differ there.
* `TauCeti.GridRectangleBetween.eq_or_eq_swapSides`: any two oriented rectangles between the same
  states are equal or differ by `swapSides`.
* `TauCeti.GridRectangleBetween.all_eq_pair`, `TauCeti.GridRectangleBetween.card_all_le_two`,
  `TauCeti.GridRectangleBetween.card_all_of_nonempty`: there are at most two oriented rectangles
  between two states, and exactly two when there is at least one.
* `TauCeti.GridRectangleBetween.nonempty_all_iff`: oriented rectangles between `x` and `y` exist
  exactly when `y` is a column transposition of `x`.
* `TauCeti.GridDiagram.card_fullyBlockedRectangles_le_two`: the fully blocked differential has at
  most two rectangles in each matrix coefficient.
* `TauCeti.GridDiagram.exists_swapColumns_of_fullyBlockedDifferentialOnGenerator_ne_zero`: the
  fully blocked differential of a generator is supported on its column transpositions.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3,
"The complexes and `∂² = 0`": the count of rectangles between two states is the finiteness fact
underlying the differential. The statement that exactly two rectangles connect two states
differing by a transposition follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 4.
-/

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- An oriented rectangle between two grid states has decidable equality: it is determined by its
ordered pair of side columns, which has decidable equality. -/
instance : DecidableEq (GridRectangleBetween x y) :=
  sidePair_injective.decidableEq

variable (R : GridRectangleBetween x y)

/-- A column is a side column of the rectangle exactly when the two states read different rows
there. Away from the two side columns the states agree, and at a side column the source
permutation is injective on the two distinct side columns, so the read rows differ. -/
theorem apply_ne_iff (c : Fin n) : y c ≠ x c ↔ c = R.left ∨ c = R.right := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    exact h (R.map_of_ne c hc.1 hc.2)
  · rintro (rfl | rfl)
    · rw [R.map_left]
      exact fun h => R.left_ne_right (x.toPerm.injective h).symm
    · rw [R.map_right]
      exact fun h => R.left_ne_right (x.toPerm.injective h)

/-- The states differ at the initial side column. -/
theorem left_apply_ne : y R.left ≠ x R.left :=
  (R.apply_ne_iff R.left).mpr (Or.inl rfl)

/-- The states differ at the terminal side column. -/
theorem right_apply_ne : y R.right ≠ x R.right :=
  (R.apply_ne_iff R.right).mpr (Or.inr rfl)

/-- The oriented rectangle from `x` to `y` obtained by exchanging the two side columns.

It connects the same two states `x` and `y` -- the two states still exchange rows at the two
side columns and agree elsewhere -- but traverses the complementary toroidal region. This is the
second of the two oriented rectangles between states related by a transposition; it is not the
opposite rectangle `symm`, which runs from `y` back to `x`. -/
@[expose] def swapSides (R : GridRectangleBetween x y) : GridRectangleBetween x y where
  left := R.right
  right := R.left
  left_ne_right := R.left_ne_right.symm
  map_left := R.map_right
  map_right := R.map_left
  map_of_ne c hl hr := R.map_of_ne c hr hl

/-- The side-swapped rectangle's initial side column is the original terminal side column. -/
@[simp]
theorem swapSides_left : R.swapSides.left = R.right :=
  rfl

/-- The side-swapped rectangle's terminal side column is the original initial side column. -/
@[simp]
theorem swapSides_right : R.swapSides.right = R.left :=
  rfl

/-- Exchanging the two side columns twice gives the original rectangle. -/
@[simp]
theorem swapSides_swapSides : R.swapSides.swapSides = R := by
  cases R
  rfl

/-- Exchanging the two side columns gives a genuinely different rectangle, since the two side
columns are distinct. -/
theorem swapSides_ne_self : R.swapSides ≠ R := by
  intro h
  have hleft : R.swapSides.left = R.left := congrArg GridRectangleBetween.left h
  rw [swapSides_left] at hleft
  exact R.left_ne_right hleft.symm

/-- Any oriented rectangle between the same two states is `R` or its side swap `R.swapSides`. Its
two side columns are exactly the two columns where `x` and `y` differ, which are `R.left` and
`R.right`, so its ordered side pair is one of the two orderings of that pair. -/
theorem eq_or_eq_swapSides (S : GridRectangleBetween x y) : S = R ∨ S = R.swapSides := by
  have hSl := (R.apply_ne_iff S.left).mp S.left_apply_ne
  have hSr := (R.apply_ne_iff S.right).mp S.right_apply_ne
  rcases hSl with hSl | hSl
  · refine Or.inl (eq_of_sides hSl ?_)
    rcases hSr with hSr | hSr
    · exact absurd (hSl.trans hSr.symm) S.left_ne_right
    · exact hSr
  · refine Or.inr (eq_of_sides ?_ ?_)
    · rw [swapSides_left]; exact hSl
    · rcases hSr with hSr | hSr
      · rw [swapSides_right]; exact hSr
      · exact absurd (hSl.trans hSr.symm) S.left_ne_right

/-- The oriented rectangles between two states are contained in the pair `{R, R.swapSides}`. -/
theorem all_subset_pair : all x y ⊆ {R, R.swapSides} := by
  intro S _
  rcases R.eq_or_eq_swapSides S with h | h <;> simp [h]

/-- Given one oriented rectangle between two states, the oriented rectangles between them are
exactly the pair `{R, R.swapSides}`. -/
theorem all_eq_pair : all x y = {R, R.swapSides} := by
  refine Finset.Subset.antisymm R.all_subset_pair ?_
  intro S hS
  rcases Finset.mem_insert.mp hS with h | h
  · exact h ▸ mem_all R
  · exact (Finset.mem_singleton.mp h) ▸ mem_all R.swapSides

/-- There are at most two oriented rectangles between two grid states. -/
theorem card_all_le_two (x y : GridState n) : (all x y).card ≤ 2 := by
  rcases (all x y).eq_empty_or_nonempty with h | h
  · rw [h]; simp
  · obtain ⟨R, -⟩ := h
    calc (all x y).card
        ≤ ({R, R.swapSides} : Finset (GridRectangleBetween x y)).card :=
          Finset.card_le_card R.all_subset_pair
      _ = 2 := Finset.card_pair R.swapSides_ne_self.symm

/-- When there is at least one oriented rectangle between two states, there are exactly two: the
chosen one and its side swap. -/
theorem card_all_of_nonempty (h : (all x y).Nonempty) : (all x y).card = 2 := by
  obtain ⟨R, -⟩ := h
  rw [R.all_eq_pair, Finset.card_pair R.swapSides_ne_self.symm]

/-- Oriented rectangles between `x` and `y` exist exactly when `y` is a column transposition of
`x`. A rectangle realizes its side columns as a transposition taking `x` to `y`, and conversely a
column transposition exhibits an oriented rectangle on those two columns. -/
theorem nonempty_all_iff :
    (all x y).Nonempty ↔ ∃ a b : Fin n, a ≠ b ∧ y = x.swapColumns a b := by
  constructor
  · rintro ⟨R, -⟩
    exact ⟨R.left, R.right, R.left_ne_right, R.target_eq_swapColumns⟩
  · rintro ⟨a, b, hab, hy⟩
    refine ⟨⟨a, b, hab, ?_, ?_, ?_⟩, mem_all _⟩
    · rw [hy, GridState.swapColumns_apply, Equiv.swap_apply_left]
    · rw [hy, GridState.swapColumns_apply, Equiv.swap_apply_right]
    · intro c hl hr
      rw [hy, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hl hr]

/-- There are at most two empty oriented rectangles between two grid states. -/
theorem card_emptyRectangles_le_two (x y : GridState n) :
    (emptyRectangles x y).card ≤ 2 :=
  (Finset.card_le_card (emptyRectangles_subset_all x y)).trans (card_all_le_two x y)

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- There are at most two fully blocked rectangles in each matrix coefficient of the fully
blocked differential. -/
theorem card_fullyBlockedRectangles_le_two (x y : GridState n) :
    (G.fullyBlockedRectangles x y).card ≤ 2 :=
  (Finset.card_le_card (G.fullyBlockedRectangles_subset_all x y)).trans
    (GridRectangleBetween.card_all_le_two x y)

/-- A nonzero matrix coefficient of the fully blocked differential forces the target state to be a
column transposition of the source state: a nonzero count means there is a fully blocked
rectangle, hence an oriented rectangle, between the two states. -/
theorem exists_swapColumns_of_fullyBlockedRectangleCount_ne_zero {x y : GridState n}
    (h : G.fullyBlockedRectangleCount x y ≠ 0) :
    ∃ a b : Fin n, a ≠ b ∧ y = x.swapColumns a b := by
  rw [fullyBlockedRectangleCount_def] at h
  have hcard : (G.fullyBlockedRectangles x y).card ≠ 0 := by
    intro hc
    rw [hc] at h
    simp at h
  obtain ⟨R, hR⟩ := Finset.card_ne_zero.mp hcard
  exact ⟨R.left, R.right, R.left_ne_right, R.target_eq_swapColumns⟩

/-- The fully blocked differential of a generator is supported on the column transpositions of
that generator: if the `y`-coefficient is nonzero, then `y` is a column transposition of `x`. -/
theorem exists_swapColumns_of_fullyBlockedDifferentialOnGenerator_ne_zero {x y : GridState n}
    (h : G.fullyBlockedDifferentialOnGenerator x y ≠ 0) :
    ∃ a b : Fin n, a ≠ b ∧ y = x.swapColumns a b := by
  rw [fullyBlockedDifferentialOnGenerator_apply] at h
  exact G.exists_swapColumns_of_fullyBlockedRectangleCount_ne_zero h

end GridDiagram

end TauCeti
