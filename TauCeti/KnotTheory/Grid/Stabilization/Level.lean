/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
public import TauCeti.KnotTheory.Grid.Stabilization.Basic

/-!
# A filtration level for the `X`-stabilization

Let `G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization of a grid diagram `G`
splitting the `X`-marking of column `s`, with new `O`-marking `O_new = (κ, ρ)` for
`κ = s.castSucc` and `ρ = (G.X s).castSucc`. Call the squares off the row `ρ` and off the column
`κ` the *outer squares* of the stabilization. This file attaches to every grid state `y` of `G'`
a rational *level* that measures, across any rectangle carrying no `O`-marking, the number of
outer squares the rectangle covers: the level of the source minus the level of the target is
that number (`GridDiagram.stabilizeXLevel_sub_stabilizeXLevel`).

The level is the pairing (`GridState.JWeight`) of `y` against the integer weight on squares that
is `1` on the outer squares, is lowered by `n` on the `O`-markings of `G'` and raised by `n` on
`O_new`. Every row and every column of that weight sums to zero, because each row and column of
`G'` carries exactly one `O`-marking and the outer squares fill `n` squares of every row but `ρ`
and every column but `κ`. So `GridRectangleBetween.JWeight_sub_JWeight_eq_sum` computes the change
of the level across a rectangle as the covered weight, which on rectangles avoiding the
`O`-markings is the number of covered outer squares.

A rectangle covering no outer square lies in the cross formed by row `ρ` and column `κ`, so it
is a single row or a single column of squares
(`GridDiagram.coveredRows_eq_or_coveredColumns_eq_of_disjoint_stabilizeXOuterSquares`).

## Main definitions

* `TauCeti.GridDiagram.stabilizeXOuterSquares`: the squares off the row and the column of `O_new`.
* `TauCeti.GridDiagram.stabilizeXWeight`: the balanced weight on squares.
* `TauCeti.GridDiagram.stabilizeXLevel`: the level of a grid state of the stabilization.

## Main results

* `TauCeti.GridDiagram.stabilizeXLevel_sub_stabilizeXLevel`: across a rectangle avoiding the
  `O`-markings the level drops by the number of covered outer squares.
* `TauCeti.GridDiagram.stabilizeXLevel_lt_or_disjoint`: across such a rectangle the level strictly
  drops unless the rectangle covers no outer square.
* `TauCeti.GridDiagram.coveredRows_eq_or_coveredColumns_eq_of_disjoint_stabilizeXOuterSquares`:
  a rectangle covering no outer square covers the single row `ρ` or the single column `κ`.

## References

This is the filtration of Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer
homology*, Geom. Topol. 11 (2007), Section 3.2 (the `Q`-filtration in the proof of stabilization
invariance), and of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2,
specialised to the fully blocked comparison of `TauCeti.KnotTheory.Grid.Stabilization.Reduction`.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The outer squares of the stabilization splitting the `X`-marking of column `s`: the squares
off the row and off the column of its new `O`-marking `(s.castSucc, (G.X s).castSucc)`. -/
def stabilizeXOuterSquares : Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.filter fun q => q.1 ≠ s.castSucc ∧ q.2 ≠ (G.X s).castSucc

@[simp]
theorem mem_stabilizeXOuterSquares (q : Fin (n + 1) × Fin (n + 1)) :
    q ∈ G.stabilizeXOuterSquares s ↔ q.1 ≠ s.castSucc ∧ q.2 ≠ (G.X s).castSucc := by
  simp [stabilizeXOuterSquares]

/-- The balanced weight on the squares of the stabilization: `1` on the outer squares, lowered by
`n` on the `O`-markings of the stabilization and raised by `n` on its new `O`-marking. -/
def stabilizeXWeight (q : Fin (n + 1) × Fin (n + 1)) : ℤ :=
  (if q ∈ G.stabilizeXOuterSquares s then 1 else 0) -
    n * (if q ∈ (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet then 1 else 0) +
    n * (if q = (s.castSucc, (G.X s).castSucc) then 1 else 0)

/-- The balanced weight as its three contributions on each square. -/
theorem stabilizeXWeight_def (q : Fin (n + 1) × Fin (n + 1)) :
    G.stabilizeXWeight s q =
      (if q ∈ G.stabilizeXOuterSquares s then 1 else 0) -
        n * (if q ∈ (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet then 1 else 0) +
        n * (if q = (s.castSucc, (G.X s).castSucc) then 1 else 0) :=
  (rfl)

/-- Every column of the balanced weight sums to zero. -/
theorem sum_stabilizeXWeight_column (c : Fin (n + 1)) :
    ∑ r, G.stabilizeXWeight s (c, r) = 0 := by
  simp only [stabilizeXWeight_def, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    mem_stabilizeXOuterSquares, mem_OSet, stabilizeX_O, Prod.mk.injEq]
  by_cases hc : c = s.castSucc
  · subst hc
    simp
  · simp [hc, Finset.sum_ite, Finset.filter_ne']

/-- Every row of the balanced weight sums to zero. -/
theorem sum_stabilizeXWeight_row (r : Fin (n + 1)) :
    ∑ c, G.stabilizeXWeight s (c, r) = 0 := by
  simp only [stabilizeXWeight_def, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    mem_stabilizeXOuterSquares, mem_OSet, stabilizeX_O, Prod.mk.injEq, ← Equiv.eq_symm_apply,
    Finset.sum_ite_eq']
  by_cases hr : r = (G.X s).castSucc
  · subst hr
    simp
  · simp [hr, Finset.sum_ite, Finset.filter_ne']

/-- The level of a grid state of the stabilization: its pairing against the balanced weight. -/
noncomputable def stabilizeXLevel (y : GridState (n + 1)) : ℚ :=
  y.JWeight (G.stabilizeXWeight s)

/-- The stabilization level is the weighted pairing of the state. -/
theorem stabilizeXLevel_def (y : GridState (n + 1)) :
    G.stabilizeXLevel s y = y.JWeight (G.stabilizeXWeight s) :=
  (rfl)

/-- **The level counts outer squares.** Across a rectangle of the stabilization covering no
`O`-marking, the level of the source minus the level of the target is the number of outer squares
the rectangle covers. -/
theorem stabilizeXLevel_sub_stabilizeXLevel {y z : GridState (n + 1)}
    (R : GridRectangleBetween y z)
    (hO : Disjoint R.toGridRectangle.coveredSquares
      (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet) :
    G.stabilizeXLevel s y - G.stabilizeXLevel s z =
      ((R.toGridRectangle.coveredSquares ∩ G.stabilizeXOuterSquares s).card : ℚ) := by
  have hmem : (s.castSucc, (G.X s).castSucc) ∈
      (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet := by
    simp
  rw [stabilizeXLevel_def, stabilizeXLevel_def, R.JWeight_sub_JWeight_eq_sum
    (G.sum_stabilizeXWeight_column s) (G.sum_stabilizeXWeight_row s),
    ← Finset.filter_mem_eq_inter, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  have hqO : q ∉ (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet :=
    Finset.disjoint_left.1 hO hq
  have hne : q ≠ (s.castSucc, (G.X s).castSucc) := fun h ↦ hqO (h ▸ hmem)
  rw [stabilizeXWeight_def, ite_eq_right hqO, ite_eq_right hne]
  split_ifs <;> simp

/-- **The level drops across rectangles covering outer squares.** Across a rectangle of the
stabilization covering no `O`-marking, the level strictly drops, unless the rectangle covers no
outer square. -/
theorem stabilizeXLevel_lt_or_disjoint {y z : GridState (n + 1)} (R : GridRectangleBetween y z)
    (hO : Disjoint R.toGridRectangle.coveredSquares
      (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet) :
    G.stabilizeXLevel s z < G.stabilizeXLevel s y ∨
      Disjoint R.toGridRectangle.coveredSquares (G.stabilizeXOuterSquares s) := by
  rcases (R.toGridRectangle.coveredSquares ∩ G.stabilizeXOuterSquares s).eq_empty_or_nonempty
    with h | h
  · exact Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr h)
  · left
    rw [← sub_pos, G.stabilizeXLevel_sub_stabilizeXLevel s R hO]
    exact Nat.cast_pos.mpr h.card_pos

/-- Across a rectangle all of whose covered squares lie in the row or the column of the new
`O`-marking, the level does not change: the balanced weight vanishes on that cross. -/
theorem stabilizeXLevel_eq_of_disjoint {y z : GridState (n + 1)} (R : GridRectangleBetween y z)
    (h : Disjoint R.toGridRectangle.coveredSquares (G.stabilizeXOuterSquares s)) :
    G.stabilizeXLevel s y = G.stabilizeXLevel s z := by
  rw [← sub_eq_zero, stabilizeXLevel_def, stabilizeXLevel_def, R.JWeight_sub_JWeight_eq_sum
    (G.sum_stabilizeXWeight_column s) (G.sum_stabilizeXWeight_row s)]
  refine Finset.sum_eq_zero fun q hq ↦ ?_
  have hout : q ∉ G.stabilizeXOuterSquares s := Finset.disjoint_left.1 h hq
  have key : q ∈ (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet ↔
      q = (s.castSucc, (G.X s).castSucc) := by
    obtain ⟨c, r⟩ := q
    rw [mem_stabilizeXOuterSquares, not_and_or, not_ne_iff, not_ne_iff] at hout
    rw [mk_mem_OSet, Prod.mk.injEq]
    by_cases hc : c = s.castSucc
    · subst hc
      simp only [true_and, stabilizeX_O, GridState.insertPoint_apply_newColumn]
      exact eq_comm
    · obtain rfl : r = (G.X s).castSucc := hout.resolve_left hc
      simp only [stabilizeX_O, G.stabilizeX_O_eq_castSucc_iff s c, hc, false_and]
  rw [stabilizeXWeight_def, ite_eq_right hout]
  by_cases hq' : q = (s.castSucc, (G.X s).castSucc)
  · rw [ite_eq_left (key.2 hq'), ite_eq_left hq']
    simp
  · rw [ite_eq_right (mt key.1 hq'), ite_eq_right hq']
    simp

/-- **Rectangles covering no outer square.** A rectangle of the stabilization that covers no
outer square covers only the row `(G.X s).castSucc` of the new `O`-marking, or only its column
`s.castSucc`. -/
theorem coveredRows_eq_or_coveredColumns_eq_of_disjoint_stabilizeXOuterSquares
    {y z : GridState (n + 1)} (R : GridRectangleBetween y z)
    (h : Disjoint R.toGridRectangle.coveredSquares (G.stabilizeXOuterSquares s)) :
    R.toGridRectangle.coveredRows = {(G.X s).castSucc} ∨
      R.toGridRectangle.coveredColumns = {s.castSucc} := by
  have hcols : R.toGridRectangle.coveredColumns.Nonempty :=
    ⟨R.left, (GridRectangle.mem_coveredColumns _ _).mpr (Grid.left_mem_cIco R.left_ne_right)⟩
  have hrows : R.toGridRectangle.coveredRows.Nonempty :=
    ⟨R.bottom, (GridRectangle.mem_coveredRows _ _).mpr (Grid.left_mem_cIco R.bottom_ne_top)⟩
  by_cases hr : R.toGridRectangle.coveredRows = {(G.X s).castSucc}
  · exact Or.inl hr
  right
  obtain ⟨r₀, hr₀, hne⟩ : ∃ r₀ ∈ R.toGridRectangle.coveredRows, r₀ ≠ (G.X s).castSucc := by
    by_contra! hall
    exact hr (hrows.subset_singleton_iff.1 fun r hr' ↦ Finset.mem_singleton.2 (hall r hr'))
  refine hcols.subset_singleton_iff.1 fun c hc ↦ Finset.mem_singleton.2 ?_
  by_contra hcκ
  exact Finset.disjoint_left.1 h (GridRectangle.mem_coveredSquares _ (c, r₀) |>.2 ⟨hc, hr₀⟩)
    ((G.mem_stabilizeXOuterSquares s (c, r₀)).2 ⟨hcκ, hne⟩)

end GridDiagram

end TauCeti
