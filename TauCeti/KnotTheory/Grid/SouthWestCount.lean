/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Prod
import TauCeti.KnotTheory.Grid.GradingInteger

/-!
# A column-index formula for the grid southwest count

The grid `J`-function and the Maslov gradings it feeds are defined through the ordered southwest
count `GridPoint.I s t`, which ranges over all pairs of points `(p, q) ∈ s × t` and keeps those
with `p` strictly southwest of `q`. For the point sets that actually occur -- the graphs of the
permutations underlying grid states and the `O`/`X` markings -- this point-pair count collapses
to a count over *column indices*: a pair of points is southwest-comparable exactly when their
columns and their occupied rows are simultaneously ordered.

This file proves that collapse and draws the consequences a computation rests on. For grid states
`x` and `y`,
`I(x, y) = #{(c, d) : c < d ∧ x c < y d}`,
and feeding this into the integer Maslov gradings rewrites them entirely as counts over column
indices, so they evaluate on an explicit grid without unfolding any point-pair product. The
self-count specializes to the number of non-inversions of a state's permutation, and pairing it
with the inversion count recovers the total number of ordered column pairs.

## Main results

* `TauCeti.GridState.I_pointSet_eq`: the ordered southwest count of two state point sets is the
  number of column pairs `c < d` with `x c < y d`.
* `TauCeti.GridState.JNum_pointSet_eq`, `TauCeti.GridState.J_pointSet_eq`: the symmetrized
  numerator and the rational `J`-function as column-index counts.
* `TauCeti.GridState.I_self_pointSet_eq`: the self southwest count is the number of
  non-inversions of the state's permutation.
* `TauCeti.GridState.card_filter_ascent_add_card_filter_descent`: non-inversions plus inversions
  is the total number of ordered column pairs.
* `TauCeti.GridDiagram.maslovOℤ_eq_card`, `TauCeti.GridDiagram.maslovXℤ_eq_card`: the integer
  Maslov gradings written entirely as counts over column indices.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 2, "Gradings.
The `J`-function, `M_O`, `M_X`, `A`", and the standing convention that the gradings must
*compute* on explicit small grids. The southwest count and its reduction to a column-index count
follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.
-/

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- The ordered southwest count of the point sets of two grid states is the number of column
pairs `c < d` at which the source row precedes the target row.

A southwest-comparable pair of occupied squares `(c, x c)` and `(d, y d)` is exactly a pair of
columns with `c < d` and `x c < y d`, so the point-pair count over the two graphs collapses to a
count over column indices. -/
theorem I_pointSet_eq (x y : GridState n) :
    GridPoint.I x.pointSet y.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < y p.2).card := by
  classical
  have hfx : Function.Injective (fun c : Fin n => (c, x c)) :=
    fun _ _ h => congrArg Prod.fst h
  have hfy : Function.Injective (fun c : Fin n => (c, y c)) :=
    fun _ _ h => congrArg Prod.fst h
  have hx : x.pointSet = Finset.univ.image (fun c : Fin n => (c, x c)) := rfl
  have hy : y.pointSet = Finset.univ.image (fun c : Fin n => (c, y c)) := rfl
  rw [GridPoint.I_def, hx, hy,
    ← Finset.prodMap_image_product (fun c : Fin n => (c, x c)) (fun c : Fin n => (c, y c)),
    Finset.filter_image, Finset.card_image_of_injective _ (hfx.prodMap hfy),
    Finset.univ_product_univ]
  refine congrArg Finset.card (Finset.filter_congr fun cd _ => ?_)
  simp only [Prod.map_fst, Prod.map_snd, GridPoint.isSouthWest_iff, Fin.lt_def]

/-- The symmetrized numerator of the grid `J`-function on two state point sets, as a sum of two
column-index counts. -/
theorem JNum_pointSet_eq (x y : GridState n) :
    GridPoint.JNum x.pointSet y.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < y p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ y p.1 < x p.2).card := by
  rw [GridPoint.JNum_def, I_pointSet_eq, I_pointSet_eq]

/-- The rational grid `J`-function on two state point sets is half the sum of the two
column-index counts. -/
theorem J_pointSet_eq (x y : GridState n) :
    GridState.J x y =
      (((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < y p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ y p.1 < x p.2).card : ℕ) : ℚ)
        / 2 := by
  rw [GridState.J_def, GridPoint.J_def, JNum_pointSet_eq]

/-- The self southwest count of a grid state is the number of *non-inversions* of its
permutation: column pairs `c < d` whose occupied rows are in the same order. -/
theorem I_self_pointSet_eq (x : GridState n) :
    GridPoint.I x.pointSet x.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card :=
  I_pointSet_eq x x

/-- The non-inversions and the inversions of a grid state partition the ordered column pairs: the
number of pairs `c < d` with `x c < x d` plus the number with `x d < x c` is the total number of
pairs `c < d`. The state's permutation is injective, so on each ordered column pair exactly one of
the two strict row comparisons holds. -/
theorem card_filter_ascent_add_card_filter_descent (x : GridState n) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card := by
  classical
  have hasc :
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2) =
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).filter
          fun p => x p.1 < x p.2 :=
    (Finset.filter_filter _ _ _).symm
  have hdesc :
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1) =
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).filter
          fun p => ¬ x p.1 < x p.2 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨hlt, hgt⟩
      exact ⟨hlt, not_lt.mpr (le_of_lt hgt)⟩
    · rintro ⟨hlt, hngt⟩
      have hxne : x p.1 ≠ x p.2 := fun h => (ne_of_lt hlt) (x.toPerm.injective h)
      exact ⟨hlt, lt_of_le_of_ne (not_lt.mp hngt) (Ne.symm hxne)⟩
  rw [hasc, hdesc]
  exact Finset.card_filter_add_card_filter_not _

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The integer `O`-Maslov grading of a grid state written entirely as counts over column
indices. Every southwest count in `maslovOℤ` is a state or marking point-set count, so it collapses
to a column-pair count and the grading evaluates without unfolding any point-pair product. -/
theorem maslovOℤ_eq_card (x : GridState n) :
    G.maslovOℤ x =
      ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card : ℤ)
        - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < G.O p.2).card
          + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.1 < x p.2).card)
        + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.1 < G.O p.2).card + 1 := by
  rw [maslovOℤ_def, show G.OSet = G.O.pointSet from rfl, GridState.I_self_pointSet_eq x,
    GridState.JNum_pointSet_eq x G.O, GridState.I_self_pointSet_eq G.O]
  push_cast
  ring

/-- The integer `X`-Maslov grading of a grid state written entirely as counts over column
indices. -/
theorem maslovXℤ_eq_card (x : GridState n) :
    G.maslovXℤ x =
      ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card : ℤ)
        - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < G.X p.2).card
          + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.X p.1 < x p.2).card)
        + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.X p.1 < G.X p.2).card + 1 := by
  rw [maslovXℤ_def, show G.XSet = G.X.pointSet from rfl, GridState.I_self_pointSet_eq x,
    GridState.JNum_pointSet_eq x G.X, GridState.I_self_pointSet_eq G.X]
  push_cast
  ring

end GridDiagram

end TauCeti
