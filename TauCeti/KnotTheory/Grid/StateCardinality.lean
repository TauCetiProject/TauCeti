/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import TauCeti.KnotTheory.Grid.Diagram

/-!
# Cardinality of grid states

This file records the finite size of the generator set for an `n × n` grid complex. A grid state
is encoded in `TauCeti.KnotTheory.Grid.Diagram` as a permutation graph on the columns, so the
set of grid states is equivalent to `Equiv.Perm (Fin n)` and has cardinality `n!`.

The statements here are deliberately about the generator set only. They are the counting API
needed before explicit computations of small fully blocked grid complexes, whose chain module is
the free `ZMod 2`-module on `GridState n`.

## Main results

* `TauCeti.GridState.card`: there are `n!` grid states on an `n × n` grid.
* `TauCeti.GridState.card_univ`: the finite generator set has cardinality `n!`.
* `TauCeti.GridState.uniqueOfLeOne`: for `n ≤ 1`, there is a unique grid state.
* `TauCeti.GridState.card_zero`, `TauCeti.GridState.card_one`, `TauCeti.GridState.card_two`:
  small-grid cardinalities used as sanity checks for later computations.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.1, "Grid diagrams
and grid states", and the standing convention that the grid complexes should compute on explicit
small grids. The encoding follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 3: a grid state is one occupied square in every row and every column.
-/

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- The permutation associated to a grid state by `GridState.equivPerm`. -/
@[simp]
theorem equivPerm_apply (x : GridState n) : equivPerm n x = x.toPerm :=
  rfl

/-- The grid state associated to a permutation by the inverse of `GridState.equivPerm`. -/
@[simp]
theorem equivPerm_symm_apply (σ : Equiv.Perm (Fin n)) : (equivPerm n).symm σ = ⟨σ⟩ :=
  rfl

/-- Converting a permutation to a grid state and evaluating it gives the permutation value. -/
@[simp]
theorem equivPerm_symm_apply_apply (σ : Equiv.Perm (Fin n)) (c : Fin n) :
    ((equivPerm n).symm σ : GridState n) c = σ c :=
  rfl

/-- The point set of the grid state obtained from a permutation `σ` is the graph `{(c, σ c)}`. -/
@[simp]
theorem equivPerm_symm_pointSet (σ : Equiv.Perm (Fin n)) :
    ((equivPerm n).symm σ : GridState n).pointSet =
      Finset.univ.image fun c => (c, σ c) :=
  rfl

/-- The number of grid states on an `n × n` grid is `n!`. -/
@[simp]
theorem card (n : ℕ) : Fintype.card (GridState n) = n.factorial := by
  rw [Fintype.card_congr (equivPerm n), Fintype.card_perm, Fintype.card_fin]

/-- The universe finite set of grid states has cardinality `n!`. -/
@[simp]
theorem card_univ (n : ℕ) : (Finset.univ : Finset (GridState n)).card = n.factorial := by
  rw [Finset.card_univ, card]

/-- The natural cardinality of grid states is `n!`. -/
@[simp]
theorem natCard (n : ℕ) : Nat.card (GridState n) = n.factorial := by
  rw [Nat.card_eq_fintype_card, card]

/-- There is one grid state on the empty grid. -/
theorem card_zero : Fintype.card (GridState 0) = 1 := by
  simp

/-- There is one grid state on a `1 × 1` grid. -/
theorem card_one : Fintype.card (GridState 1) = 1 := by
  simp

/-- There are two grid states on a `2 × 2` grid. -/
theorem card_two : Fintype.card (GridState 2) = 2 := by
  simp

/-- There is a unique grid state whenever the grid has at most one row and column. -/
@[reducible]
def uniqueOfLeOne (hn : n ≤ 1) : Unique (GridState n) := by
  have hcard : Fintype.card (GridState n) ≤ 1 := by
    rw [card]
    rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp
      · omega
  letI : Subsingleton (GridState n) := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact
    { default := (equivPerm n).symm 1
      uniq := fun _ => Subsingleton.elim _ _ }

/-- There is a unique grid state on the empty grid. -/
instance instUniqueZero : Unique (GridState 0) :=
  uniqueOfLeOne (n := 0) (Nat.zero_le 1)

/-- The unique empty-grid state is the state associated to the identity permutation. -/
theorem default_zero_eq : (default : GridState 0) = (equivPerm 0).symm 1 :=
  Subsingleton.elim _ _

/-- There is a unique grid state on a `1 × 1` grid. -/
instance instUniqueOne : Unique (GridState 1) :=
  uniqueOfLeOne (n := 1) (Nat.le_refl 1)

/-- The unique `1 × 1` grid state sends the only column to the only row. -/
@[simp]
theorem apply_eq_zero (x : GridState 1) (c : Fin 1) : x c = 0 := by
  fin_cases c
  exact Subsingleton.elim _ _

/-- The two grid states on a `2 × 2` grid are exactly the identity and the transposition. -/
theorem eq_equivPerm_symm_one_or_eq_equivPerm_symm_swap (x : GridState 2) :
    x = (equivPerm 2).symm 1 ∨ x = (equivPerm 2).symm (Equiv.swap 0 1) := by
  have hne : x 1 ≠ x 0 := fun h => Fin.zero_ne_one (x.toPerm.injective h.symm)
  rcases eq_or_ne (x 0) 0 with h0 | h0
  · left
    ext c
    fin_cases c
    · simpa using h0
    · have h1 : x 1 = 1 :=
        Fin.eq_one_of_ne_zero (x 1) fun hx1 => hne (hx1.trans h0.symm)
      exact congrArg Fin.val h1
  · right
    have hx0 : x 0 = 1 := Fin.eq_one_of_ne_zero (x 0) h0
    ext c
    fin_cases c
    · exact congrArg Fin.val hx0
    · have hx1 : x 1 = 0 := by
        by_contra hx1
        exact hne ((Fin.eq_one_of_ne_zero (x 1) hx1).trans hx0.symm)
      exact congrArg Fin.val hx1

end GridState

end TauCeti
