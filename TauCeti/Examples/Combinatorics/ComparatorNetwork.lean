/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ComparatorNetwork.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Examples of comparator networks

The network `(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)` on four wires sorts every input of zeros and
ones, which a finite check confirms; by the zero-one principle it sorts every linear order. On the
input `(3, 1, 2, 0)` its output is `(0, 1, 2, 3)`.

A comparator puts the smaller value on its first wire, whatever the order of the two wires: the
comparator `(2, 0)` on three wires sends `(5, 6, 7)` to `(7, 6, 5)`. The single comparator
`(0, 2)` on three wires sends `(7, 6, 5)` to `(5, 6, 7)`, but it does not sort: its output on
`(2, 0, 1)` is `(1, 0, 2)`, and the threshold at the value `1` gives the input `(1, 0, 1)` of
zeros and ones, which it leaves unchanged. On one wire the network `(0, 0), (0, 0)` changes
nothing, and the empty network on `n` wires sorts `Bool` exactly when `n ≤ 1`.

The hypothesis of `TauCeti.ComparatorNetwork.apply_comp_of_monotone` is needed: negation on
`Bool` does not commute with the comparator `(0, 1)` on the input `(false, true)`.
-/

public section

namespace TauCeti.Examples.ComparatorNetwork

open TauCeti ComparatorNetwork

/-- A sorting network on four wires with five comparators. -/
abbrev sortFour : ComparatorNetwork 4 := [(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)]

example : sortFour.apply ![(3 : ℕ), 1, 2, 0] = ![0, 1, 2, 3] := by
  funext k
  fin_cases k <;> simp [sortFour, comparator_apply]

/-- `sortFour` sorts every input of zeros and ones. -/
theorem sortFour_sorts_bool : sortFour.Sorts Bool := by
  have key : ∀ a b c d : Bool, ∀ i j : Fin 4, i ≤ j →
      sortFour.apply ![a, b, c, d] i ≤ sortFour.apply ![a, b, c, d] j := by
    simp only [sortFour, apply_cons, apply_nil, comparator_apply]
    decide
  refine sorts_iff.2 fun x i j hij => ?_
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    funext k
    fin_cases k <;> rfl
  rw [hx]
  exact key _ _ _ _ i j hij

/-- By the zero-one principle, `sortFour` sorts the natural numbers. -/
example : sortFour.Sorts ℕ :=
  sorts_of_sorts_bool _ sortFour_sorts_bool ℕ

example : comparator ((2, 0) : Fin 3 × Fin 3) ![(5 : ℕ), 6, 7] = ![7, 6, 5] := by
  funext k
  fin_cases k <;> simp [comparator_apply]

/-- The network with the single comparator `(0, 2)` on three wires. -/
abbrev outerThree : ComparatorNetwork 3 := [(0, 2)]

example : outerThree.apply ![(7 : ℕ), 6, 5] = ![5, 6, 7] := by
  funext k
  fin_cases k <;> simp [outerThree, comparator_apply]

example : outerThree.apply ![(2 : ℕ), 0, 1] = ![1, 0, 2] := by
  funext k
  fin_cases k <;> simp [outerThree, comparator_apply]

example : outerThree.apply ![true, false, true] = ![true, false, true] := by
  funext k
  fin_cases k <;> simp [outerThree, comparator_apply]

/-- `outerThree` does not sort `Bool`. -/
example : ¬outerThree.Sorts Bool := by
  intro h
  have := sorts_iff.1 h ![true, false, true] (by decide : (0 : Fin 3) ≤ 1)
  simp [outerThree, comparator_apply, Bool.le_iff_imp] at this

example (x : Fin 1 → ℕ) : ComparatorNetwork.apply [((0 : Fin 1), (0 : Fin 1)), (0, 0)] x = x := by
  simp

/-- The empty network on `n` wires sorts `Bool` exactly when `n ≤ 1`. -/
example (n : ℕ) : ComparatorNetwork.Sorts ([] : ComparatorNetwork n) Bool ↔ n ≤ 1 := by
  refine ⟨fun h => ?_, fun hn => ?_⟩
  · by_contra hn
    have h2 : 1 < n := by omega
    have := sorts_iff.1 h (fun k => decide ((k : ℕ) = 0))
      (Fin.mk_le_mk.2 zero_le_one : (⟨0, by omega⟩ : Fin n) ≤ ⟨1, h2⟩)
    simp [Bool.le_iff_imp] at this
  · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 hn
    exact sorts_iff.2 fun x => Subsingleton.monotone _

/-- A map that is not monotone need not commute with a comparator. -/
example : comparator ((0, 1) : Fin 2 × Fin 2) (not ∘ ![false, true]) ≠
    not ∘ comparator (0, 1) ![false, true] := by
  intro h
  have := congrFun h 0
  simp [comparator_apply] at this

end TauCeti.Examples.ComparatorNetwork
