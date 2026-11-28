/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Logic.Propositional.Formula

/-!
# Regression examples: propositional formulas and negation normal form

These examples exercise propositional formulas from a downstream module, through public
statements only:

* `and (var x) (neg (var x))` has size `2` and three subformulas, and is unsatisfiable;
* subformulas form a set: `and φ φ` for `φ = or (var x) (var x)` has three subformulas, fewer than
  the bound `size + 1 = 4` of `card_subformulas_le`;
* the negation normal form of `neg (and (var x) (neg (var y)))` is `or (neg (var x)) (var y)`,
  and the formula obtained without flipping the connective is not equivalent to the original;
* a double negation and a negated constant are not in negation normal form;
* two distinct variables are equisatisfiable formulas that are not equivalent.
-/

open TauCeti.Propositional PropForm

variable {V : Type*} [DecidableEq V]

/-! ### A contradiction -/

example (x : V) : (and (var x) (neg (var x))).size = 2 := by
  simp

example (x : V) : (and (var x) (neg (var x))).subformulas.card = 3 := by
  simp

-- The formula is false under both values of `x`, so it is unsatisfiable.
example (x : V) (τ : V → Bool) : (and (var x) (neg (var x))).eval τ = false := by
  simp

example (x : V) : ¬(and (var x) (neg (var x))).Satisfiable := by
  simp [satisfiable_iff]

/-! ### Subformulas form a set -/

example (x : V) : (or (var x) (var x)).size = 1 ∧ (or (var x) (var x)).subformulas.card = 2 := by
  simp

example (x : V) :
    (and (or (var x) (var x)) (or (var x) (var x))).size = 3 ∧
      (and (or (var x) (var x)) (or (var x) (var x))).subformulas.card = 3 ∧
      (and (or (var x) (var x)) (or (var x) (var x))).vars.card = 1 := by
  simp

/-! ### Negation normal form -/

example (x y : V) : (neg (and (var x) (neg (var y)))).nnf = or (neg (var x)) (var y) := by
  simp [nnf_eq_toNNF]

-- Forgetting to flip `and` into `or` changes the value under `x ↦ true`, `y ↦ true`.
example (x y : V) (τ : V → Bool) (hx : τ x = true) (hy : τ y = true) :
    (and (neg (var x)) (var y)).eval τ ≠ (neg (and (var x) (neg (var y)))).eval τ := by
  simp [hx, hy]

example (x : V) : ¬(neg (neg (var x))).IsNNF := by
  simp

example : ¬(neg tru : PropForm V).IsNNF := by
  simp

example (x : V) : (or (neg (var x)) tru).IsNNF := by
  simp

example (x : V) : (neg (neg (var x))).nnf = var x := by
  simp [nnf_eq_toNNF]

/-! ### Equisatisfiable but not equivalent -/

example {x y : V} (hxy : x ≠ y) :
    (var x).Equisatisfiable (var y) ∧ ¬(var x).Equivalent (var y) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · simp only [equisatisfiable_iff, satisfiable_iff, eval_var]
    exact ⟨fun _ ↦ ⟨fun _ ↦ true, rfl⟩, fun _ ↦ ⟨fun _ ↦ true, rfl⟩⟩
  · exact hxy.symm (by simpa using equivalent_iff.1 h fun v ↦ decide (v = x))
