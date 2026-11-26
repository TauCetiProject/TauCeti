/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Logic.Propositional.Clause
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Regression examples: clauses, models and entailment

These examples exercise the semantics of clauses from a downstream module, through public
statements only:

* the empty formula is satisfiable and the formula `{∅}` is not, and over an empty type of
  variables these are the only two formulas;
* `{x, ¬x}` is tautological while `{x, ¬y}` is not, and the latter is false under `x ↦ false`,
  `y ↦ true`, which pins the polarity convention: `(v, true)` is the positive literal;
* the two unit clauses of `x` form an unsatisfiable set that entails every clause;
* the four clauses on two variables are unsatisfiable, and each three of them have exactly one
  model;
* relabelling along a non-injective map can turn a non-tautological clause into a tautology.
-/

open Std.Sat (Literal)
open TauCeti.Propositional

variable {V : Type*}

/-! ### The two degenerate formulas -/

-- The empty formula is satisfiable.
example : Satisfiable ((∅ : CNF V) : Set (Clause V)) := by
  simp

-- The formula consisting of the empty clause is unsatisfiable.
example : ¬Satisfiable (({∅} : CNF V) : Set (Clause V)) :=
  not_satisfiable_of_empty_mem (by simp)

-- Over an empty type of variables, these are the only two formulas.
example [IsEmpty V] (F : CNF V) : F = ∅ ∨ F = {∅} :=
  Finset.subset_singleton_iff.1 fun C _ ↦ Finset.mem_singleton.2 (Finset.eq_empty_of_isEmpty C)

/-! ### Tautologies and the polarity convention -/

-- `{x, ¬x}` is tautological.
example [DecidableEq V] (x : V) : Clause.IsTautology ({(x, true), (x, false)} : Clause V) :=
  Clause.isTautology_iff.2 ⟨(x, true), by simp, by simp⟩

-- `{x, ¬y}` is not tautological for distinct `x` and `y`.
example [DecidableEq V] {x y : V} (hxy : x ≠ y) :
    ¬Clause.IsTautology ({(x, true), (y, false)} : Clause V) := by
  simp [Clause.isTautology_iff, hxy, hxy.symm]

-- `{x, ¬y}` is false under `x ↦ false`, `y ↦ true`: `(x, true)` is the positive literal of `x`.
example [DecidableEq V] {x y : V} (τ : V → Bool) (hx : τ x = false) (hy : τ y = true) :
    ¬Satisfies τ ({(x, true), (y, false)} : Clause V) := by
  simp [hx, hy]

/-! ### The two unit clauses of a variable -/

-- The two unit clauses of `x` are unsatisfiable together.
example [DecidableEq V] (x : V) :
    ¬Satisfiable (({{(x, true)}, {(x, false)}} : CNF V) : Set (Clause V)) := by
  rw [satisfiable_iff]
  rintro ⟨τ, hτ⟩
  simp_all

-- They entail the empty clause, and hence every clause.
example [DecidableEq V] (x : V) (C : Clause V) :
    Entails (({{(x, true)}, {(x, false)}} : CNF V) : Set (Clause V)) C := by
  refine (not_satisfiable_iff_entails_empty.1 ?_).mono_right C.empty_subset
  rw [satisfiable_iff]
  rintro ⟨τ, hτ⟩
  simp_all

/-! ### The four clauses on two variables -/

-- The four clauses `{x, y}, {¬x, y}, {x, ¬y}, {¬x, ¬y}` are unsatisfiable.
example : ¬Satisfiable (({{(0, true), (1, true)}, {(0, false), (1, true)},
    {(0, true), (1, false)}, {(0, false), (1, false)}} : CNF (Fin 2)) : Set (Clause (Fin 2))) := by
  rw [satisfiable_iff]
  rintro ⟨τ, hτ⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, models_insert, models_singleton,
    satisfies_insert, satisfies_singleton] at hτ
  cases h0 : τ 0 <;> cases h1 : τ 1 <;> simp_all

-- Without `{¬x, ¬y}` the only model is `x, y ↦ true`.
example : ∃! τ : Fin 2 → Bool, Models τ (({{(0, true), (1, true)}, {(0, false), (1, true)},
    {(0, true), (1, false)}} : CNF (Fin 2)) : Set (Clause (Fin 2))) := by
  refine ⟨fun _ ↦ true, by simp, fun τ hτ ↦ ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, models_insert, models_singleton,
    satisfies_insert, satisfies_singleton] at hτ
  funext i
  fin_cases i <;> cases h0 : τ 0 <;> cases h1 : τ 1 <;> simp_all

-- Without `{x, ¬y}` the only model is `x ↦ false`, `y ↦ true`.
example : ∃! τ : Fin 2 → Bool, Models τ (({{(0, true), (1, true)}, {(0, false), (1, true)},
    {(0, false), (1, false)}} : CNF (Fin 2)) : Set (Clause (Fin 2))) := by
  refine ⟨![false, true], by simp, fun τ hτ ↦ ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, models_insert, models_singleton,
    satisfies_insert, satisfies_singleton] at hτ
  funext i
  fin_cases i <;> cases h0 : τ 0 <;> cases h1 : τ 1 <;> simp_all

-- Without `{¬x, y}` the only model is `x ↦ true`, `y ↦ false`.
example : ∃! τ : Fin 2 → Bool, Models τ (({{(0, true), (1, true)}, {(0, true), (1, false)},
    {(0, false), (1, false)}} : CNF (Fin 2)) : Set (Clause (Fin 2))) := by
  refine ⟨![true, false], by simp, fun τ hτ ↦ ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, models_insert, models_singleton,
    satisfies_insert, satisfies_singleton] at hτ
  funext i
  fin_cases i <;> cases h0 : τ 0 <;> cases h1 : τ 1 <;> simp_all

-- Without `{x, y}` the only model is `x, y ↦ false`.
example : ∃! τ : Fin 2 → Bool, Models τ (({{(0, false), (1, true)}, {(0, true), (1, false)},
    {(0, false), (1, false)}} : CNF (Fin 2)) : Set (Clause (Fin 2))) := by
  refine ⟨fun _ ↦ false, by simp, fun τ hτ ↦ ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, models_insert, models_singleton,
    satisfies_insert, satisfies_singleton] at hτ
  funext i
  fin_cases i <;> cases h0 : τ 0 <;> cases h1 : τ 1 <;> simp_all

/-! ### Relabelling -/

-- Identifying the two variables of `{x, ¬y}` produces the tautology `{z, ¬z}`.
example : Clause.IsTautology
    (({(0, true), (1, false)} : Clause (Fin 2)).relabel fun _ ↦ ()) := by
  refine Clause.isTautology_iff.2 ⟨((), true), ?_, ?_⟩ <;> simp
