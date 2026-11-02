/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Evaln

/-!
# Regression examples: bounded evaluation of oracle programs, with use

These examples exercise bounded evaluation from a downstream module, through public statements
only:

* query-free instructions succeed with use `0` against any oracle answers;
* a query at address `0` succeeds with use `1`, on a positive and on a negative answer;
* a query beyond a finite oracle string fails: an unanswered query is not a negative answer;
* by the use principle, a run against a finite string succeeds unchanged against an extension of
  the string, and its output is a value of the program relative to every total oracle extending
  the string;
* for a total oracle, the values of a program are exactly the outputs of its successful runs.
-/

open TauCeti.Oracle.Single Code

-- Query-free instructions have use `0`, whatever the oracle answers.
example (σ : ℕ → Option ℕ) : evaln σ 1 succ 0 = some ⟨1, 0⟩ := by
  simp

-- A query at address `0` has use `1`, on a positive answer ...
example : evaln (fun z => [1][z]?) 1 oracle 0 = some ⟨1, 1⟩ := by
  simp

-- ... and on a negative answer.
example : evaln (fun z => [0][z]?) 1 oracle 0 = some ⟨0, 1⟩ := by
  simp

-- A query beyond a finite string fails, at every fuel.
example (k : ℕ) : evaln (fun z => [1][z]?) k oracle 1 = none := by
  cases k with
  | zero => simp
  | succ k => exact Option.eq_none_iff_forall_ne_some.2 fun d => by simp

-- The run against `[1]` succeeds unchanged against the extension `[1, 5]`.
example : evaln (fun z => [1, 5][z]?) 1 oracle 0 = some ⟨1, 1⟩ :=
  evaln_eq_some_of_eqOn (σ := fun z => [1][z]?) (by simp) fun z hz => by
    obtain rfl := Nat.lt_one_iff.1 (Set.mem_Iio.1 hz)
    simp

-- Its output is a value of the oracle instruction relative to every total oracle extending `[1]`.
example (O : ℕ → ℕ) (hO : O 0 = 1) : 1 ∈ eval (fun z => Part.some (O z)) oracle 0 :=
  evaln_sound (σ := fun z => [1][z]?) (k := 1) (d := ⟨1, 1⟩) (by simp) fun z hz y hy => by
    obtain rfl := Nat.lt_one_iff.1 hz
    simp_all

-- For a total oracle, the values of a program are the outputs of its successful runs.
example (O : ℕ → ℕ) (c : Code) (n y : ℕ) :
    y ∈ eval (fun z => Part.some (O z)) c n ↔
      ∃ k d, evaln (fun z => some (O z)) k c n = some d ∧ d.output = y :=
  mem_eval_iff_exists_evaln fun z y => by simp [eq_comm]
