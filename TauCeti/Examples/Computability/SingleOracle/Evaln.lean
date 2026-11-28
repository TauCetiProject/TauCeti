/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Evaln
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Regression examples: bounded evaluation of oracle programs, with use

These examples exercise bounded evaluation from a downstream module, through public statements
only:

* query-free instructions succeed with use `0` against any oracle answers;
* a query at address `0` succeeds with use `1`, on a positive and on a negative answer;
* a query-free program supplies a bounded answer even with a use bound of `0`;
* a query beyond a finite oracle string fails: an unanswered query is not a negative answer;
* by the use principle, a run against a finite string succeeds unchanged against an extension of
  the string, and its output is a value of the program relative to every total oracle extending
  the string;
* for a total oracle, the values of a program are exactly the outputs of its successful runs;
* a finite batch of runs has a common fuel and use bound: the empty batch needs neither fuel nor
  agreement of the answers, a batch may repeat a program and input, a batch of runs without
  queries persists against all answers, and two runs with different uses persist together against
  all answers agreeing below the larger use.
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

-- A zero-use query program returns zero even when the base answer table supplies no answers.
example : evaln (zero.boundedAnswers (fun _ => none) 1 0) 1 oracle 0 = some ⟨0, 1⟩ :=
  evaln_succ_oracle_eq_some.2 ⟨le_rfl, 0,
    boundedAnswers_eq_some_iff.2 ⟨⟨0, 0⟩, by simp, le_rfl, rfl⟩, rfl⟩

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

-- The empty batch persists at fuel `0` against all answers.
example {ι : Type*} (σ τ : ℕ → Option ℕ) (c : ι → Code) (x : ι → ℕ) (d : ι → Halt) :
    ∀ i ∈ (∅ : Finset ι), evaln τ 0 (c i) (x i) = some (d i) :=
  forall_evaln_eq_some_of_sup_le_of_eqOn (σ := σ) (k := fun _ => 0) (by simp) (by simp)
    (by simp)

-- Two copies of the query at address `3` of a total oracle `O`, and the query-free program
-- `zero` at `5`, have a common fuel and use bound, with the expected outputs.
example (O : ℕ → ℕ) :
    ∃ K U : ℕ, U ≤ K ∧ ∃ d : Fin 3 → Halt,
      (∀ i, (d i).output = ![O 3, O 3, 0] i ∧ (d i).use ≤ U) ∧
      ∀ k, K ≤ k → ∀ τ : ℕ → Option ℕ, Set.EqOn (fun z => some (O z)) τ (Set.Iio U) →
        ∀ i, evaln τ k (![oracle, oracle, zero] i) (![3, 3, 5] i) = some (d i) := by
  obtain ⟨K, U, hUK, d, hd, h⟩ := exists_forall_evaln_eq_some_of_mem_eval
    (O := (O : ℕ →. ℕ)) (σ := fun z => some (O z)) (s := Finset.univ)
    (c := ![oracle, oracle, zero]) (x := ![3, 3, 5]) (y := ![O 3, O 3, 0]) (by simp [eq_comm])
    (by intro i _; fin_cases i <;> simp)
  exact ⟨K, U, hUK, d, fun i => hd i (Finset.mem_univ i),
    fun k hk τ hτ i => h k hk τ hτ i (Finset.mem_univ i)⟩

-- The same batch, run at the fuels `4`, `4` and `6`, persists at every fuel from `6` on against
-- all answers agreeing with `O` below the largest use `4`.
example (O : ℕ → ℕ) (τ : ℕ → Option ℕ) (hτ : ∀ z < 4, τ z = some (O z)) {k : ℕ} (hk : 6 ≤ k) :
    evaln τ k oracle 3 = some ⟨O 3, 4⟩ ∧ evaln τ k zero 5 = some ⟨0, 0⟩ := by
  have h := forall_evaln_eq_some_of_sup_le_of_eqOn (σ := fun z => some (O z)) (τ := τ)
    (s := Finset.univ) (c := ![oracle, oracle, zero]) (x := ![3, 3, 5]) (k := ![4, 4, 6])
    (d := ![⟨O 3, 4⟩, ⟨O 3, 4⟩, ⟨0, 0⟩]) (by intro i; fin_cases i <;> simp)
    ((Finset.sup_le fun i _ => by fin_cases i <;> simp) |>.trans hk)
    fun z hz => (hτ z (hz.trans_le (Finset.sup_le fun i _ => by fin_cases i <;> simp))).symm
  exact ⟨h 0 (Finset.mem_univ _), h 2 (Finset.mem_univ _)⟩

-- A batch of runs without queries persists against all answers: its largest use is `0`.
example (σ τ : ℕ → Option ℕ) :
    evaln τ 3 zero 2 = some ⟨0, 0⟩ ∧ evaln τ 3 succ 2 = some ⟨3, 0⟩ := by
  have h := forall_evaln_eq_some_of_sup_le_of_eqOn (σ := σ) (τ := τ) (s := Finset.univ)
    (c := ![zero, succ]) (x := ![2, 2]) (k := fun _ => 3) (k' := 3) (d := ![⟨0, 0⟩, ⟨3, 0⟩])
    (by intro i; fin_cases i <;> simp) (by simp)
    fun z hz => absurd (hz.trans_le (Finset.sup_le fun i _ => by fin_cases i <;> simp))
      z.not_lt_zero
  exact ⟨h 0 (Finset.mem_univ _), h 1 (Finset.mem_univ _)⟩

-- The queries at `0` and at `2`, with uses `1` and `3`, persist together at every larger fuel
-- against all answers agreeing with the oracle below `3`.
example (O : ℕ → ℕ) (τ : ℕ → Option ℕ) (hτ : ∀ z < 3, τ z = some (O z)) {k : ℕ} (hk : 3 ≤ k) :
    evaln τ k oracle 0 = some ⟨O 0, 1⟩ ∧ evaln τ k oracle 2 = some ⟨O 2, 3⟩ := by
  have h := forall_evaln_eq_some_of_sup_le_of_eqOn (σ := fun z => some (O z)) (τ := τ)
    (s := Finset.univ) (c := fun _ : Fin 2 => oracle) (x := ![0, 2]) (k := ![1, 3])
    (d := ![⟨O 0, 1⟩, ⟨O 2, 3⟩]) (by intro i; fin_cases i <;> simp)
    ((Finset.sup_le fun i _ => by fin_cases i <;> simp) |>.trans hk)
    fun z hz => (hτ z (hz.trans_le (Finset.sup_le fun i _ => by fin_cases i <;> simp))).symm
  exact ⟨h 0 (Finset.mem_univ _), h 1 (Finset.mem_univ _)⟩
