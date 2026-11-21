/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Nonuniform

/-!
# Regression examples: the emptiness indicator has no uniform program

These examples exercise `TauCeti.Computability.SingleOracle.Nonuniform` from a downstream module,
through public statements only:

* the emptiness indicator is `1` on the empty set and `0` on every singleton;
* for each set `Z` some program computes it relative to `Z.oracle`;
* no single program computes it at the input `0` relative to every set oracle, hence none computes
  it uniformly on all inputs;
* the use principle for set oracles transfers a run against the empty oracle with use `u` to the
  singleton `{u}`.
-/

open TauCeti.Oracle.Single Code

-- The prescribed values on the empty set and on a singleton.
example : (∅ : Set ℕ).emptinessIndicator 0 = 1 := by simp

example (u : ℕ) : ({u} : Set ℕ).emptinessIndicator 0 = 0 := by simp

-- For each set oracle, a program depending on it computes the emptiness indicator.
example : ∀ Z : Set ℕ, ∃ c : Code, ∀ x, eval Z.oracle c x = Part.some (Z.emptinessIndicator x) :=
  exists_eval_oracle_eq_emptinessIndicator

-- No single program computes the emptiness indicator at the input `0` for every set oracle.
example : ¬∃ c : Code, ∀ Z : Set ℕ, eval Z.oracle c 0 = Part.some (Z.emptinessIndicator 0) :=
  not_exists_forall_eval_oracle_apply_eq_emptinessIndicator 0

-- Hence no single program computes it on all inputs for every set oracle.
example : ¬∃ c : Code, ∀ Z : Set ℕ, ∀ x, eval Z.oracle c x = Part.some (Z.emptinessIndicator x) :=
  not_exists_forall_eval_oracle_eq_emptinessIndicator

-- A run against the empty oracle with use `u` has the same output relative to `{u}.oracle`.
example {k n : ℕ} {c : Code} {d : Halt} (h : evaln (setAnswers ∅) k c n = some d) :
    d.output ∈ eval ({d.use} : Set ℕ).oracle c n :=
  mem_eval_oracle_of_evaln_setAnswers_eq_some h fun z hz => by simp [hz.ne]
