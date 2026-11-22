/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Stage

/-!
# Regression examples: stage computations against fixed and moving oracles

These examples exercise stage-bounded evaluation from a downstream module, through public
statements only. They use the program `oracle`, which on input `0` reads only the answer at
address `0`: against a set not containing `0` it halts with output `0` and use `1`.

* **Fixed versus moving oracles:** against fixed answers a stage computation `evalStage σ s c x`
  persists at every later stage, while the stage computation `evalStage (setAnswers (A s)) s c x`
  against the stages of an enumeration can be lost once a number below its use enters, as happens
  here when the address `0` it reads enters.
-/

open TauCeti.Oracle.Single.Code

/-! ### Fixed versus moving oracles -/

-- Against the fixed answers of `∅`, the computation is found at stage `encode oracle + 1`, the
-- first stage exceeding the program index, and persists at every later stage.
example (t : ℕ) (ht : Encodable.encode oracle + 1 ≤ t) :
    evalStage (setAnswers ∅) t oracle 0 = some ⟨0, 1⟩ :=
  evalStage_mono ht (evalStage_eq_some_of_evaln (k := 1) (by simp) (by omega) (by omega) (by simp))

-- Against the stages of the enumeration in which `0` enters right after that stage, the
-- computation found there is lost at every later stage.
example (t : ℕ) (ht : Encodable.encode oracle + 1 < t) :
    evalStage (setAnswers ↑(if t ≤ Encodable.encode oracle + 1 then (∅ : Finset ℕ) else {0})) t
      oracle 0 ≠ some ⟨0, 1⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : t ≠ 0)
  have hk : ¬k + 1 ≤ Encodable.encode oracle + 1 := by omega
  simp [hk]
