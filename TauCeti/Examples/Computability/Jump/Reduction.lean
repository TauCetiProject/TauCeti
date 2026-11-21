/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Jump.Compiler.Reduction

/-!
# An example of the finite-jump reduction compiler

The zero program reduces the empty set to any set. Iterating the compiler gives reductions
between their corresponding finite jumps.
-/

open TauCeti.Oracle.Single.Code

-- Every iterated jump of the empty set reduces to the matching jump of any set.
example (B : Set ℕ) (n : ℕ) :
    eval (Set.jump^[n] B).oracle (jumpProgram^[n] zero) =
      (Set.jump^[n] (∅ : Set ℕ)).oracle := by
  apply Set.eval_iterate_jumpProgram_of_eval_eq_oracle
  rw [Set.oracle_empty]
  exact funext eval_zero
