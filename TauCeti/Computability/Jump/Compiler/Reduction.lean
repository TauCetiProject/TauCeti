/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Jump.Basic
public import TauCeti.Computability.Jump.Compiler.Basic

/-!
# Compiling reductions between finite iterates of the jump

Given a program computing the oracle of `A` in the oracle of `B`, `Code.jumpProgram` compiles
a program computing the oracle of `A.jump` in the oracle of `B.jump`. It uses the uniform
diagonal index translation and makes one query at the translated index. Iteration gives
a primitive-recursive family of reduction programs for all finite jump levels, and a
primitive-recursive family of one-one maps on indices for the positive levels.
The reduction programs are defined by iterating the noncomputable `Code.jumpProgram`,
so Lean cannot execute this definition of the family.

The only input to the transformation is the program, and its correctness holds for every pair
of set oracles for which that program is a reduction. The underlying jump monotonicity is from
R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.2.
-/

public section

namespace TauCeti.Oracle.Single.Code

variable {A B : Set ℕ}

/-- A program computing the oracle of `A` in the oracle of `B` gives a uniform index
translation from diagonal halting in `A` to diagonal halting in `B`. -/
theorem jumpIndex_mem_jump_iff (d : Code) (hd : eval B.oracle d = A.oracle) (e : ℕ) :
    d.jumpIndex e ∈ B.jump ↔ e ∈ A.jump := by
  simp [hd]

/-- A reduction program for `A` in `B` compiles to one for `A.jump` in `B.jump`. -/
theorem eval_jumpProgram_of_eval_eq_oracle (d : Code) (hd : eval B.oracle d = A.oracle) :
    eval B.jump.oracle d.jumpProgram = A.jump.oracle := by
  have hpre : d.jumpIndex ⁻¹' B.jump = A.jump :=
    Set.ext (d.jumpIndex_mem_jump_iff hd)
  funext e
  simp only [eval_jumpProgram, Set.oracle_apply, ← Set.indicator_comp_right, hpre, Pi.one_comp]

/-- The iterated compiler sends a reduction program for `A` in `B` to a reduction program
between their `n`th jumps. -/
theorem eval_iterate_jumpProgram_of_eval_eq_oracle (d : Code) (hd : eval B.oracle d = A.oracle)
    (n : ℕ) : eval (Set.jump^[n] B).oracle (jumpProgram^[n] d) = (Set.jump^[n] A).oracle := by
  induction n with
  | zero => simpa only [Function.iterate_zero_apply] using hd
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact (jumpProgram^[n] d).eval_jumpProgram_of_eval_eq_oracle ih

/-- The index map at each positive jump level is the diagonal translation by the compiled
reduction program at the preceding level. -/
theorem jumpIndex_mem_iterate_jump_iff (d : Code) (hd : eval B.oracle d = A.oracle) (n e : ℕ) :
    (jumpProgram^[n] d).jumpIndex e ∈ Set.jump^[n + 1] B ↔ e ∈ Set.jump^[n + 1] A := by
  simp only [Function.iterate_succ_apply']
  exact (jumpProgram^[n] d).jumpIndex_mem_jump_iff
    (d.eval_iterate_jumpProgram_of_eval_eq_oracle hd n) e

end TauCeti.Oracle.Single.Code
