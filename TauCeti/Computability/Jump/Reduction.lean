/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Jump.Basic
import TauCeti.Computability.SingleOracle.Recursion
import TauCeti.Data.PFun.Basic

/-!
# Compiling reductions between finite iterates of the jump

Given a program computing the oracle of `A` in the oracle of `B`, `Code.jumpProgram` compiles
a program computing the oracle of `A.jump` in the oracle of `B.jump`. It uses the uniform
diagonal index translation and makes one query at the translated index. Iteration gives
a primitive-recursive family of reduction programs for all finite jump levels, and a
primitive-recursive family of one-one maps on indices for the positive levels.

The only input to the transformation is the program, and its correctness holds for every pair
of set oracles for which that program is a reduction. The underlying jump monotonicity is from
R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.2.
-/

public section

open Encodable Denumerable TauCeti.Oracle.Single

namespace TauCeti.Oracle.Single.Code

private theorem exists_jumpIndexCode : ∃ c : Code, ∀ O,
    eval O c = fun n => Part.some ((ofNat Code n.unpair.1).jumpIndex n.unpair.2) := by
  have h : Primrec fun n : ℕ => (ofNat Code n.unpair.1).jumpIndex n.unpair.2 :=
    primrec₂_jumpIndex.comp ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)
  exact exists_forall_eval_eq_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.1 h))

/-- Compile a program that translates a halting index using `d` and queries its oracle at the
translated index. If `d` computes `A.oracle` relative to `B.oracle`, this program computes
`A.jump.oracle` relative to `B.jump.oracle`. The code for index translation is fixed for
all `d`. -/
noncomputable def jumpProgram (d : Code) : Code :=
  comp oracle (exists_jumpIndexCode.choose.curry (encode d))

/-- The jump program compiler is primitive recursive in the supplied reduction program. -/
theorem primrec_jumpProgram : Primrec jumpProgram :=
  primrec₂_comp.comp (Primrec.const oracle) <|
    primrec₂_curry.comp (Primrec.const exists_jumpIndexCode.choose) Primrec.encode

/-- The jump program consults its oracle at the translated halting index. -/
@[simp]
theorem eval_jumpProgram (O : ℕ →. ℕ) (d : Code) (e : ℕ) :
    eval O d.jumpProgram e = O (d.jumpIndex e) := by
  simp only [jumpProgram, eval_comp, eval_curry, exists_jumpIndexCode.choose_spec,
    Nat.unpair_pair, ofNat_encode, eval_oracle, PFun.some_bind]

/-- Iterating the compiler is primitive recursive jointly in the program and the jump level. -/
theorem primrec₂_iterate_jumpProgram : Primrec₂ fun (d : Code) (n : ℕ) => jumpProgram^[n] d :=
  (Primrec.nat_iterate Primrec.snd Primrec.fst (primrec_jumpProgram.comp Primrec.snd).to₂).to₂

/-- The one-one index maps at positive jump levels are primitive recursive jointly in
the original reduction program, the level (minus one), and the index. -/
theorem primrec_jumpIndex_iterate_jumpProgram :
    Primrec fun p : Code × ℕ × ℕ => (jumpProgram^[p.2.1] p.1).jumpIndex p.2.2 :=
  primrec₂_jumpIndex.comp (primrec₂_iterate_jumpProgram.comp Primrec.fst
    (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

end TauCeti.Oracle.Single.Code

namespace Set

variable {A B : Set ℕ} {d : Code}

/-- A reduction program for `A` in `B` compiles to one for `A.jump` in `B.jump`. -/
theorem eval_jumpProgram_of_eval_eq_oracle (hd : Code.eval B.oracle d = A.oracle) :
    Code.eval B.jump.oracle d.jumpProgram = A.jump.oracle := by
  funext e
  simp only [Code.eval_jumpProgram, oracle_apply]
  have h := jumpIndex_mem_jump_iff hd e
  by_cases he : e ∈ A.jump
  · simp only [indicator_of_mem (h.2 he), indicator_of_mem he, Pi.one_apply]
  · rw [indicator_of_notMem (mt h.1 he), indicator_of_notMem he]

/-- The iterated compiler sends a reduction program for `A` in `B` to a reduction program
between their `n`th jumps. -/
theorem eval_iterate_jumpProgram_of_eval_eq_oracle (hd : Code.eval B.oracle d = A.oracle) (n : ℕ) :
    Code.eval (jump^[n] B).oracle (Code.jumpProgram^[n] d) = (jump^[n] A).oracle := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact eval_jumpProgram_of_eval_eq_oracle ih

/-- The index map at each positive jump level is the diagonal translation by the compiled
reduction program at the preceding level. -/
theorem jumpIndex_mem_iterate_jump_iff (hd : Code.eval B.oracle d = A.oracle) (n e : ℕ) :
    (Code.jumpProgram^[n] d).jumpIndex e ∈ jump^[n + 1] B ↔ e ∈ jump^[n + 1] A := by
  simp only [Function.iterate_succ_apply']
  exact jumpIndex_mem_jump_iff (eval_iterate_jumpProgram_of_eval_eq_oracle hd n) e

end Set
