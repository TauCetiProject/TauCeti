/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Basic
import TauCeti.Computability.SingleOracle.Recursion
import TauCeti.Data.PFun.Basic

/-!
# A compiler for querying translated diagonal indices

`Code.jumpProgram` queries its oracle at the index produced by `Code.jumpIndex`. The
construction works for partial oracles and can be iterated primitive recursively. For
characteristic-function oracles it supplies programs for reductions between finite jumps.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

private theorem exists_jumpIndexCode : ∃ c : Code, ∀ O,
    eval O c = fun n => Part.some ((ofNat Code n.unpair.1).jumpIndex n.unpair.2) := by
  have h : Primrec fun n : ℕ => (ofNat Code n.unpair.1).jumpIndex n.unpair.2 :=
    primrec₂_jumpIndex.comp ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)
  exact exists_forall_eval_eq_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.1 h))

/-- Compile a program that translates a halting index using `d` and queries its oracle at the
translated index. The code for index translation is fixed for all `d`. -/
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

/-- Iterating the compiler is primitive recursive jointly in the program and the number of
iterations. -/
theorem primrec₂_iterate_jumpProgram : Primrec₂ fun (d : Code) (n : ℕ) => jumpProgram^[n] d :=
  (Primrec.nat_iterate Primrec.snd Primrec.fst (primrec_jumpProgram.comp Primrec.snd).to₂).to₂

/-- Translating an index after iterating the compiler is primitive recursive jointly in
the original program, the iteration count, and the index. -/
theorem primrec_jumpIndex_iterate_jumpProgram :
    Primrec fun p : Code × ℕ × ℕ => (jumpProgram^[p.2.1] p.1).jumpIndex p.2.2 :=
  primrec₂_jumpIndex.comp (primrec₂_iterate_jumpProgram.comp Primrec.fst
    (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

end TauCeti.Oracle.Single.Code
