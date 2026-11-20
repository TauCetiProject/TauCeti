/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Jump.Compiler.Basic
public import TauCeti.Computability.SingleOracle.Evaln
-- The use proof inspects the compiler and its private translator evaluation lemma.
import all TauCeti.Computability.Jump.Compiler.Basic

/-!
# Bounded use of compiled jump queries

A successful bounded run of `Code.jumpProgram` records use equal to the translated index plus
one. The translator makes no oracle queries, so the recorded use comes from the final query.
-/

public section

open Encodable

namespace TauCeti.Oracle.Single.Code

/-- A successful bounded run of the jump program has use one more than the translated index. -/
theorem evaln_jumpProgram_use {σ : ℕ → Option ℕ} {k e : ℕ} {d : Code} {r : Halt}
    (h : evaln σ k d.jumpProgram e = some r) : r.use = d.jumpIndex e + 1 := by
  cases k with
  | zero => simp at h
  | succ k =>
    rw [jumpProgram] at h
    obtain ⟨-, t, q, ht, hq, rfl⟩ := evaln_succ_comp_eq_some.1 h
    obtain ⟨-, _, -, rfl⟩ := evaln_succ_oracle_eq_some.1 hq
    -- A successful run of the translator on the empty oracle witnesses that it makes no queries.
    let O : ℕ →. ℕ := fun _ => Part.none
    have hmem : d.jumpIndex e ∈
        eval O (exists_jumpIndexCode.choose.curry (encode d)) e := by
      rw [eval_jumpIndexTranslator, Part.mem_some_iff]
    obtain ⟨j, s, hs, he⟩ := exists_evaln_eq_some_of_mem_eval (σ := fun _ => none)
      (by simp [O]) hmem
    have huse : s.use = 0 :=
      Nat.eq_zero_of_le_zero (evaln_use_le_of_forall_eq_none (fun _ _ => rfl) hs)
    have hts := evaln_unique ht (evaln_eq_some_of_use_eq_zero σ hs huse)
    simp [hts, huse, he]

end TauCeti.Oracle.Single.Code
