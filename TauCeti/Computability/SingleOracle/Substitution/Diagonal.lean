/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Basic
public import TauCeti.Computability.SingleOracle.Evaln
import TauCeti.Data.PFun.Basic

/-!
# A compiler for querying translated diagonal indices

`Code.jumpProgram` queries its oracle at the index produced by `Code.jumpIndex`, with
recorded use one more than that index. The compiler chooses its translator code
noncomputably, so Lean cannot execute the definition. The resulting map and its iteration
are primitive recursive. For characteristic-function oracles the compiler supplies programs
for reductions between finite jumps.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

private theorem exists_jumpIndexCode : ∃ c : Code, ∀ O n,
    eval O c n = Part.some ((ofNat Code n.unpair.1).jumpIndex n.unpair.2) :=
  exists_code_of_primrec <|
    primrec₂_jumpIndex.comp ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)

/-- Compile a program that translates a halting index using `d` and queries its oracle at the
translated index. The translator code is chosen noncomputably and fixed for all `d`.
`primrec_jumpProgram` proves primitive recursiveness of the resulting map. -/
noncomputable def jumpProgram (d : Code) : Code :=
  comp oracle (exists_jumpIndexCode.choose.curry (encode d))

private theorem eval_jumpIndexTranslator (O : ℕ →. ℕ) (d : Code) (e : ℕ) :
    eval O (exists_jumpIndexCode.choose.curry (encode d)) e = Part.some (d.jumpIndex e) := by
  simp only [eval_curry, exists_jumpIndexCode.choose_spec, Nat.unpair_pair, ofNat_encode]

/-- The jump program compiler is primitive recursive in the supplied reduction program. -/
theorem primrec_jumpProgram : Primrec jumpProgram :=
  primrec₂_comp.comp (Primrec.const oracle) <|
    primrec₂_curry.comp (Primrec.const exists_jumpIndexCode.choose) Primrec.encode

/-- The jump program consults its oracle at the translated halting index. -/
@[simp]
theorem eval_jumpProgram (O : ℕ →. ℕ) (d : Code) (e : ℕ) :
    eval O d.jumpProgram e = O (d.jumpIndex e) := by
  simp only [jumpProgram, eval_comp, eval_jumpIndexTranslator, eval_oracle, PFun.some_bind]

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
