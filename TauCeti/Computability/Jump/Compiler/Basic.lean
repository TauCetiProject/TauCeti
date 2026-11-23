/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Jump.Compiler.Index
import TauCeti.Data.PFun.Basic

/-!
# A compiler for querying translated diagonal indices

`Code.jumpProgram` queries its oracle at the index produced by `Code.jumpIndex`. The compiler
chooses its translator code noncomputably. The resulting map and its iteration are primitive
recursive. A program computing the characteristic-function oracle of `A` in that of `B` compiles
to a reduction from `A.jump` to `B.jump`. Iteration lifts the supplied reduction to matching
finite jump levels.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

private theorem exists_jumpIndexCode : ∃ c : Code, ∀ O n,
    eval O c n = Part.some ((ofNat Code n.unpair.1).jumpIndex n.unpair.2) :=
  exists_code_of_computable <| Primrec.to_comp <|
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

/-- The compiled jump program composes one oracle query with a translator that returns the
translated index relative to every partial oracle, including the nowhere-defined one. -/
theorem exists_jumpProgram_eq_comp_oracle (d : Code) :
    ∃ t : Code, d.jumpProgram = comp oracle t ∧
      ∀ (O : ℕ →. ℕ) (e : ℕ), eval O t e = Part.some (d.jumpIndex e) :=
  ⟨_, rfl, fun O => eval_jumpIndexTranslator O d⟩

/-- The jump program compiler is primitive recursive in the supplied reduction program. -/
theorem primrec_jumpProgram : Primrec jumpProgram :=
  primrec₂_comp.comp (Primrec.const oracle) <|
    primrec₂_curry.comp (Primrec.const exists_jumpIndexCode.choose) Primrec.encode

/-- The jump program consults its oracle at the translated halting index. -/
@[simp]
theorem eval_jumpProgram (O : ℕ →. ℕ) (d : Code) (e : ℕ) :
    eval O d.jumpProgram e = O (d.jumpIndex e) := by
  simp only [jumpProgram, eval_comp, eval_jumpIndexTranslator, eval_oracle, PFun.some_bind]

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
