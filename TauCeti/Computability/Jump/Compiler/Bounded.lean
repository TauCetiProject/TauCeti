/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Jump.Compiler.Basic
public import TauCeti.Computability.SingleOracle.Evaln

/-!
# Bounded use of compiled jump queries

At sufficient fuel, `Code.jumpProgram` returns the answer at the translated index if supplied.
The fuel threshold is independent of the answer table. Every successful run records use equal
to the translated index plus one.
-/

public section

namespace TauCeti.Oracle.Single.Code

/-- At sufficiently large fuel, the compiled jump program returns the translated oracle
answer with use one more than the translated index, or `none` if the answer is missing.
The same fuel threshold works for every answer table. -/
theorem exists_forall_evaln_jumpProgram_eq_map (d : Code) (e : ℕ) :
    ∃ K, ∀ (σ : ℕ → Option ℕ) (k : ℕ), K ≤ k →
      evaln σ k d.jumpProgram e = (σ (d.jumpIndex e)).map (fun y => ⟨y, d.jumpIndex e + 1⟩) := by
  obtain ⟨t, ht, htranslate⟩ := exists_jumpProgram_eq_comp_oracle d
  rw [ht]
  exact exists_forall_evaln_comp_oracle_eq_map (htranslate _ e ▸ Part.mem_some _)

/-- A successful bounded run of the jump program has use one more than the translated index. -/
theorem evaln_jumpProgram_use {σ : ℕ → Option ℕ} {k e : ℕ} {d : Code} {r : Halt}
    (h : evaln σ k d.jumpProgram e = some r) : r.use = d.jumpIndex e + 1 := by
  obtain ⟨t, ht, htranslate⟩ := exists_jumpProgram_eq_comp_oracle d
  rw [ht] at h
  exact evaln_comp_oracle_use (htranslate _ e ▸ Part.mem_some _) h

end TauCeti.Oracle.Single.Code
