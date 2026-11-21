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
  have hmem : d.jumpIndex e ∈ eval (fun _ => Part.none) t e := by
    rw [htranslate, Part.mem_some_iff]
  obtain ⟨j, r, hr, he⟩ := exists_evaln_eq_some_of_mem_eval (σ := fun _ => none)
    (by simp) hmem
  have hzero : r.use = 0 := Nat.eq_zero_of_le_zero
    (evaln_use_le_of_forall_eq_none (fun _ _ => rfl) hr)
  refine ⟨max j (d.jumpIndex e + 1), fun σ k hk => ?_⟩
  have hrun := evaln_eq_some_of_use_eq_zero σ (evaln_mono ((le_max_left _ _).trans hk) hr) hzero
  have hindex := (le_max_right j (d.jumpIndex e + 1)).trans hk
  cases k with
  | zero => simp at hrun
  | succ k =>
    have he' := Nat.lt_succ_iff.1 (evaln_bound hrun)
    have hx : d.jumpIndex e ≤ k := Nat.succ_le_succ_iff.1 hindex
    rw [ht]
    apply Option.ext
    intro q
    rw [evaln_succ_comp_eq_some, Option.map_eq_some_iff]
    constructor
    · rintro ⟨-, r', q', hr', hq', rfl⟩
      rw [evaln_unique hr' hrun] at hq' ⊢
      obtain ⟨-, y, hy, rfl⟩ := evaln_succ_oracle_eq_some.1 hq'
      exact ⟨y, he ▸ hy, by simp [he, hzero]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨he', r, ⟨y, d.jumpIndex e + 1⟩, hrun,
        evaln_succ_oracle_eq_some.2 ⟨he.symm ▸ hx, y, he.symm ▸ hy, by simp [he]⟩,
        by simp [hzero]⟩

/-- A successful bounded run of the jump program has use one more than the translated index. -/
theorem evaln_jumpProgram_use {σ : ℕ → Option ℕ} {k e : ℕ} {d : Code} {r : Halt}
    (h : evaln σ k d.jumpProgram e = some r) : r.use = d.jumpIndex e + 1 := by
  obtain ⟨K, hK⟩ := exists_forall_evaln_jumpProgram_eq_map d e
  have hr := evaln_mono (le_max_left k K) h
  rw [hK σ _ (le_max_right k K)] at hr
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hr
  rfl

end TauCeti.Oracle.Single.Code
