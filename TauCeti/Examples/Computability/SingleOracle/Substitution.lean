/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Bounded
import TauCeti.Computability.Jump.Reduction

/-!
# Examples of bounded substitution

A search uses a query program that shifts each address by one. The base oracle supplies
a positive answer at one and a zero answer at two, leaving address zero unanswered.
The outer run looks at two entries of the intermediate oracle. The inlined run
needs three base coordinates in its prefix and more fuel than either separate run.
A query program that makes no queries can instead supply answers with a zero use bound.
-/

public section

namespace TauCeti.Oracle.Single.SubstitutionExample

open Code

private def snapshot (x : ℕ) : Option ℕ :=
  if x = 1 then some 1 else if x = 2 then some 0 else none

private def shiftQuery : Code :=
  comp oracle succ

private theorem evaln_shiftQuery_zero :
    evaln snapshot 3 shiftQuery 0 = some ⟨1, 2⟩ :=
  evaln_succ_comp_eq_some.2 ⟨by decide, ⟨1, 0⟩, ⟨1, 2⟩, by simp, by simp [snapshot], rfl⟩

private theorem evaln_shiftQuery_one :
    evaln snapshot 3 shiftQuery 1 = some ⟨0, 3⟩ :=
  evaln_succ_comp_eq_some.2 ⟨by decide, ⟨2, 0⟩, ⟨0, 3⟩, by simp, by simp [snapshot], rfl⟩

private theorem evaln_shiftQuery_one_fuel_two :
    evaln snapshot 2 shiftQuery 1 = none := by
  apply Option.eq_none_iff_forall_ne_some.2
  intro r h
  rw [shiftQuery, evaln_succ_comp_eq_some] at h
  obtain ⟨-, g, f, hg, hf, -⟩ := h
  obtain ⟨-, rfl⟩ := evaln_succ_succ_eq_some.1 hg
  exact (lt_irrefl 2) (evaln_bound hf)

-- The outer search sees nonzero at address zero, then zero at address one.
private theorem evaln_search_boundedAnswers :
    evaln (shiftQuery.boundedAnswers snapshot 3 3) 3 (rfind' oracle) (Nat.pair 0 0) =
      some ⟨1, 2⟩ := by
  have ha : shiftQuery.boundedAnswers snapshot 3 3 (Nat.pair 0 0) = some 1 :=
    boundedAnswers_eq_some_iff.2 ⟨⟨1, 2⟩, evaln_shiftQuery_zero, by decide, rfl⟩
  have hb : shiftQuery.boundedAnswers snapshot 3 3 (Nat.pair 0 1) = some 0 :=
    boundedAnswers_eq_some_iff.2 ⟨⟨0, 3⟩, evaln_shiftQuery_one, le_rfl, rfl⟩
  have htail : evaln (shiftQuery.boundedAnswers snapshot 3 3) 2 (rfind' oracle) (Nat.pair 0 1) =
      some ⟨1, 2⟩ :=
    evaln_succ_rfind'_eq_some.2 ⟨by decide, ⟨0, 2⟩,
      evaln_succ_oracle_eq_some.2 ⟨by decide, 0, hb, rfl⟩, .inl ⟨rfl, rfl⟩⟩
  exact evaln_succ_rfind'_eq_some.2 ⟨by decide, ⟨1, 1⟩,
    evaln_succ_oracle_eq_some.2 ⟨by decide, 1, ha, rfl⟩, .inr ⟨by decide, _, htail, rfl⟩⟩

private theorem evaln_search_subst_fuel_three :
    evaln snapshot 3 ((rfind' oracle).subst shiftQuery) (Nat.pair 0 0) = none := by
  apply Option.eq_none_iff_forall_ne_some.2
  intro t ht
  rw [rfind'_subst, oracle_subst, evaln_succ_rfind'_eq_some] at ht
  obtain ⟨-, f, hf, hcase⟩ := ht
  have hf' : f = ⟨1, 2⟩ := evaln_unique hf evaln_shiftQuery_zero
  subst f
  obtain ⟨-, g, hg, -⟩ := hcase.resolve_left (by simp)
  obtain ⟨-, v, hv, -⟩ := evaln_succ_rfind'_eq_some.1 hg
  have hinput : Nat.pair 0 1 = 1 := by decide
  rw [hinput, evaln_shiftQuery_one_fuel_two] at hv
  contradiction

/-- The maximum of the two separate fuels can be too small for inlining, even when the
intermediate oracle's answers are furnished by a single successful query at each address read. -/
theorem exists_evaln_boundedAnswers_and_evaln_subst_eq_none_at_max :
    ∃ (σ : ℕ → Option ℕ) (c d : Code) (x j k : ℕ) (r : Halt),
      evaln (d.boundedAnswers σ j j) k c x = some r ∧
        evaln σ (max j k) (c.subst d) x = none :=
  ⟨snapshot, rfind' oracle, shiftQuery, Nat.pair 0 0, 3, 3, ⟨1, 2⟩,
    evaln_search_boundedAnswers, evaln_search_subst_fuel_three⟩

-- With a large enough fuel the inlined run has base use three.
private theorem evaln_search_subst :
    evaln snapshot 4 ((rfind' oracle).subst shiftQuery) (Nat.pair 0 0) = some ⟨1, 3⟩ := by
  rw [rfind'_subst, oracle_subst, evaln_succ_rfind'_eq_some]
  have htail : evaln snapshot 3 (rfind' shiftQuery) (Nat.pair 0 1) = some ⟨1, 3⟩ :=
    evaln_succ_rfind'_eq_some.2 ⟨by decide, ⟨0, 3⟩, evaln_shiftQuery_one, .inl ⟨rfl, rfl⟩⟩
  exact ⟨by decide, ⟨1, 2⟩, evaln_mono (by decide) evaln_shiftQuery_zero,
    .inr ⟨by decide, _, htail, rfl⟩⟩

example : ¬ ∃ j k t, evaln (shiftQuery.boundedAnswers snapshot j 2) k (rfind' oracle)
      (Nat.pair 0 0) = some t := by
  rw [exists_evaln_boundedAnswers_iff_use_le evaln_search_subst]
  decide

example : ∃ t, evaln snapshot 6 ((rfind' oracle).subst shiftQuery) (Nat.pair 0 0) =
    some t ∧ t.output = 1 ∧ t.use ≤ 3 :=
  exists_evaln_subst_of_evaln_boundedAnswers evaln_search_boundedAnswers

-- A zero-use query program supplies a zero answer even against an empty base oracle.
example : evaln (zero.boundedAnswers (fun _ => none) 1 0) 1 oracle 0 = some ⟨0, 1⟩ :=
  evaln_succ_oracle_eq_some.2 ⟨le_rfl, 0,
    boundedAnswers_eq_some_iff.2 ⟨⟨0, 0⟩, by simp, le_rfl, rfl⟩, rfl⟩

-- Every iterated jump of the empty set reduces to the matching jump of any set.
example (B : Set ℕ) (n : ℕ) :
    eval (Set.jump^[n] B).oracle (jumpProgram^[n] zero) =
      (Set.jump^[n] (∅ : Set ℕ)).oracle := by
  apply Set.eval_iterate_jumpProgram_of_eval_eq_oracle
  rw [Set.oracle_empty]
  exact funext eval_zero

end TauCeti.Oracle.Single.SubstitutionExample
