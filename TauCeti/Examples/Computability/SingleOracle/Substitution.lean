/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Substitution.Bounded

/-!
# Bounded substitution in a two-step oracle search

The query program shifts each address by one. The search finds a zero at intermediate
address one, using base addresses one and two. Replay needs a base-oracle use bound of at
least three. The second example reuses the maximum-fuel counterexample to show that the
sum of the query and search fuels succeeds on the same run.
-/

open TauCeti.Oracle.Single Code

example : ¬ ∃ j k t, evaln ((comp oracle succ).boundedAnswers (fun x => [0, 1, 0][x]?) j 2) k
      (rfind' oracle) (Nat.pair 0 0) = some t := by
  have h : evaln (fun x => [0, 1, 0][x]?) 4 ((rfind' oracle).subst (comp oracle succ))
      (Nat.pair 0 0) = some ⟨1, 3⟩ := by
    rw [rfind'_subst, oracle_subst]
    refine evaln_succ_rfind'_eq_some.2
      ⟨by decide, ⟨1, 2⟩, ?_, .inr ⟨by decide, ⟨1, 3⟩, ?_, rfl⟩⟩
    · exact evaln_succ_comp_eq_some.2
        ⟨by decide, ⟨1, 0⟩, ⟨1, 2⟩, by simp [Nat.pair], by simp, rfl⟩
    · refine evaln_succ_rfind'_eq_some.2 ⟨by decide, ⟨0, 3⟩, ?_, .inl ⟨rfl, rfl⟩⟩
      exact evaln_succ_comp_eq_some.2
        ⟨by decide, ⟨2, 0⟩, ⟨0, 3⟩, by simp [Nat.pair], by simp, rfl⟩
  rw [exists_evaln_boundedAnswers_iff_use_le h]
  decide

example : ∃ (σ : ℕ → Option ℕ) (c d : Code) (x j k : ℕ) (r : Halt),
    evaln (d.boundedAnswers σ j j) k c x = some r ∧
      evaln σ (max j k) (c.subst d) x = none ∧
      ∃ t, evaln σ (j + k) (c.subst d) x = some t ∧ t.output = r.output ∧ t.use ≤ j := by
  obtain ⟨σ, c, d, x, j, k, r, hrun, hmax⟩ :=
    exists_evaln_boundedAnswers_and_evaln_subst_eq_none_at_max
  exact ⟨σ, c, d, x, j, k, r, hrun, hmax, exists_evaln_subst_of_evaln_boundedAnswers hrun⟩
