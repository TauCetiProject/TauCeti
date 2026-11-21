/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Bounded

/-!
# Bounded substitution in a two-step oracle search

The query program shifts each address by one. The search finds a zero at intermediate
address one, using base addresses one and two. Replay needs a base-oracle use bound of at
least three. The second example reuses the maximum-fuel counterexample to show that the
sum of the query and search fuels succeeds on the same run.
-/

namespace TauCeti.Oracle.Single.Code

private theorem evaln_comp_oracle_succ {σ : ℕ → Option ℕ} {k n : ℕ} :
    evaln σ k (comp oracle succ) n =
      if n + 1 < k then (σ (n + 1)).map (fun y => ⟨y, n + 2⟩) else none := by
  cases k with
  | zero => simp
  | succ k =>
    rw [evaln_comp_oracle]
    by_cases hn : n ≤ k
    · have hr : evaln σ (k + 1) succ n = some ⟨n + 1, 0⟩ :=
        evaln_succ_succ_eq_some.2 ⟨hn, rfl⟩
      simp [hr]
    · have hr : evaln σ (k + 1) succ n = none := evaln_eq_none_of_le (by omega)
      have hq : ¬ n + 1 < k + 1 := by omega
      simp [hr, hq]

private def searchAnswers (x : ℕ) : Option ℕ :=
  if x = 1 then some 1 else if x = 2 then some 0 else none

private def shiftQuery : Code :=
  comp oracle succ

-- The outer search sees nonzero at address zero, then zero at address one.
private theorem evaln_search_boundedAnswers :
    evaln (shiftQuery.boundedAnswers searchAnswers 3 3) 3 (rfind' oracle) (Nat.pair 0 0) =
      some ⟨1, 2⟩ := by
  have hanswer {x y : ℕ} (hx : x + 1 < 3) (hy : searchAnswers (x + 1) = some y) :
      shiftQuery.boundedAnswers searchAnswers 3 3 x = some y := by
    have hrun : evaln searchAnswers 3 shiftQuery x = some ⟨y, x + 2⟩ := by
      simp [shiftQuery, evaln_comp_oracle_succ, hx, hy]
    exact boundedAnswers_eq_some_iff.2 ⟨_, hrun, evaln_use_le hrun, rfl⟩
  have hfirst : evaln (shiftQuery.boundedAnswers searchAnswers 3 3) 3 oracle (Nat.pair 0 0) =
      some ⟨1, 1⟩ := evaln_succ_oracle_eq_some.2 ⟨by decide, 1, hanswer (by decide) rfl, rfl⟩
  have hsecond : evaln (shiftQuery.boundedAnswers searchAnswers 3 3) 2 oracle (Nat.pair 0 1) =
      some ⟨0, 2⟩ := evaln_succ_oracle_eq_some.2 ⟨by decide, 0, hanswer (by decide) rfl, rfl⟩
  rw [evaln_succ_rfind', hfirst, evaln_succ_rfind', hsecond]
  rfl

private theorem evaln_search_subst_fuel_three :
    evaln searchAnswers 3 ((rfind' oracle).subst shiftQuery) (Nat.pair 0 0) = none := by
  simp only [rfind'_subst, oracle_subst, shiftQuery, evaln_succ_rfind', evaln_comp_oracle_succ]
  rfl

/-- The maximum of the separate fuels can be too small, even for an answer program that
makes just one query. -/
public theorem exists_evaln_boundedAnswers_and_evaln_subst_eq_none_at_max :
    ∃ (σ : ℕ → Option ℕ) (c d : Code) (x j k : ℕ) (r : Halt),
      evaln (d.boundedAnswers σ j j) k c x = some r ∧
        evaln σ (max j k) (c.subst d) x = none :=
  ⟨searchAnswers, rfind' oracle, shiftQuery, Nat.pair 0 0, 3, 3, ⟨1, 2⟩,
    evaln_search_boundedAnswers, evaln_search_subst_fuel_three⟩

example : ¬ ∃ j k t, evaln ((comp oracle succ).boundedAnswers (fun x => [0, 1, 0][x]?) j 2) k
      (rfind' oracle) (Nat.pair 0 0) = some t := by
  have h : evaln (fun x => [0, 1, 0][x]?) 4 ((rfind' oracle).subst (comp oracle succ))
      (Nat.pair 0 0) = some ⟨1, 3⟩ := by
    simp only [rfind'_subst, oracle_subst, evaln_succ_rfind', evaln_comp_oracle_succ]
    rfl
  rw [exists_evaln_boundedAnswers_iff_use_le h]
  decide

example : ∃ (σ : ℕ → Option ℕ) (c d : Code) (x j k : ℕ) (r : Halt),
    evaln (d.boundedAnswers σ j j) k c x = some r ∧
      evaln σ (max j k) (c.subst d) x = none ∧
      ∃ t, evaln σ (j + k) (c.subst d) x = some t ∧ t.output = r.output ∧ t.use ≤ j := by
  obtain ⟨σ, c, d, x, j, k, r, hrun, hmax⟩ :=
    exists_evaln_boundedAnswers_and_evaln_subst_eq_none_at_max
  exact ⟨σ, c, d, x, j, k, r, hrun, hmax, exists_evaln_subst_of_evaln_boundedAnswers hrun⟩

end TauCeti.Oracle.Single.Code
