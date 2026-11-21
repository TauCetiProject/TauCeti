/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Substitution.Bounded
-- The concrete search certificates compute using the evaluator's defining equations.
import all TauCeti.Computability.SingleOracle.Evaln

/-!
# Bounded substitution in a two-step oracle search

The query program shifts each address by one. The search finds a zero at intermediate
address one, using base addresses one and two. Replay needs a base-oracle use bound of at
least three, and adding the query and search fuels suffices to inline the search.
-/

open TauCeti.Oracle.Single Code

example : ¬ ∃ j k t, evaln ((comp oracle succ).boundedAnswers (fun x => [0, 1, 0][x]?) j 2) k
      (rfind' oracle) (Nat.pair 0 0) = some t := by
  have h : evaln (fun x => [0, 1, 0][x]?) 4 ((rfind' oracle).subst (comp oracle succ))
      (Nat.pair 0 0) = some ⟨1, 3⟩ := by
    simp [evaln, Nat.unpaired, Nat.unpair, Nat.pair]
  rw [exists_evaln_boundedAnswers_iff_use_le h]
  decide

example : ∃ t, evaln (fun x => [0, 1, 0][x]?) 6 ((rfind' oracle).subst (comp oracle succ))
    (Nat.pair 0 0) = some t ∧ t.output = 1 ∧ t.use ≤ 3 :=
  exists_evaln_subst_of_evaln_boundedAnswers (j := 3) (k := 3) (r := ⟨1, 2⟩) (by
    simp [evaln, boundedAnswers_def, Nat.unpaired, Nat.unpair, Nat.pair])
