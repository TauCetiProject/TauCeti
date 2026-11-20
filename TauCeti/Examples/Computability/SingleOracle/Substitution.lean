/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Bounded

/-!
# A zero-use example of bounded substitution

A query program that makes no oracle queries can supply an answer with a zero use bound.
-/

public section

namespace TauCeti.Oracle.Single.SubstitutionExample

open Code

-- A zero-use query program supplies a zero answer even against an empty base oracle.
example : evaln (zero.boundedAnswers (fun _ => none) 1 0) 1 oracle 0 = some ⟨0, 1⟩ :=
  evaln_succ_oracle_eq_some.2 ⟨le_rfl, 0,
    boundedAnswers_eq_some_iff.2 ⟨⟨0, 0⟩, by simp, le_rfl, rfl⟩, rfl⟩

end TauCeti.Oracle.Single.SubstitutionExample
