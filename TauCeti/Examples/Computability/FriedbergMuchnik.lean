/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.FriedbergMuchnik.Basic

/-!
# Regression examples: the original Friedberg–Muchnik construction

These examples exercise the public interface of `TauCeti.Computability.FriedbergMuchnik` from a
downstream module without unfolding stage-machine definitions:

* initial stage sets, column witnesses, inactive restraints, and agreement with `soareMarkers`;
* separation of witness appointment/reappointment stages from attention stages, and disjointness of
  the two constructed c.e. sets;
* label separation of `monitoredInjuryEvents` between even (`R_{2e}`) and odd (`R_{2e+1}`)
  requirements, together with concrete finite-injury bounds at priorities `0`, `1`, and `2`;
* existence of incomparable c.e. sets and Turing degrees strictly between `0` and `0'`.
-/

open TauCeti TauCeti.FriedbergMuchnik TauCeti.Priority

-- Stage `0` starts with empty approximations, column witnesses `(0, j)`, and inactive restraints,
-- matching Soare's marker recurrence at every priority.
example (j : ℕ) :
    stage false 0 = ∅ ∧ stage true 0 = ∅ ∧
      witness j 0 = Nat.pair 0 j ∧ restraint j 0 = none ∧
      (witness j 0, restraint j 0) = soareMarkers 0 j :=
  ⟨stage_zero false, stage_zero true, witness_zero j, restraint_zero j,
    witness_restraint_eq_soareMarkers 0 j⟩

-- Appointment/reappointment stages never coincide with attention stages, and the two limit sets
-- are disjoint because even and odd priorities enumerate into disjoint pairing columns.
example (j : ℕ) :
    Disjoint (appointmentStages j) (attentionStages action j) ∧
      Disjoint friedbergMuchnikSetA friedbergMuchnikSetB :=
  ⟨disjoint_appointmentStages_attentionStages j,
    disjoint_friedbergMuchnikSetA_friedbergMuchnikSetB⟩

-- Even requirements `R_{2d}` monitor `B` (`true`) while odd requirements `R_{2e+1}` monitor `A`
-- (`false`), so their labelled injury-event sets are disjoint for all `d, e`.
example (d e : ℕ) :
    Disjoint (monitoredInjuryEvents stage monitoredSide restraint (2 * d))
      (monitoredInjuryEvents stage monitoredSide restraint (2 * e + 1)) := by
  refine disjoint_monitoredInjuryEvents_of_target_ne ?_
  simp

-- Concrete finite-injury budgets at priorities `0`, `1`, and `2`.
example :
    injurySet (stage (monitoredSide 0)) restraint 0 = ∅ ∧
      (attentionStages action 1).ncard ≤ 2 ∧
      (monitoredInjuryEvents stage monitoredSide restraint 1).ncard ≤ 1 ∧
      (monitoredInjuryEvents stage monitoredSide restraint 2).ncard ≤ 3 :=
  ⟨injurySet_zero_eq_empty,
    (finite_attentionStages_and_ncard_le 1).2,
    (finite_monitoredInjuryEvents_and_ncard_le 1).2,
    (finite_monitoredInjuryEvents_and_ncard_le 2).2⟩

-- The Friedberg–Muchnik theorem and its Turing-degree form strictly between `0` and `0'`.
example :
    (∃ A B : Set ℕ, REPred (· ∈ A) ∧ REPred (· ∈ B) ∧
      ¬TuringReducible A.oracle B.oracle ∧ ¬TuringReducible B.oracle A.oracle) ∧
    (∃ A B : Set ℕ, REPred (· ∈ A) ∧ REPred (· ∈ B) ∧
      toAntisymmetrization TuringReducible A.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      toAntisymmetrization TuringReducible B.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      ¬(toAntisymmetrization TuringReducible A.oracle ≤
          toAntisymmetrization TuringReducible B.oracle) ∧
      ¬(toAntisymmetrization TuringReducible B.oracle ≤
          toAntisymmetrization TuringReducible A.oracle)) :=
  ⟨friedberg_muchnik, exists_incomparable_ce_turingDegrees_mem_Ioo⟩
