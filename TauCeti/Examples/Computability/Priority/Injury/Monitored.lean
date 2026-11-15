/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Priority.Initialization
import TauCeti.Computability.Priority.Injury.Monitored

/-!
# Regression examples: multi-oracle injury events and initialization stages

These examples exercise `monitoredInjuryEvents` and `initializationStages` from a downstream module
through public statements only:

* **Label separation:** when `0` enters oracle `false` at stage `1` below an active restraint, it is
  an injury event on `false`, yet neither `(false, 0, 0)` nor `(true, 0, 0)` belongs to
  `monitoredInjuryEvents` for a requirement monitoring `true` whose oracle stays empty. Thus an
  event on one oracle cannot discharge or witness an event claim for another.
* **Initialization without injury:** a higher-priority action at stage `0` places `1` in
  `initializationStages` for priority `1` while `injuryStages` remains empty when the entry occurs
  on the unmonitored oracle (or above the restraint).
-/

open TauCeti.Priority

-- Requirement `0` enumerates `0` into oracle `false` while requirement `1` monitors `true` with
-- active restraint `some 0`: `(0, 0)` is an injury on `false`, yet neither `(false, 0, 0)` nor
-- `(true, 0, 0)` lies in `monitoredInjuryEvents` of requirement `1`.
example :
    let stages : Bool → ℕ → Finset ℕ := fun b s => if b = false ∧ 0 < s then {0} else ∅
    let target : ℕ → Bool := fun e => decide (e % 2 = 1)
    let r : ℕ → ℕ → Option ℕ := fun _ _ => some 0
    (0, 0) ∈ injuryEvents (stages false) r 1 ∧
      (false, 0, 0) ∉ monitoredInjuryEvents stages target r 1 ∧
      (true, 0, 0) ∉ monitoredInjuryEvents stages target r 1 := by
  intro stages target r
  refine ⟨by simp [stages, r], notMem_monitoredInjuryEvents_of_ne (by decide), ?_⟩
  rw [mk_mem_monitoredInjuryEvents]
  simp [stages, target, r]

-- Priority `0` acts at stage `0` and enumerates into oracle `false`; priority `1` monitors `true`
-- with active restraint `some 5`, so `1` is an initialization stage of priority `1` with no injury
-- to its monitored oracle.
example :
    let action : ℕ → Option ℕ := fun s => if s = 0 then some 0 else none
    let stages : Bool → ℕ → Finset ℕ := fun b s => if b = false ∧ 0 < s then {0} else ∅
    1 ∈ initializationStages action 1 ∧
      injuryStages (stages true) (fun _ _ => some 5) 1 = ∅ := by
  intro action stages
  refine ⟨succ_mem_initializationStages.mpr ⟨0, Nat.zero_lt_one, by simp [action]⟩, ?_⟩
  ext t
  rw [mem_injuryStages]
  simp [stages, Finset.eq_empty_iff_forall_notMem]
