/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Priority.Records

/-!
# Regression examples: priority records

These examples exercise priority records from a downstream module, through public statements
only:

* the guard is load-bearing: on the empty records, the unguarded truncation for an update at
  priority `3` changes the record at priority `0`, of strictly higher priority, while the guarded
  update changes nothing;
* a genuine reset: priority `1` holds a record, attention to priority `0` resets it, and priority
  `1` then recovers with a different record;
* local finiteness without global silence: when requirement `e` receives attention exactly at
  stage `e`, some requirement receives attention at every stage and the records grow without
  bound, yet every record settles.

Requirement `e` attends at stage `n` when the update scheduled at stage `n` has priority `e`; it
has then been applied in the records `run init sched (n + 1)`, and `attentionStages` records the
run index `n + 1`.
-/

open TauCeti.Priority

-- Without the guard, an update at priority `3` on the empty records would install its record at
-- position `0`, of strictly higher priority than the attending requirement.
example : (([] : List ℕ).take 3 ++ [7])[0]? ≠ ([] : List ℕ)[0]? := by decide

-- The guarded update changes nothing out of range.
example : update ([] : List ℕ) ⟨3, 7⟩ = [] := update_of_lt (by simp)

-- A genuine reset: priority `0` attends at stages `0` and `2`, priority `1` at stages `1` and `3`.
-- After two stages priority `1` holds `8`; the attention to priority `0` at stage `2` resets it;
-- priority `1` then recovers with `5`.
example :
    let sched : ℕ → Option (Update ℕ) := fun n =>
      if n = 0 then some ⟨0, 7⟩ else if n = 1 then some ⟨1, 8⟩
      else if n = 2 then some ⟨0, 9⟩ else if n = 3 then some ⟨1, 5⟩ else none
    run [] sched 2 = [7, 8] ∧ run [] sched 3 = [9] ∧ run [] sched 4 = [9, 5] := by
  intro sched
  simp [sched, update_of_le]

-- When requirement `e` attends exactly at stage `e`, its update has been applied after run index
-- `e + 1` only, so every requirement attends finitely often ...
example (e : ℕ) : attentionStages (fun n => some n) e = {e + 1} := by
  ext t
  simp [eq_comm]

-- ... but the records grow without bound ...
example (n : ℕ) : run [] (fun n => some (⟨n, n⟩ : Update ℕ)) n = List.range n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, update_of_le, List.range_succ]

-- ... and each record settles.
example (e : ℕ) : ∃ N, ∀ n, N ≤ n →
    (run [] (fun n => some (⟨n, n⟩ : Update ℕ)) n)[e]? =
      (run [] (fun n => some (⟨n, n⟩ : Update ℕ)) N)[e]? :=
  exists_forall_getElem?_run_eq_of_local _ _ (fun e _ => by
    refine (Set.finite_singleton (e + 1)).subset fun t ht => ?_
    obtain ⟨s, rfl, hs⟩ := mem_attentionStages.1 ht
    simp_all) e
