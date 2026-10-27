/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Priority records and their stabilization

A priority construction keeps, at each stage, a finite list of records indexed by priority, with
smaller index meaning higher priority. When requirement `e` receives attention it installs a new
record at position `e` and **resets** every record of lower priority: the list is truncated after
position `e`. This is the initialization of lower-priority requirements. It is bookkeeping about
records only; whether a reset is accompanied by an injury, an entry into a protected oracle
interval, is a separate question that this file does not address.

The update is **guarded**: attention at a priority beyond the end of the list leaves the records
unchanged. Without the guard, truncating and appending would place the new record at the end of
the list, a position of higher priority than the attending requirement.

## Main definitions

* `TauCeti.Priority.Update`: a priority together with the record to install there.
* `TauCeti.Priority.update`: the guarded update of a list of records.
* `TauCeti.Priority.run`: the records after `n` stages of a schedule of updates.
* `TauCeti.Priority.attentionStages`: for a priority schedule `ℕ → Option ℕ`, the run indices
  `s + 1` after which an update of priority `e`, scheduled at stage `s`, has been applied.

## Main results

* `TauCeti.Priority.getElem?_update_of_lt`: **locality**. An update at priority `e` leaves every
  record of strictly higher priority unchanged.
* `TauCeti.Priority.getElem?_update_of_gt`: an update in range resets every record of strictly
  lower priority.
* `TauCeti.Priority.all_attention_finite_of_local`: if each requirement receives attention
  finitely often whenever every higher-priority requirement does, then every requirement receives
  attention finitely often.
* `TauCeti.Priority.exists_forall_getElem?_run_eq_of_finite`: if requirements `0, …, e` each
  receive attention finitely often, the record at position `e` eventually stops changing.
* `TauCeti.Priority.exists_forall_getElem?_run_eq_of_local`: under the conditional local
  finiteness hypothesis, every record eventually stops changing.

The stabilization theorem assumes only the conditional local finiteness of attention: no
scheduling discipline, no bound on how often a requirement receives attention, and no effective
stabilization stage. Stabilization of a record is not satisfaction of its requirement.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.
* Ported from `cameronfreer/computable-model-theory` at commit
  `a1fe76155a98f03933f7de0811e03b2473dd2e21`:
  `ComputableModelTheory/Computability/FiniteInjury.lean` and its audit
  `FiniteInjuryAudit.lean`.
* Divergences from that source: records are a plain `List` rather than a wrapper structure;
  truncation of lower-priority records is called a reset (initialization), not an injury;
  attention is counted by the sets `attentionStages` of a priority schedule `ℕ → Option ℕ`, and
  local finiteness is stated as finiteness of these sets; the separate goodness predicate is not
  included.
-/

public section

namespace TauCeti

namespace Priority

variable {α : Type*}

/-- An update: install `value` at priority `prio`, resetting every record of strictly lower
priority. -/
structure Update (α : Type*) where
  /-- The priority receiving attention. -/
  prio : ℕ
  /-- The record installed at that priority. -/
  value : α

/-- **The guarded update.** In range, keep the records of higher priority, install the new record,
and reset the rest; out of range, change nothing. -/
def update (s : List α) (u : Update α) : List α :=
  if u.prio ≤ s.length then s.take u.prio ++ [u.value] else s

/-- In range, an update keeps the records of higher priority and installs the new record last. -/
theorem update_of_le {s : List α} {u : Update α} (h : u.prio ≤ s.length) :
    update s u = s.take u.prio ++ [u.value] :=
  ite_eq_left h

/-- Out of range, an update changes nothing. -/
@[simp]
theorem update_of_lt {s : List α} {u : Update α} (h : s.length < u.prio) : update s u = s :=
  ite_eq_right (Nat.not_le.2 h)

/-- **Locality.** An update at priority `e` leaves every record of strictly higher priority
unchanged. -/
@[simp]
theorem getElem?_update_of_lt (s : List α) (u : Update α) {i : ℕ} (h : i < u.prio) :
    (update s u)[i]? = s[i]? := by
  rcases Nat.lt_or_ge s.length u.prio with hlt | hle
  · rw [update_of_lt hlt]
  · rw [update_of_le hle, List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h]

/-- An update in range installs its record at its own priority. -/
@[simp]
theorem getElem?_update_self {s : List α} {u : Update α} (h : u.prio ≤ s.length) :
    (update s u)[u.prio]? = some u.value := by
  rw [update_of_le h, List.getElem?_append_right (by simp)]
  simp [Nat.min_eq_left h]

/-- **Reset.** An update in range resets every record of strictly lower priority. -/
@[simp]
theorem getElem?_update_of_gt {s : List α} {u : Update α} (h : u.prio ≤ s.length) {i : ℕ}
    (hi : u.prio < i) : (update s u)[i]? = none := by
  rw [update_of_le h, List.getElem?_eq_none]
  simp
  omega

/-- An update at priority `e` keeps the first `n ≤ e` records. -/
@[simp]
theorem take_update_of_le (s : List α) (u : Update α) {n : ℕ} (h : n ≤ u.prio) :
    (update s u).take n = s.take n := by
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_take, List.getElem?_take]
  split_ifs with hi
  · exact getElem?_update_of_lt s u (Nat.lt_of_lt_of_le hi h)
  · rfl

/-! ### Runs -/

/-- The records after `n` stages: starting from `init`, at each stage `s < n` the update `sched s`
scheduled at that stage, if any, is applied. -/
def run (init : List α) (sched : ℕ → Option (Update α)) : ℕ → List α
  | 0 => init
  | n + 1 => match sched n with
    | none => run init sched n
    | some u => update (run init sched n) u

/-- A run starts at the initial records. -/
@[simp]
theorem run_zero (init : List α) (sched : ℕ → Option (Update α)) : run init sched 0 = init := (rfl)

/-- A run applies the update scheduled at stage `n`, if any, to the records after `n` stages. -/
theorem run_succ (init : List α) (sched : ℕ → Option (Update α)) (n : ℕ) :
    run init sched (n + 1) = (sched n).elim (run init sched n) (update (run init sched n)) := by
  rw [run]
  cases sched n <;> rfl

/-- A stage with no scheduled update leaves the records unchanged. -/
@[simp]
theorem run_succ_of_eq_none {init : List α} {sched : ℕ → Option (Update α)} {n : ℕ}
    (h : sched n = none) : run init sched (n + 1) = run init sched n := by
  rw [run, h]

/-- A stage with a scheduled update applies it. -/
@[simp]
theorem run_succ_of_eq_some {init : List α} {sched : ℕ → Option (Update α)} {n : ℕ}
    {u : Update α} (h : sched n = some u) :
    run init sched (n + 1) = update (run init sched n) u := by
  rw [run, h]

/-! ### Attention and stabilization

A priority schedule `action : ℕ → Option ℕ` records which requirement, if any, receives attention
at each stage. The update scheduled at stage `s` has been applied in the records `run init sched
(s + 1)`, so attention is counted by these run indices `s + 1`. A schedule of updates gives the
priority schedule `fun s => (sched s).map Update.prio`. -/

/-- The run indices `s + 1` after which an update of priority `e`, scheduled at stage `s`, has
been applied. -/
def attentionStages (action : ℕ → Option ℕ) (e : ℕ) : Set ℕ :=
  {t | ∃ s, t = s + 1 ∧ action s = some e}

/-- Membership in `attentionStages`. -/
@[simp]
theorem mem_attentionStages {action : ℕ → Option ℕ} {e t : ℕ} :
    t ∈ attentionStages action e ↔ ∃ s, t = s + 1 ∧ action s = some e :=
  Iff.rfl

/-- **Priority induction.** If each requirement receives attention finitely often whenever every
higher-priority requirement does, then every requirement receives attention finitely often. -/
theorem all_attention_finite_of_local (action : ℕ → Option ℕ)
    (hlocal : ∀ e, (∀ i, i < e → (attentionStages action i).Finite) →
      (attentionStages action e).Finite) (e : ℕ) :
    (attentionStages action e).Finite := by
  induction e using Nat.strong_induction_on with
  | _ e ih => exact hlocal e ih

/-- If requirements `0, …, e` each receive attention finitely often, then from some stage on every
requirement receiving attention has priority beyond `e`. -/
theorem exists_forall_lt_of_finite {action : ℕ → Option ℕ} {e : ℕ}
    (h : ∀ i, i ≤ e → (attentionStages action i).Finite) :
    ∃ N, ∀ s, N ≤ s → ∀ i, action s = some i → e < i := by
  have hfin : (⋃ i ∈ Set.Iic e, attentionStages action i).Finite :=
    (Set.finite_Iic e).biUnion fun i hi => h i hi
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B, fun s hs i hi => Nat.lt_of_not_le fun hle => ?_⟩
  have hmem : s + 1 ∈ ⋃ i ∈ Set.Iic e, attentionStages action i :=
    Set.mem_biUnion (x := i) hle ⟨s, rfl, hi⟩
  have := hB hmem
  omega

/-- From a stage after which only updates of priority beyond `e` are scheduled, the record at
position `e` never changes. -/
theorem getElem?_run_eq_of_forall_lt_prio {init : List α} {sched : ℕ → Option (Update α)}
    {e N : ℕ} (h : ∀ s, N ≤ s → ∀ u, sched s = some u → e < u.prio) {n : ℕ} (hn : N ≤ n) :
    (run init sched n)[e]? = (run init sched N)[e]? := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rcases hu : sched n with - | u
    · rw [run_succ_of_eq_none hu, ih]
    · rw [run_succ_of_eq_some hu, getElem?_update_of_lt _ _ (h n hn u hu), ih]

/-- **Stabilization of one record.** If requirements `0, …, e` each receive attention finitely
often, then the record at position `e` eventually stops changing. -/
theorem exists_forall_getElem?_run_eq_of_finite {init : List α} {sched : ℕ → Option (Update α)}
    {e : ℕ} (h : ∀ i, i ≤ e → (attentionStages (fun s => (sched s).map Update.prio) i).Finite) :
    ∃ N, ∀ n, N ≤ n → (run init sched n)[e]? = (run init sched N)[e]? := by
  obtain ⟨N, hN⟩ := exists_forall_lt_of_finite h
  exact ⟨N, fun n hn => getElem?_run_eq_of_forall_lt_prio
    (fun s hs u hu => hN s hs u.prio (by simp [hu])) hn⟩

/-- **Stabilization.** If each requirement receives attention finitely often whenever every
higher-priority requirement does, then every record eventually stops changing. -/
theorem exists_forall_getElem?_run_eq_of_local (init : List α) (sched : ℕ → Option (Update α))
    (hlocal : ∀ e, (∀ i, i < e → (attentionStages (fun s => (sched s).map Update.prio) i).Finite) →
      (attentionStages (fun s => (sched s).map Update.prio) e).Finite) (e : ℕ) :
    ∃ N, ∀ n, N ≤ n → (run init sched n)[e]? = (run init sched N)[e]? :=
  exists_forall_getElem?_run_eq_of_finite fun i _ => all_attention_finite_of_local _ hlocal i

end Priority

end TauCeti
