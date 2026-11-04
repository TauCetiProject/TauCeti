/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Code
public import TauCeti.Computability.Enumeration.Domain
public import TauCeti.Computability.Primrec.Pairing
public import TauCeti.Computability.Priority.Initialization
public import TauCeti.Computability.SingleOracle.Stage
import TauCeti.Computability.Primrec.Bitwise
import Mathlib.Data.List.MinMax

/-!
# The stage machine of the original Friedberg–Muchnik construction

This file constructs the finite-stage state machine of the original Friedberg–Muchnik theorem
[S, VII.2.1], building two c.e. sets `A = friedbergMuchnikSetA` and `B = friedbergMuchnikSetB`
against the interleaved negative requirements

* `R_{2e} : A ≠ Φ_e^B` (priority `k = 2e`, enumerating into `A` and monitoring `B`);
* `R_{2e+1} : B ≠ Φ_e^A` (priority `k = 2e + 1`, enumerating into `B` and monitoring `A`).

At each stage `s`, the finite state `state s` stores the finite sets `A_s` and `B_s`, an active
prefix of `(witness, restraint)` records, and a freshness floor `floor`. Any priority `j` beyond
the active prefix defaults to the column witness `j.leastInPairColumn floor` in `j.pairColumn` and
the inactive restraint `none`. Theorem `witness_restraint_eq_soareMarkers` proves that this finite
representation agrees at every stage and priority with Soare's infinite sequence of markers.

Requirement `k` **requires attention** at stage `s` when its witness `w = witness k s` has not yet
entered `stage (side k) s` and the normalized stage computation `Φ_{k / 2, s}` against the
opposite set `stage (monitoredSide k) s` halts at `w` with output `0`. The least eligible `k`
enumerates `w` into `side k`, leaves `monitoredSide k` unchanged, activates restraint `some d.use`
at priority `k`, preserves higher-priority records (`j < k`), and resets all lower-priority
requirements (`j > k`) to fresh column witnesses strictly exceeding `s`, `d.use`, all current
members of `A_{s+1} ∪ B_{s+1}`, and all active higher-priority restraints and witnesses.

## Main definitions

* `TauCeti.FriedbergMuchnik.side`, `TauCeti.FriedbergMuchnik.monitoredSide`: the enumerated side
  (`false` for `A`, `true` for `B`) and opposite monitored side of priority `k`.
* `TauCeti.FriedbergMuchnik.State`, `TauCeti.FriedbergMuchnik.step`,
  `TauCeti.FriedbergMuchnik.state`: the finite state and deterministic stage transition.
* `TauCeti.FriedbergMuchnik.RequiresAttention`, `TauCeti.FriedbergMuchnik.attention`,
  `TauCeti.FriedbergMuchnik.action`: eligibility and least-priority selection at stage `s`.
* `TauCeti.FriedbergMuchnik.stage`, `TauCeti.FriedbergMuchnik.witness`,
  `TauCeti.FriedbergMuchnik.restraint`: finite stage sets, column witnesses, and `Option ℕ`
  restraints.
* `TauCeti.FriedbergMuchnik.soareMarkers`: Soare's infinite marker recurrence, proved equal to
  `(witness j s, restraint j s)` at all `s, j`.
* `TauCeti.FriedbergMuchnik.appointmentStages`, `TauCeti.FriedbergMuchnik.enumeratedBy`: witness
  appointment/reappointment stages (disjoint from `attentionStages`) and numbers enumerated by `k`.
* `TauCeti.friedbergMuchnikSetA`, `TauCeti.friedbergMuchnikSetB`,
  `TauCeti.FriedbergMuchnik.code`: the two c.e. limit sets and their `Nat.Partrec.Code` indices.

## References

* R. M. Friedberg, *Two recursively enumerable sets of incomparable degrees of unsolvability*,
  Proc. Nat. Acad. Sci. U.S.A. **43** (1957), 236–238.
* A. A. Muchnik, *On the unsolvability of the problem of reducibility in the theory of algorithms*,
  Dokl. Akad. Nauk SSSR **108** (1956), 194–197.
* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.2.1.
-/

public section

open Denumerable TauCeti.Enumeration TauCeti.Priority

namespace TauCeti

namespace FriedbergMuchnik

open Oracle.Single

/-- Side enumerated by requirement `k`: `false` (`A`) for even `k = 2e`, `true` (`B`) for odd
`k = 2e + 1`. -/
def side (k : ℕ) : Bool :=
  k.bodd

/-- Side monitored and protected by requirement `k`: the opposite side `!k.bodd`. -/
def monitoredSide (k : ℕ) : Bool :=
  !k.bodd

/-- Even priorities `2 * e` enumerate into `false` (`A`). -/
@[simp]
theorem side_two_mul (e : ℕ) : side (2 * e) = false := by
  simp [side, Nat.bodd_mul]

/-- Odd priorities `2 * e + 1` enumerate into `true` (`B`). -/
@[simp]
theorem side_two_mul_add_one (e : ℕ) : side (2 * e + 1) = true := by
  simp [side, Nat.bodd_mul]

/-- The monitored side is the negation of the enumerated side. -/
theorem monitoredSide_eq_not_side (k : ℕ) : monitoredSide k = !side k :=
  (rfl)

/-- Even priorities `2 * e` monitor `true` (`B`). -/
@[simp]
theorem monitoredSide_two_mul (e : ℕ) : monitoredSide (2 * e) = true := by
  simp [monitoredSide, Nat.bodd_mul]

/-- Odd priorities `2 * e + 1` monitor `false` (`A`). -/
@[simp]
theorem monitoredSide_two_mul_add_one (e : ℕ) : monitoredSide (2 * e + 1) = false := by
  simp [monitoredSide, Nat.bodd_mul]

/-- A requirement never monitors the side it enumerates into. -/
theorem monitoredSide_ne_side (k : ℕ) : monitoredSide k ≠ side k := by
  cases h : side k <;> simp [monitoredSide_eq_not_side, h]

/-! ### Finite active state and uniform column defaults -/

/-- The finite state at the end of a stage: current finite approximations `setA` and `setB`, active
`(witness, restraint)` records for priorities `< records.length`, and the freshness floor `floor`
for not-yet-activated or reset priorities. -/
@[ext]
structure State where
  /-- Current finite approximation to `A` (`false`). -/
  setA : Finset ℕ
  /-- Current finite approximation to `B` (`true`). -/
  setB : Finset ℕ
  /-- Active `(witness, restraint)` records indexed by priority. -/
  records : List (ℕ × Option ℕ)
  /-- Lower bound for default witness selection in `j.pairColumn` beyond `records.length`. -/
  floor : ℕ
  deriving DecidableEq

namespace State

/-- The initial empty state at stage `0`: empty sets, no active records, and floor `0`. -/
def init : State :=
  ⟨∅, ∅, [], 0⟩

/-- Select `setA` for `false` and `setB` for `true`. -/
def set (st : State) : Bool → Finset ℕ
  | false => st.setA
  | true => st.setB

/-- `st.set false` is `st.setA`. -/
@[simp]
theorem set_false (st : State) : st.set false = st.setA :=
  (rfl)

/-- `st.set true` is `st.setB`. -/
@[simp]
theorem set_true (st : State) : st.set true = st.setB :=
  (rfl)

/-- Witness of requirement `j` in state `st`: the recorded witness if `j < st.records.length`, and
otherwise the default fresh witness `j.leastInPairColumn st.floor`. -/
def witness (st : State) (j : ℕ) : ℕ :=
  ((st.records[j]?).map Prod.fst).getD (j.leastInPairColumn st.floor)

/-- Restraint of requirement `j` in state `st`: the recorded restraint if `j < st.records.length`,
and `none` (inactive) otherwise. -/
def restraint (st : State) (j : ℕ) : Option ℕ :=
  (st.records[j]?).bind Prod.snd

/-- Both approximations in `State.init` are empty. -/
@[simp]
theorem init_set (b : Bool) : init.set b = ∅ := by
  cases b <;> rfl

/-- In `State.init`, requirement `j` holds the initial witness `Nat.pair 0 j`. -/
@[simp]
theorem init_witness (j : ℕ) : init.witness j = Nat.pair 0 j := by
  simp [init, witness]

/-- In `State.init`, every restraint is inactive (`none`). -/
@[simp]
theorem init_restraint (j : ℕ) : init.restraint j = none :=
  (rfl)

/-- Equivalence between `State` and primitive-codable data, encoding `setA` and `setB` via
`Finset.equivBitIndices`. -/
def equivCode : State ≃ (ℕ × ℕ) × List (ℕ × Option ℕ) × ℕ where
  toFun st := ((Finset.equivBitIndices.symm st.setA, Finset.equivBitIndices.symm st.setB),
    st.records, st.floor)
  invFun c := ⟨Finset.equivBitIndices c.1.1, Finset.equivBitIndices c.1.2, c.2.1, c.2.2⟩
  left_inv st := by cases st; simp
  right_inv c := by rcases c with ⟨⟨_, _⟩, _, _⟩; simp

/-- Finite states are primitive codable via `State.equivCode`. -/
instance instPrimcodable : Primcodable State :=
  Primcodable.ofEquiv ((ℕ × ℕ) × List (ℕ × Option ℕ) × ℕ) equivCode

end State

/-! ### Stage evaluation, eligibility, and least-priority attention -/

/-- Normalized stage computation `Φ_{e, s}^D(x)` against the binary answers of a finite set `D`. -/
def stageRun (D : Finset ℕ) (s e x : ℕ) : Option Code.Halt :=
  Code.evalStage (fun z => some (if z ∈ D then 1 else 0)) s (ofNat Code e) x

/-- Unfolding `stageRun`. -/
theorem stageRun_def (D : Finset ℕ) (s e x : ℕ) :
    stageRun D s e x =
      Code.evalStage (fun z => some (if z ∈ D then 1 else 0)) s (ofNat Code e) x :=
  (rfl)

/-- `stageRun` agrees with `Code.evalStage` on `Code.setAnswers D`. -/
theorem stageRun_eq_evalStage_setAnswers (D : Finset ℕ) (s e x : ℕ) :
    stageRun D s e x = Code.evalStage (Code.setAnswers D) s (ofNat Code e) x := by
  rw [stageRun]
  congr 1
  ext z
  simp [Set.indicator_apply]

/-- Requirement `k` **requires attention** in state `st` at stage `s` with halting record `d` when
its witness `st.witness k` lies in `k.pairColumn` outside `st.set (side k)` and the opposite-side
stage computation `Φ_{k / 2, s}` halts at `st.witness k` with `d` and output `0`. -/
structure RequiresAttention (st : State) (s k : ℕ) (d : Code.Halt) : Prop where
  /-- The witness has not yet entered the enumerated side of `k`. -/
  witness_notMem : st.witness k ∉ st.set (side k)
  /-- The witness belongs to `k`'s column. -/
  witness_mem_pairColumn : st.witness k ∈ k.pairColumn
  /-- The opposite-oracle stage computation halts at the witness with record `d`. -/
  stageRun_eq_some : stageRun (st.set (monitoredSide k)) s (k / 2) (st.witness k) = some d
  /-- The stage computation outputs `0`. -/
  output_eq_zero : d.output = 0

/-- Unfolding `RequiresAttention` into its four clauses. -/
theorem requiresAttention_iff {st : State} {s k : ℕ} {d : Code.Halt} :
    RequiresAttention st s k d ↔
      st.witness k ∉ st.set (side k) ∧ st.witness k ∈ k.pairColumn ∧
        stageRun (st.set (monitoredSide k)) s (k / 2) (st.witness k) = some d ∧ d.output = 0 :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

/-- Any requirement requiring attention at stage `s` has priority `k < s`, since
`k ≤ st.witness k < s`. -/
theorem RequiresAttention.lt_stage {st : State} {s k : ℕ} {d : Code.Halt}
    (h : RequiresAttention st s k d) : k < s :=
  (Nat.le_of_mem_pairColumn h.witness_mem_pairColumn).trans_lt
    (Code.evalStage_input_lt h.stageRun_eq_some)

/-- At a fixed state, stage, and priority, the halting record witnessing `RequiresAttention` is
unique. -/
theorem RequiresAttention.unique {st : State} {s k : ℕ} {d d' : Code.Halt}
    (h : RequiresAttention st s k d) (h' : RequiresAttention st s k d') : d = d' :=
  Option.some.inj (h.stageRun_eq_some.symm.trans h'.stageRun_eq_some)

private def candRun (st : State) (s k : ℕ) : Option Code.Halt :=
  if st.witness k ∉ st.set (side k) ∧ st.witness k ∈ k.pairColumn then
    (stageRun (st.set (monitoredSide k)) s (k / 2) (st.witness k)).bind fun d =>
      if d.output = 0 then some d else none
  else none

private theorem candRun_eq_some_iff {st : State} {s k : ℕ} {d : Code.Halt} :
    candRun st s k = some d ↔ RequiresAttention st s k d := by
  rw [candRun, requiresAttention_iff]
  split_ifs with h
  · rcases h with ⟨hnot, hcol⟩
    simp only [hnot, not_false_eq_true, hcol, true_and, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨d', hd', h0⟩
      split_ifs at h0 with hd0
      obtain ⟨rfl⟩ := Option.some.inj h0
      exact ⟨hd', hd0⟩
    · rintro ⟨hd, hd0⟩
      exact ⟨d, hd, by simp [hd0]⟩
  · refine ⟨fun hnone => (by cases hnone), ?_⟩
    rintro ⟨hnot, hcol, -⟩
    exact absurd ⟨hnot, hcol⟩ h

/-- **Least-priority attention.** Search `k < s` for the least priority requiring attention and
return `(k, d)`. -/
def attention (st : State) (s : ℕ) : Option (ℕ × Code.Halt) :=
  ((List.range s).find? fun k => (candRun st s k).isSome).bind fun k =>
    (candRun st s k).map (k, ·)

/-- `attention st s = some (k, d)` holds exactly when `k` is the least priority requiring attention
at stage `s`, with halting record `d`. -/
theorem attention_eq_some_iff {st : State} {s k : ℕ} {d : Code.Halt} :
    attention st s = some (k, d) ↔
      RequiresAttention st s k d ∧ ∀ j < k, ∀ d', ¬RequiresAttention st s j d' := by
  simp only [attention, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq,
    List.find?_range_eq_some, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true,
    Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨k', ⟨-, -, hmin⟩, d', hd', rfl, rfl⟩
    refine ⟨candRun_eq_some_iff.mp hd', fun j hj d'' hj' => ?_⟩
    have hnone := hmin j hj
    rw [candRun_eq_some_iff.mpr hj'] at hnone
    cases hnone
  · rintro ⟨hk, hmin⟩
    have hck : candRun st s k = some d := candRun_eq_some_iff.mpr hk
    refine ⟨k, ⟨by simp [hck], hk.lt_stage, fun j hj => ?_⟩, d, hck, rfl, rfl⟩
    refine Option.eq_none_iff_forall_not_mem.mpr fun d' hd' => ?_
    exact hmin j hj d' (candRun_eq_some_iff.mp hd')

/-- `attention st s = none` holds exactly when no priority requires attention. -/
theorem attention_eq_none_iff {st : State} {s : ℕ} :
    attention st s = none ↔ ∀ k d, ¬RequiresAttention st s k d := by
  refine ⟨fun h k d hk => ?_, fun h => ?_⟩
  · have hck : candRun st s k = some d := candRun_eq_some_iff.mpr hk
    have his : ((List.range s).find? fun j => (candRun st s j).isSome).isSome :=
      List.find?_isSome.mpr ⟨k, List.mem_range.mpr hk.lt_stage, by simp [hck]⟩
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp his
    obtain ⟨hcj, -⟩ := List.find?_range_eq_some.mp hj
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp hcj
    simp [attention, hj, hd'] at h
  · rw [attention, Option.bind_eq_none_iff]
    intro k hk
    obtain ⟨hck, -⟩ := List.find?_range_eq_some.mp hk
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hck
    exact absurd (candRun_eq_some_iff.mp hd) (h k d)

/-- No requirement can receive attention at stage `0`. -/
@[simp]
theorem attention_zero (st : State) : attention st 0 = none := by
  simp [attention]

/-! ### Stage transition and semantic correspondence -/

/-- Freshness floor installed when requirement `k` acts with halting record `d` at stage `s`:
strictly exceeds `st.floor`, `s`, `d.use`, every member of `st.setA ∪ st.setB`, every witness of
priority `≤ k`, and every active restraint of priority `≤ k`. -/
def nextFloor (st : State) (s k : ℕ) (d : Code.Halt) : ℕ :=
  max (max st.floor (max s d.use) + 1)
    (max ((st.setA ∪ st.setB).sup (· + 1))
      (((List.range (k + 1)).map fun i =>
        max (st.witness i + 1) (((st.restraint i).map (· + 1)).getD 0)).foldr max 0))

/-- `nextFloor` strictly exceeds the previous floor `st.floor`. -/
theorem lt_nextFloor_floor (st : State) (s k : ℕ) (d : Code.Halt) :
    st.floor < nextFloor st s k d := by
  simp only [nextFloor]
  omega

/-- `nextFloor` strictly exceeds the current stage `s`. -/
theorem lt_nextFloor_stage (st : State) (s k : ℕ) (d : Code.Halt) :
    s < nextFloor st s k d := by
  simp only [nextFloor]
  omega

/-- `nextFloor` strictly exceeds the halting use `d.use`. -/
theorem lt_nextFloor_use (st : State) (s k : ℕ) (d : Code.Halt) :
    d.use < nextFloor st s k d := by
  simp only [nextFloor]
  omega

/-- `nextFloor` strictly exceeds every element already in `st.setA ∪ st.setB`. -/
theorem lt_nextFloor_of_mem_union {st : State} {s k x : ℕ} {d : Code.Halt}
    (hx : x ∈ st.setA ∪ st.setB) : x < nextFloor st s k d := by
  have hsup : x + 1 ≤ (st.setA ∪ st.setB).sup (· + 1) := Finset.le_sup (f := (· + 1)) hx
  have hle : (st.setA ∪ st.setB).sup (· + 1) ≤ nextFloor st s k d :=
    (le_max_left _ _).trans (le_max_right _ _)
  omega

/-- `nextFloor` strictly exceeds `st.witness i` for every priority `i ≤ k`. -/
theorem witness_lt_nextFloor {st : State} {s k i : ℕ} {d : Code.Halt} (hi : i ≤ k) :
    st.witness i < nextFloor st s k d := by
  let f : ℕ → ℕ := fun j => max (st.witness j + 1) (((st.restraint j).map (· + 1)).getD 0)
  have hmem : f i ∈ (List.range (k + 1)).map f :=
    List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hi))
  have h1 : st.witness i + 1 ≤ f i := le_max_left _ _
  have h2 : st.witness i + 1 ≤ ((List.range (k + 1)).map f).foldr max 0 :=
    List.le_max_of_le' 0 hmem h1
  have h3 : ((List.range (k + 1)).map f).foldr max 0 ≤ nextFloor st s k d :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

/-- `nextFloor` strictly exceeds any active restraint `st.restraint i = some b` with `i ≤ k`. -/
theorem restraint_lt_nextFloor {st : State} {s k i b : ℕ} {d : Code.Halt} (hi : i ≤ k)
    (hb : st.restraint i = some b) : b < nextFloor st s k d := by
  let f : ℕ → ℕ := fun j => max (st.witness j + 1) (((st.restraint j).map (· + 1)).getD 0)
  have hmem : f i ∈ (List.range (k + 1)).map f :=
    List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hi))
  have h1 : b + 1 ≤ f i := by
    have : ((st.restraint i).map (· + 1)).getD 0 = b + 1 := by simp [hb]
    exact this ▸ le_max_right _ _
  have h2 : b + 1 ≤ ((List.range (k + 1)).map f).foldr max 0 :=
    List.le_max_of_le' 0 hmem h1
  have h3 : ((List.range (k + 1)).map f).foldr max 0 ≤ nextFloor st s k d :=
    (le_max_right _ _).trans (le_max_right _ _)
  omega

private def applyAction (st : State) (s k : ℕ) (d : Code.Halt) : State where
  setA := if side k = false then insert (st.witness k) st.setA else st.setA
  setB := if side k = true then insert (st.witness k) st.setB else st.setB
  records := (List.range k).map (fun i => (st.witness i, st.restraint i)) ++
    [(st.witness k, some d.use)]
  floor := nextFloor st s k d

/-- One step of the Friedberg–Muchnik stage machine. -/
def step (st : State) (s : ℕ) : State :=
  match attention st s with
  | none => st
  | some p => applyAction st s p.1 p.2

/-- The finite state at the end of stage `s`. -/
def state : ℕ → State
  | 0 => State.init
  | s + 1 => step (state s) s

/-- The priority receiving attention at stage `s`, if any. -/
def action (s : ℕ) : Option ℕ :=
  (attention (state s) s).map Prod.fst

/-- Finite stage `s` of side `b` (`A_s` for `false`, `B_s` for `true`). -/
def stage (b : Bool) (s : ℕ) : Finset ℕ :=
  (state s).set b

/-- Witness `x_j^s` of requirement `j` at stage `s`. -/
def witness (j s : ℕ) : ℕ :=
  (state s).witness j

/-- Restraint `r_j^s` of requirement `j` at stage `s` (`none` when inactive). -/
def restraint (j s : ℕ) : Option ℕ :=
  (state s).restraint j

/-- Stage `0` starts in `State.init`. -/
@[simp]
theorem state_zero : state 0 = State.init :=
  (rfl)

/-- Both stage approximations start empty at stage `0`. -/
@[simp]
theorem stage_zero (b : Bool) : stage b 0 = ∅ := by
  simp [stage]

/-- At stage `0`, requirement `j` holds the initial column witness `Nat.pair 0 j`. -/
@[simp]
theorem witness_zero (j : ℕ) : witness j 0 = Nat.pair 0 j := by
  simp [witness]

/-- At stage `0`, every restraint is inactive (`none`). -/
@[simp]
theorem restraint_zero (j : ℕ) : restraint j 0 = none :=
  (rfl)

/-- No requirement acts at stage `0`. -/
@[simp]
theorem action_zero : action 0 = none := by
  simp [action]

/-- `action s = some k` iff `attention (state s) s = some (k, d)` for some halting record `d`. -/
theorem action_eq_some_iff {s k : ℕ} :
    action s = some k ↔ ∃ d, attention (state s) s = some (k, d) := by
  simp [action]

/-- `action s = none` iff `attention (state s) s = none`. -/
theorem action_eq_none_iff {s : ℕ} :
    action s = none ↔ attention (state s) s = none := by
  simp [action]

/-! ### Action, locality, initialization, and opposite-oracle protection equations -/

private theorem state_succ_of_attention_eq_none {s : ℕ} (h : attention (state s) s = none) :
    state (s + 1) = state s := by
  simp [state, step, h]

private theorem state_succ_of_attention_eq_some {s k : ℕ} {d : Code.Halt}
    (h : attention (state s) s = some (k, d)) :
    state (s + 1) = applyAction (state s) s k d := by
  simp [state, step, h]

/-- If no requirement receives attention at stage `s`, `stage b` is unchanged. -/
theorem stage_succ_of_attention_eq_none {b : Bool} {s : ℕ} (h : attention (state s) s = none) :
    stage b (s + 1) = stage b s := by
  rw [stage, state_succ_of_attention_eq_none h, stage]

/-- An action of `k` enumerates `witness k s` into `stage (side k)`. -/
theorem stage_side_succ_of_attention_eq_some {s k : ℕ} {d : Code.Halt}
    (h : attention (state s) s = some (k, d)) :
    stage (side k) (s + 1) = insert (witness k s) (stage (side k) s) := by
  rw [stage, state_succ_of_attention_eq_some h]
  cases hside : side k <;> simp [applyAction, State.set, stage, witness, hside]

/-- **Protection of the opposite oracle at the acting stage.** An action of `k` leaves
`stage (monitoredSide k)` unchanged. -/
theorem stage_monitoredSide_succ_of_attention_eq_some {s k : ℕ} {d : Code.Halt}
    (h : attention (state s) s = some (k, d)) :
    stage (monitoredSide k) (s + 1) = stage (monitoredSide k) s := by
  rw [stage, state_succ_of_attention_eq_some h]
  cases hside : side k <;> simp [applyAction, State.set, stage, monitoredSide_eq_not_side, hside]

/-- If no requirement receives attention at stage `s`, `witness j` is unchanged. -/
theorem witness_succ_of_attention_eq_none {j s : ℕ} (h : attention (state s) s = none) :
    witness j (s + 1) = witness j s := by
  rw [witness, state_succ_of_attention_eq_none h, witness]

/-- If no requirement receives attention at stage `s`, `restraint j` is unchanged. -/
theorem restraint_succ_of_attention_eq_none {j s : ℕ} (h : attention (state s) s = none) :
    restraint j (s + 1) = restraint j s := by
  rw [restraint, state_succ_of_attention_eq_none h, restraint]

private theorem applyAction_records_getElem?_of_lt {st : State} {s k j : ℕ} {d : Code.Halt}
    (hjk : j < k) :
    (applyAction st s k d).records[j]? = some (st.witness j, st.restraint j) := by
  simp only [applyAction]
  rw [List.getElem?_append_left (by simp [hjk])]
  simp [hjk]

private theorem applyAction_records_getElem?_self {st : State} {s k : ℕ} {d : Code.Halt} :
    (applyAction st s k d).records[k]? = some (st.witness k, some d.use) := by
  simp [applyAction]

private theorem applyAction_records_getElem?_of_gt {st : State} {s k j : ℕ} {d : Code.Halt}
    (hkj : k < j) :
    (applyAction st s k d).records[j]? = none := by
  rw [List.getElem?_eq_none]
  simp [applyAction]
  omega

/-- **Higher-priority witness locality.** An action at priority `k` leaves `witness j` unchanged for
every `j ≤ k`. -/
theorem witness_succ_of_attention_eq_some_of_le {j s k : ℕ} {d : Code.Halt}
    (h : attention (state s) s = some (k, d)) (hjk : j ≤ k) :
    witness j (s + 1) = witness j s := by
  rw [witness, state_succ_of_attention_eq_some h, State.witness]
  rcases lt_or_eq_of_le hjk with hlt | rfl
  · rw [applyAction_records_getElem?_of_lt hlt]; rfl
  · rw [applyAction_records_getElem?_self]; rfl

/-- **Higher-priority restraint locality.** An action at priority `k` leaves `restraint j` unchanged
for every `j < k`. -/
theorem restraint_succ_of_attention_eq_some_of_lt {j s k : ℕ} {d : Code.Halt}
    (h : attention (state s) s = some (k, d)) (hjk : j < k) :
    restraint j (s + 1) = restraint j s := by
  rw [restraint, state_succ_of_attention_eq_some h, State.restraint,
    applyAction_records_getElem?_of_lt hjk]
  rfl

/-- **Self restraint activation.** When `k` acts with halting record `d`, `restraint k (s + 1)`
becomes `some d.use`. -/
theorem restraint_succ_of_attention_eq_some_self {s k : ℕ} {d : Code.Halt}
    (h : attention (state s) s = some (k, d)) :
    restraint k (s + 1) = some d.use := by
  rw [restraint, state_succ_of_attention_eq_some h, State.restraint,
    applyAction_records_getElem?_self]
  rfl

/-- **Lower-priority witness initialization.** When `k` acts at stage `s`, every `j > k` is
reappointed the fresh column witness `j.leastInPairColumn (nextFloor (state s) s k d)`. -/
theorem witness_succ_of_attention_eq_some_of_gt {j s k : ℕ} {d : Code.Halt}
    (h : attention (state s) s = some (k, d)) (hkj : k < j) :
    witness j (s + 1) = j.leastInPairColumn (nextFloor (state s) s k d) := by
  rw [witness, state_succ_of_attention_eq_some h, State.witness,
    applyAction_records_getElem?_of_gt hkj]
  rfl

/-- **Lower-priority restraint initialization.** When `k` acts at stage `s`, every `j > k` has its
restraint reset to `none`. -/
theorem restraint_succ_of_attention_eq_some_of_gt {j s k : ℕ} {d : Code.Halt}
    (h : attention (state s) s = some (k, d)) (hkj : k < j) :
    restraint j (s + 1) = none := by
  rw [restraint, state_succ_of_attention_eq_some h, State.restraint,
    applyAction_records_getElem?_of_gt hkj]
  rfl

/-- **Soare's infinite marker recurrence.** At stage `0`, every requirement `j` holds
`(Nat.pair 0 j, none)`; at stage `s + 1`, higher-priority markers are kept, the acting marker
activates `some d.use`, and lower-priority markers are reset to fresh column witnesses with
`none`. -/
def soareMarkers : ℕ → ℕ → ℕ × Option ℕ
  | 0, j => (Nat.pair 0 j, none)
  | s + 1, j =>
    match attention (state s) s with
    | none => soareMarkers s j
    | some p =>
      if j < p.1 then soareMarkers s j
      else if j = p.1 then ((soareMarkers s j).1, some p.2.use)
      else (j.leastInPairColumn (nextFloor (state s) s p.1 p.2), none)

/-- **Semantic correspondence.** The finite active-prefix state with uniform column defaults agrees
with Soare's infinite marker sequence `soareMarkers` at every stage and priority. -/
theorem witness_restraint_eq_soareMarkers (s j : ℕ) :
    (witness j s, restraint j s) = soareMarkers s j := by
  induction s generalizing j with
  | zero => simp [soareMarkers]
  | succ s ih =>
    rcases h : attention (state s) s with _ | ⟨k, d⟩
    · simp [soareMarkers, h, witness_succ_of_attention_eq_none h,
        restraint_succ_of_attention_eq_none h, ih j]
    · simp only [soareMarkers, h]
      rcases lt_trichotomy j k with hlt | rfl | hgt
      · simp [hlt, witness_succ_of_attention_eq_some_of_le h hlt.le,
          restraint_succ_of_attention_eq_some_of_lt h hlt, ih j]
      · have hw : witness j s = (soareMarkers s j).1 := congrArg Prod.fst (ih j)
        simp [witness_succ_of_attention_eq_some_of_le h le_rfl,
          restraint_succ_of_attention_eq_some_self h, hw]
      · have hnotlt : ¬j < k := not_lt.mpr hgt.le
        have hne : j ≠ k := hgt.ne'
        simp [hnotlt, hne, witness_succ_of_attention_eq_some_of_gt h hgt,
          restraint_succ_of_attention_eq_some_of_gt h hgt]

/-! ### Monotonicity, witness ownership, and appointment vs. attention -/

/-- Both stage sequences `stage false` and `stage true` are monotone. -/
theorem monotone_stage (b : Bool) : Monotone (stage b) := by
  refine monotone_nat_of_le_succ fun s => ?_
  rcases h : attention (state s) s with _ | ⟨k, d⟩
  · rw [stage_succ_of_attention_eq_none h]
  · by_cases hb : b = side k
    · subst hb
      rw [stage_side_succ_of_attention_eq_some h]
      exact Finset.subset_insert _ _
    · have hb' : b = monitoredSide k := by
        cases b <;> cases hside : side k <;> simp_all [monitoredSide_eq_not_side]
      rw [hb', stage_monitoredSide_succ_of_attention_eq_some h]

/-- Every witness `witness j s` belongs to `j`'s pairing column `j.pairColumn`. -/
theorem witness_mem_pairColumn (j s : ℕ) : witness j s ∈ j.pairColumn := by
  induction s generalizing j with
  | zero => simp [witness_zero]
  | succ s ih =>
    rcases h : attention (state s) s with _ | ⟨k, d⟩
    · rw [witness_succ_of_attention_eq_none h]
      exact ih j
    · rcases le_or_gt j k with hle | hgt
      · rw [witness_succ_of_attention_eq_some_of_le h hle]
        exact ih j
      · rw [witness_succ_of_attention_eq_some_of_gt h hgt]
        exact Nat.leastInPairColumn_mem_pairColumn j _

/-- The second `Nat.unpair` coordinate of `witness j s` is `j`. -/
@[simp]
theorem unpair_witness_snd (j s : ℕ) : (witness j s).unpair.2 = j :=
  Nat.mem_pairColumn.mp (witness_mem_pairColumn j s)

/-- On a reachable state `state s`, `RequiresAttention` reduces to unenumerated witness + halting
opposite-side run with output `0`. -/
theorem requiresAttention_state_iff {s k : ℕ} {d : Code.Halt} :
    RequiresAttention (state s) s k d ↔
      witness k s ∉ stage (side k) s ∧
        stageRun (stage (monitoredSide k) s) s (k / 2) (witness k s) = some d ∧ d.output = 0 := by
  rw [requiresAttention_iff, ← witness, ← stage, ← stage]
  exact and_congr_right fun _ => and_iff_right (witness_mem_pairColumn k s)

private theorem witness_lt_floor_of_lt_length (s : ℕ) :
    ∀ j < (state s).records.length, witness j s < (state s).floor := by
  induction s with
  | zero => simp [State.init]
  | succ s ih =>
    rcases h : attention (state s) s with _ | ⟨k, d⟩
    · rw [state_succ_of_attention_eq_none h]
      intro j hj
      rw [witness_succ_of_attention_eq_none h]
      exact ih j hj
    · intro j hj
      have hlen : (state (s + 1)).records.length = k + 1 := by
        simp [state_succ_of_attention_eq_some h, applyAction]
      have hjk : j ≤ k := by omega
      rw [witness_succ_of_attention_eq_some_of_le h hjk, state_succ_of_attention_eq_some h]
      exact witness_lt_nextFloor hjk

/-- For each requirement `j`, the witness sequence `s ↦ witness j s` is monotone. -/
theorem monotone_witness (j : ℕ) : Monotone (witness j) := by
  refine monotone_nat_of_le_succ fun s => ?_
  rcases h : attention (state s) s with _ | ⟨k, d⟩
  · rw [witness_succ_of_attention_eq_none h]
  · rcases le_or_gt j k with hle | hgt
    · rw [witness_succ_of_attention_eq_some_of_le h hle]
    · rw [witness_succ_of_attention_eq_some_of_gt h hgt]
      rcases lt_or_ge j (state s).records.length with hjlen | hjlen
      · exact ((witness_lt_floor_of_lt_length s j hjlen).trans
          (lt_nextFloor_floor (state s) s k d)).le.trans (Nat.le_leastInPairColumn j _)
      · have hdef : witness j s = j.leastInPairColumn (state s).floor := by
          simp [witness, State.witness, List.getElem?_eq_none hjlen]
        rw [hdef]
        exact Nat.monotone_leastInPairColumn j (lt_nextFloor_floor (state s) s k d).le

/-- Stages at which requirement `j` is appointed or reappointed a witness: stage `0` together with
its initialization stages `initializationStages action j`. -/
def appointmentStages (j : ℕ) : Set ℕ :=
  insert 0 (initializationStages action j)

/-- Stage `0` is an appointment stage for every requirement. -/
@[simp]
theorem zero_mem_appointmentStages (j : ℕ) : 0 ∈ appointmentStages j :=
  Set.mem_insert 0 _

/-- A positive stage `s + 1` is an appointment stage for `j` iff it initializes `j`. -/
@[simp]
theorem succ_mem_appointmentStages {j s : ℕ} :
    s + 1 ∈ appointmentStages j ↔ s + 1 ∈ initializationStages action j := by
  simp [appointmentStages]

/-- **Appointment and attention stages are disjoint:** appointing a witness at stage `0` or upon
higher-priority initialization never coincides with `j` acting to enumerate its witness. -/
theorem disjoint_appointmentStages_attentionStages (j : ℕ) :
    Disjoint (appointmentStages j) (attentionStages action j) := by
  rw [appointmentStages, Set.disjoint_insert_left]
  refine ⟨fun h0 => ?_, disjoint_initializationStages_attentionStages action j⟩
  obtain ⟨s, hs, -⟩ := mem_attentionStages.mp h0
  omega

/-- Outside `appointmentStages j`, `witness j` does not change in `s ↦ s + 1`. -/
theorem witness_succ_eq_of_notMem_appointmentStages {j s : ℕ}
    (h : s + 1 ∉ appointmentStages j) : witness j (s + 1) = witness j s := by
  rcases hatt : attention (state s) s with _ | ⟨k, d⟩
  · exact witness_succ_of_attention_eq_none hatt
  · refine witness_succ_of_attention_eq_some_of_le hatt (not_lt.mp fun hkj => h ?_)
    exact succ_mem_appointmentStages.mpr
      (succ_mem_initializationStages.mpr ⟨k, hkj, by simp [action, hatt]⟩)

/-- `nextFloor (state s) s k d` strictly exceeds every element of `stage b s`. -/
theorem lt_nextFloor_of_mem_stage {b : Bool} {s k x : ℕ} {d : Code.Halt}
    (hx : x ∈ stage b s) : x < nextFloor (state s) s k d := by
  refine lt_nextFloor_of_mem_union ?_
  cases b <;> simp_all [stage]

/-- `nextFloor (state s) s k d` strictly exceeds any active restraint `restraint i s = some b` with
`i ≤ k`. -/
theorem lt_nextFloor_of_restraint_eq_some {s k i b : ℕ} {d : Code.Halt} (hi : i ≤ k)
    (hb : restraint i s = some b) : b < nextFloor (state s) s k d :=
  restraint_lt_nextFloor hi hb

/-- At every reappointment stage `s + 1 ∈ initializationStages action j`, the new witness of `j`
lies outside both `stage false (s + 1)` and `stage true (s + 1)`. -/
theorem witness_notMem_stage_of_mem_initializationStages {j s : ℕ} (b : Bool)
    (h : s + 1 ∈ initializationStages action j) :
    witness j (s + 1) ∉ stage b (s + 1) := by
  obtain ⟨k, hkj, hk⟩ := succ_mem_initializationStages.mp h
  obtain ⟨d, hd⟩ := action_eq_some_iff.mp hk
  rw [witness_succ_of_attention_eq_some_of_gt hd hkj]
  intro hmem
  have hge : nextFloor (state s) s k d ≤ j.leastInPairColumn (nextFloor (state s) s k d) :=
    Nat.le_leastInPairColumn j _
  have hlt : j.leastInPairColumn (nextFloor (state s) s k d) < nextFloor (state s) s k d := by
    by_cases hb : b = side k
    · subst hb
      rw [stage_side_succ_of_attention_eq_some hd, Finset.mem_insert] at hmem
      rcases hmem with hwk | hmem'
      · exact hwk ▸ witness_lt_nextFloor le_rfl
      · exact lt_nextFloor_of_mem_stage hmem'
    · have hb' : b = monitoredSide k := by
        cases b <;> cases hside : side k <;> simp_all [monitoredSide_eq_not_side]
      rw [hb', stage_monitoredSide_succ_of_attention_eq_some hd] at hmem
      exact lt_nextFloor_of_mem_stage hmem
  omega

/-- Numbers enumerated by requirement `k` across all stages. -/
def enumeratedBy (k : ℕ) : Set ℕ :=
  {x | ∃ s, action s = some k ∧ witness k s = x}

/-- Membership in `enumeratedBy k`. -/
@[simp]
theorem mem_enumeratedBy {k x : ℕ} :
    x ∈ enumeratedBy k ↔ ∃ s, action s = some k ∧ witness k s = x :=
  Iff.rfl

/-- Every number enumerated by requirement `k` belongs to `k.pairColumn`. -/
theorem enumeratedBy_subset_pairColumn (k : ℕ) : enumeratedBy k ⊆ k.pairColumn := by
  rintro _ ⟨s, -, rfl⟩
  exact witness_mem_pairColumn k s

/-- Distinct requirements enumerate disjoint sets of witnesses. -/
theorem disjoint_enumeratedBy {j k : ℕ} (h : j ≠ k) :
    Disjoint (enumeratedBy j) (enumeratedBy k) :=
  (Nat.disjoint_pairColumn h).mono (enumeratedBy_subset_pairColumn j)
    (enumeratedBy_subset_pairColumn k)

/-- **Fresh entries.** A number `x` enters `stage b` in `s ↦ s + 1` if and only if the requirement
`k` acting at stage `s` has `side k = b` and `witness k s = x`. -/
theorem mem_fresh_stage {b : Bool} {s x : ℕ} :
    x ∈ fresh (stage b) s ↔ ∃ k, side k = b ∧ action s = some k ∧ witness k s = x := by
  rw [mem_fresh]
  constructor
  · rintro ⟨hx1, hx0⟩
    rcases h : attention (state s) s with _ | ⟨k, d⟩
    · rw [stage_succ_of_attention_eq_none h] at hx1
      exact absurd hx1 hx0
    · by_cases hb : side k = b
      · subst hb
        rw [stage_side_succ_of_attention_eq_some h, Finset.mem_insert] at hx1
        exact ⟨k, rfl, by simp [action, h], (hx1.resolve_right hx0).symm⟩
      · have hb' : b = monitoredSide k := by
          cases b <;> cases hside : side k <;> simp_all [monitoredSide_eq_not_side]
        subst hb'
        rw [stage_monitoredSide_succ_of_attention_eq_some h] at hx1
        exact absurd hx1 hx0
  · rintro ⟨k, rfl, hk, rfl⟩
    obtain ⟨d, hd⟩ := action_eq_some_iff.mp hk
    have hnot : witness k s ∉ stage (side k) s := (attention_eq_some_iff.mp hd).1.witness_notMem
    rw [stage_side_succ_of_attention_eq_some hd]
    exact ⟨Finset.mem_insert_self _ _, hnot⟩

/-! ### Limit sets, disjointness, and effectivity -/

/-- The limit set of side `b`: `A` for `false` and `B` for `true`. -/
def set (b : Bool) : Set ℕ :=
  stageLimit (stage b)

end FriedbergMuchnik

/-- The first c.e. set `A` constructed by the original Friedberg–Muchnik theorem. -/
def friedbergMuchnikSetA : Set ℕ :=
  FriedbergMuchnik.set false

/-- The second c.e. set `B` constructed by the original Friedberg–Muchnik theorem. -/
def friedbergMuchnikSetB : Set ℕ :=
  FriedbergMuchnik.set true

namespace FriedbergMuchnik

open Oracle.Single

/-- `set b` is the stage limit `stageLimit (stage b)`. -/
theorem set_eq_stageLimit (b : Bool) : set b = stageLimit (stage b) :=
  (rfl)

/-- `set false` is `friedbergMuchnikSetA`. -/
theorem set_false_eq : set false = friedbergMuchnikSetA :=
  (rfl)

/-- `set true` is `friedbergMuchnikSetB`. -/
theorem set_true_eq : set true = friedbergMuchnikSetB :=
  (rfl)

/-- Membership in `set b` is eventual membership in `stage b`. -/
theorem mem_set_iff_exists_stage {b : Bool} {x : ℕ} : x ∈ set b ↔ ∃ s, x ∈ stage b s :=
  mem_stageLimit

/-- **Witness ownership.** A number belongs to `set b` if and only if it is enumerated by the unique
requirement `k = x.unpair.2`, and that requirement has `side k = b`. -/
theorem mem_set_iff_enumeratedBy {b : Bool} {x : ℕ} :
    x ∈ set b ↔ ∃ k, side k = b ∧ x ∈ enumeratedBy k := by
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := exists_mem_fresh_of_mem_stageLimit hx (by simp)
    obtain ⟨k, hb, hk, hw⟩ := mem_fresh_stage.mp hs
    exact ⟨k, hb, s, hk, hw⟩
  · rintro ⟨k, rfl, s, hk, rfl⟩
    exact mem_stageLimit_of_mem_fresh (mem_fresh_stage.mpr ⟨k, rfl, hk, rfl⟩)

/-- Every element `x ∈ set b` belongs to the column of a requirement with `side = b`, so
`side x.unpair.2 = b`. -/
theorem side_unpair_snd_of_mem_set {b : Bool} {x : ℕ} (hx : x ∈ set b) :
    side x.unpair.2 = b := by
  obtain ⟨k, rfl, hk⟩ := mem_set_iff_enumeratedBy.mp hx
  rw [Nat.mem_pairColumn.mp (enumeratedBy_subset_pairColumn k hk)]

end FriedbergMuchnik

/-- Because `A` only receives numbers from even columns and `B` only from odd columns, the two
constructed sets are disjoint. -/
theorem disjoint_friedbergMuchnikSetA_friedbergMuchnikSetB :
    Disjoint friedbergMuchnikSetA friedbergMuchnikSetB := by
  refine Set.disjoint_left.mpr fun x hxA hxB => ?_
  have hA := FriedbergMuchnik.side_unpair_snd_of_mem_set hxA
  have hB := FriedbergMuchnik.side_unpair_snd_of_mem_set hxB
  rw [hA] at hB
  exact Bool.false_ne_true hB

namespace FriedbergMuchnik

open Oracle.Single

section Effectivity

open Primrec

private theorem primrec_side : Primrec side :=
  nat_bodd

private theorem primrec_monitoredSide : Primrec monitoredSide :=
  Primrec.not.comp nat_bodd

private theorem primrec_equivCode : Primrec State.equivCode :=
  of_equiv (e := State.equivCode)

private theorem primrec_equivCode_symm : Primrec State.equivCode.symm :=
  of_equiv_symm (e := State.equivCode)

private theorem primrec_setA_code :
    Primrec fun st : State => Finset.equivBitIndices.symm st.setA :=
  (fst.comp (fst.comp primrec_equivCode)).of_eq fun _ => rfl

private theorem primrec_setB_code :
    Primrec fun st : State => Finset.equivBitIndices.symm st.setB :=
  (snd.comp (fst.comp primrec_equivCode)).of_eq fun _ => rfl

private theorem primrec_records : Primrec State.records :=
  (fst.comp (snd.comp primrec_equivCode)).of_eq fun _ => rfl

private theorem primrec_floor : Primrec State.floor :=
  (snd.comp (snd.comp primrec_equivCode)).of_eq fun _ => rfl

private theorem primrec_witness_state : Primrec₂ State.witness := by
  have hget : Primrec fun p : State × ℕ => p.1.records[p.2]? :=
    list_getElem?.comp (primrec_records.comp fst) snd
  have hdef : Primrec fun p : State × ℕ => p.2.leastInPairColumn p.1.floor :=
    nat_leastInPairColumn.comp snd (primrec_floor.comp fst)
  exact (option_getD.comp (option_map hget (fst.comp snd).to₂) hdef).to₂

private theorem primrec_restraint_state : Primrec₂ State.restraint :=
  (option_bind (list_getElem?.comp (primrec_records.comp fst) snd) (snd.comp snd).to₂).to₂

private theorem primrec_set_state :
    Primrec₂ fun (st : State) (b : Bool) => Finset.equivBitIndices.symm (st.set b) := by
  refine (Primrec.cond snd (primrec_setB_code.comp fst)
    (primrec_setA_code.comp fst)).to₂.of_eq fun st b => ?_
  cases b <;> rfl

private theorem primrec_stageRun_code :
    Primrec fun q : ℕ × ℕ × ℕ × ℕ =>
      stageRun (Finset.equivBitIndices q.1) q.2.1 q.2.2.1 q.2.2.2 := by
  have hargs : Primrec fun q : ℕ × ℕ × ℕ × ℕ =>
      (q.1, q.2.1, ofNat Code q.2.2.1, q.2.2.2) :=
    fst.pair ((fst.comp snd).pair
      (((Primrec.ofNat Code).comp (fst.comp (snd.comp snd))).pair (snd.comp (snd.comp snd))))
  exact (Code.primrec_evalStage_equivBitIndices.comp hargs).of_eq fun _ => rfl

private theorem primrec_candRun :
    Primrec fun q : State × ℕ × ℕ => candRun q.1 q.2.1 q.2.2 := by
  have hk : Primrec fun q : State × ℕ × ℕ => q.2.2 := snd.comp snd
  have hs : Primrec fun q : State × ℕ × ℕ => q.2.1 := fst.comp snd
  have hw : Primrec fun q : State × ℕ × ℕ => q.1.witness q.2.2 :=
    primrec_witness_state.comp fst hk
  have hmside : Primrec fun q : State × ℕ × ℕ =>
      Finset.equivBitIndices.symm (q.1.set (side q.2.2)) :=
    primrec_set_state.comp fst (primrec_side.comp hk)
  have hmmon : Primrec fun q : State × ℕ × ℕ =>
      Finset.equivBitIndices.symm (q.1.set (monitoredSide q.2.2)) :=
    primrec_set_state.comp fst (primrec_monitoredSide.comp hk)
  have hnotmem : PrimrecPred fun q : State × ℕ × ℕ =>
      q.1.witness q.2.2 ∉ q.1.set (side q.2.2) :=
    ((mem_equivBitIndices.comp hmside hw).not).of_eq fun q => by simp
  have hcol : PrimrecPred fun q : State × ℕ × ℕ =>
      q.1.witness q.2.2 ∈ q.2.2.pairColumn :=
    mem_pairColumn.comp hk hw
  have hrun : Primrec fun q : State × ℕ × ℕ =>
      stageRun (q.1.set (monitoredSide q.2.2)) q.2.1 (q.2.2 / 2) (q.1.witness q.2.2) :=
    (primrec_stageRun_code.comp
      (hmmon.pair (hs.pair ((nat_div.comp hk (const 2)).pair hw)))).of_eq fun q => by simp
  have hbind : Primrec fun q : State × ℕ × ℕ =>
      (stageRun (q.1.set (monitoredSide q.2.2)) q.2.1 (q.2.2 / 2) (q.1.witness q.2.2)).bind
        fun d => if d.output = 0 then some d else none :=
    option_bind hrun
      (Primrec.ite (Primrec.eq.comp (Code.Halt.primrec_output.comp snd) (const 0))
        (option_some.comp snd) (const none)).to₂
  exact (Primrec.ite (hnotmem.and hcol) hbind (const none)).of_eq fun _ => rfl

/-- Least-priority attention selection is primitive recursive in the state and stage. -/
theorem primrec_attention : Primrec₂ attention := by
  have hcand : Primrec fun p : (State × ℕ) × ℕ => candRun p.1.1 p.1.2 p.2 :=
    primrec_candRun.comp ((fst.comp fst).pair ((snd.comp fst).pair snd))
  have his : Primrec₂ fun (q : State × ℕ) (k : ℕ) => (candRun q.1 q.2 k).isSome :=
    (option_isSome.comp hcand).to₂
  have hpair : Primrec₂ fun (p : (State × ℕ) × ℕ) (d : Code.Halt) => (p.2, d) :=
    ((snd.comp fst).pair snd).to₂
  exact (option_bind (list_find? (list_range.comp snd) his) (option_map hcand hpair).to₂).to₂

private theorem primrec_nextFloor :
    Primrec fun q : State × ℕ × ℕ × Code.Halt => nextFloor q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hfl : Primrec fun q : State × ℕ × ℕ × Code.Halt => q.1.floor :=
    primrec_floor.comp fst
  have hs : Primrec fun q : State × ℕ × ℕ × Code.Halt => q.2.1 := fst.comp snd
  have hk : Primrec fun q : State × ℕ × ℕ × Code.Halt => q.2.2.1 := fst.comp (snd.comp snd)
  have huse : Primrec fun q : State × ℕ × ℕ × Code.Halt => q.2.2.2.use :=
    Code.Halt.primrec_use.comp (snd.comp (snd.comp snd))
  have hpart1 : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      max q.1.floor (max q.2.1 q.2.2.2.use) + 1 :=
    succ.comp (nat_max.comp hfl (nat_max.comp hs huse))
  have hunionCode : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      Finset.equivBitIndices.symm q.1.setA ||| Finset.equivBitIndices.symm q.1.setB :=
    nat_lor.comp (primrec_setA_code.comp fst) (primrec_setB_code.comp fst)
  have hsup : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      (((Finset.equivBitIndices.symm q.1.setA |||
        Finset.equivBitIndices.symm q.1.setB).bitIndices.map (· + 1)).foldr max 0) :=
    list_foldr (list_map (nat_bitIndices.comp hunionCode) (succ.comp snd).to₂) (const 0)
      (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂
  have hitem : Primrec₂ fun (q : State × ℕ × ℕ × Code.Halt) (i : ℕ) =>
      max (q.1.witness i + 1) (((q.1.restraint i).map (· + 1)).getD 0) :=
    nat_max.comp (succ.comp (primrec_witness_state.comp (fst.comp fst) snd))
      (option_getD.comp
        (option_map (primrec_restraint_state.comp (fst.comp fst) snd) (succ.comp snd).to₂)
        (const 0))
  have hpart3 : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      ((List.range (q.2.2.1 + 1)).map fun i =>
        max (q.1.witness i + 1) (((q.1.restraint i).map (· + 1)).getD 0)).foldr max 0 :=
    list_foldr (list_map (list_range.comp (succ.comp hk)) hitem) (const 0)
      (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂
  refine (nat_max.comp hpart1 (nat_max.comp hsup hpart3)).of_eq fun q => ?_
  have hunion : q.1.setA ∪ q.1.setB =
      ((Finset.equivBitIndices.symm q.1.setA |||
        Finset.equivBitIndices.symm q.1.setB).bitIndices).toFinset := by
    rw [← Finset.equivBitIndices_apply, Finset.equivBitIndices_lor,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hsup_eq (l : List ℕ) : l.toFinset.sup (· + 1) = (l.map (· + 1)).foldr max 0 := by
    have hmap : (l.map (· + 1)).toFinset = l.toFinset.image (· + 1) := by ext; simp
    calc l.toFinset.sup (· + 1)
      _ = (l.toFinset.image (· + 1)).sup id := by rw [Finset.sup_image]; rfl
      _ = (l.map (· + 1)).toFinset.sup id := by rw [hmap]
      _ = (l.map (· + 1)).foldr (· ⊔ ·) ⊥ := (List.foldr_sup_eq_sup_toFinset _).symm
      _ = (l.map (· + 1)).foldr max 0 := rfl
  simp only [nextFloor]
  rw [hunion, hsup_eq]

private theorem primrec_applyAction :
    Primrec fun q : State × ℕ × ℕ × Code.Halt => applyAction q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hk : Primrec fun q : State × ℕ × ℕ × Code.Halt => q.2.2.1 := fst.comp (snd.comp snd)
  have huse : Primrec fun q : State × ℕ × ℕ × Code.Halt => q.2.2.2.use :=
    Code.Halt.primrec_use.comp (snd.comp (snd.comp snd))
  have hw : Primrec fun q : State × ℕ × ℕ × Code.Halt => q.1.witness q.2.2.1 :=
    primrec_witness_state.comp fst hk
  have hmA : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      Finset.equivBitIndices.symm q.1.setA := primrec_setA_code.comp fst
  have hmB : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      Finset.equivBitIndices.symm q.1.setB := primrec_setB_code.comp fst
  have hbit : Primrec fun q : State × ℕ × ℕ × Code.Halt => 2 ^ q.1.witness q.2.2.1 :=
    nat_pow.comp (const 2) hw
  have hmA' : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      if side q.2.2.1 = false then
        Finset.equivBitIndices.symm q.1.setA ||| 2 ^ q.1.witness q.2.2.1
      else Finset.equivBitIndices.symm q.1.setA :=
    Primrec.ite (Primrec.eq.comp (primrec_side.comp hk) (const false))
      (nat_lor.comp hmA hbit) hmA
  have hmB' : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      if side q.2.2.1 = true then
        Finset.equivBitIndices.symm q.1.setB ||| 2 ^ q.1.witness q.2.2.1
      else Finset.equivBitIndices.symm q.1.setB :=
    Primrec.ite (Primrec.eq.comp (primrec_side.comp hk) (const true))
      (nat_lor.comp hmB hbit) hmB
  have hrecItem : Primrec₂ fun (q : State × ℕ × ℕ × Code.Halt) (i : ℕ) =>
      (q.1.witness i, q.1.restraint i) :=
    ((primrec_witness_state.comp (fst.comp fst) snd).pair
      (primrec_restraint_state.comp (fst.comp fst) snd)).to₂
  have hrecs : Primrec fun q : State × ℕ × ℕ × Code.Halt =>
      (List.range q.2.2.1).map (fun i => (q.1.witness i, q.1.restraint i)) ++
        [(q.1.witness q.2.2.1, some q.2.2.2.use)] :=
    list_append.comp (list_map (list_range.comp hk) hrecItem)
      (list_cons.comp (hw.pair (option_some.comp huse)) (const []))
  refine (primrec_equivCode_symm.comp
    ((hmA'.pair hmB').pair (hrecs.pair primrec_nextFloor))).of_eq fun q => ?_
  rcases q with ⟨st, s, k, d⟩
  cases hside : side k <;>
    simp only [State.equivCode, applyAction, hside, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, Equiv.coe_fn_symm_mk, ← Finset.equivBitIndices_symm_insert,
      Equiv.apply_symm_apply]

/-- The stage transition `step` is primitive recursive. -/
theorem primrec_step : Primrec₂ step := by
  have hsome : Primrec₂ fun (p : State × ℕ) (kd : ℕ × Code.Halt) =>
      applyAction p.1 p.2 kd.1 kd.2 :=
    (primrec_applyAction.comp
      ((fst.comp fst).pair ((snd.comp fst).pair ((fst.comp snd).pair (snd.comp snd))))).to₂
  exact (option_casesOn primrec_attention fst hsome).to₂.of_eq fun st s => by
    dsimp only
    cases h : attention st s <;> simp [step, h]

/-- The finite state `state s` is primitive recursive in the stage `s`. -/
theorem primrec_state : Primrec state := by
  refine (nat_rec₁ State.init (primrec_step.comp snd fst).to₂).of_eq fun s => ?_
  induction s with
  | zero => rfl
  | succ s ih => simp [state, ih]

/-- The acting priority `action s` is primitive recursive in the stage `s`. -/
theorem primrec_action : Primrec action :=
  option_map (primrec_attention.comp primrec_state Primrec.id) (fst.comp snd).to₂

/-- The witness `witness j s` is primitive recursive uniformly in `(j, s)`. -/
theorem primrec₂_witness : Primrec₂ witness :=
  (primrec_witness_state.comp (primrec_state.comp snd) fst).to₂

/-- The restraint `restraint j s` is primitive recursive uniformly in `(j, s)`. -/
theorem primrec₂_restraint : Primrec₂ restraint :=
  (primrec_restraint_state.comp (primrec_state.comp snd) fst).to₂

/-- The binary finite-set codes of `stage b s` are primitive recursive uniformly in `(b, s)`. -/
theorem primrec₂_stage :
    Primrec₂ fun (b : Bool) (s : ℕ) => Finset.equivBitIndices.symm (stage b s) :=
  (primrec_set_state.comp (primrec_state.comp snd) fst).to₂

/-- For each side `b`, the binary finite-set codes of `stage b s` are primitive recursive in `s`. -/
theorem primrec_stage (b : Bool) :
    Primrec fun s => Finset.equivBitIndices.symm (stage b s) :=
  primrec₂_stage.comp (const b) Primrec.id

end Effectivity

/-- Both constructed limit sets `set false` and `set true` are c.e. -/
theorem rePred_mem_set (b : Bool) : REPred (· ∈ set b) :=
  rePred_iff_exists_stages.mpr
    ⟨stage b, monotone_stage b, stage_zero b, (primrec_stage b).to_comp, rfl⟩

/-- Canonical partial-recursive enumeration codes for `set false` (`A`) and `set true` (`B`). -/
noncomputable def code (b : Bool) : Nat.Partrec.Code :=
  (rePred_iff_exists_code.mp (rePred_mem_set b)).choose

/-- Membership in `set b` is the domain of `code b`. -/
@[simp]
theorem dom_eval_code (b : Bool) (x : ℕ) : ((code b).eval x).Dom ↔ x ∈ set b :=
  ((rePred_iff_exists_code.mp (rePred_mem_set b)).choose_spec x).symm

/-- `set b` is the c.e. domain `{x | ((code b).eval x).Dom}` of `code b`. -/
theorem set_eq_dom_code (b : Bool) : set b = {x | ((code b).eval x).Dom} :=
  Set.ext (fun x => (dom_eval_code b x).symm)

end FriedbergMuchnik

/-- `friedbergMuchnikSetA` is c.e. -/
theorem rePred_mem_friedbergMuchnikSetA : REPred (· ∈ friedbergMuchnikSetA) :=
  FriedbergMuchnik.rePred_mem_set false

/-- `friedbergMuchnikSetB` is c.e. -/
theorem rePred_mem_friedbergMuchnikSetB : REPred (· ∈ friedbergMuchnikSetB) :=
  FriedbergMuchnik.rePred_mem_set true

end TauCeti
