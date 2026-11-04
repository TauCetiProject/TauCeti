/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.FriedbergMuchnik.Construction
public import TauCeti.Computability.Jump.Basic
public import TauCeti.Computability.Priority.Injury.Monitored
public import TauCeti.Computability.Priority.Preservation
import TauCeti.Computability.Priority.Injury.Causes
import TauCeti.Data.Set.Card
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Verification of the original Friedberg–Muchnik theorem

This file verifies the finite-injury stage construction of
`TauCeti.Computability.FriedbergMuchnik.Construction` [S, VII.2.1] and proves the Friedberg–Muchnik
theorem: the two c.e. sets `friedbergMuchnikSetA` and `friedbergMuchnikSetB` are Turing
incomparable, hence noncomputable, and represent incomparable c.e. Turing degrees strictly between
`0` and `0'`.

## Proof outline

1. **Restraint–witness invariant (`restraint_lt_witness_of_notMem`):** whenever `i < j`,
   `restraint i s = some b`, and `witness j s` has not yet entered `stage (side j) s`, we have
   `b < witness j s`. Consequently, no requirement `j > e` can injure `restraint e s`, and no
   requirement can injure itself because `side e ≠ monitoredSide e`. Every injury to `e` on
   `stage (monitoredSide e)` is therefore caused by an action of some `k < e`
   (`exists_lt_of_mem_injuriesAt`).
2. **At most one action per epoch (`exists_lt_action_between`):** once requirement `k` acts and
   enumerates `witness k s₁`, its witness stays constant and inside `stage (side k)` until some
   `i < k` acts to initialize `k`. Thus `k` acts at most once between higher-priority actions.
3. **Quantitative bounds:** `TauCeti.Computability.Priority.Initialization` and
   `TauCeti.Computability.Priority.Injury.Causes` immediately give at most `2 ^ k` attentions and
   enumerated witnesses for priority `k`, and at most `2 ^ e - 1` initializations, injuring numbers,
   injury stages, and labelled `monitoredInjuryEvents` for priority `e`.
4. **Satisfaction in both stabilization regimes:** once all `i < k` stop acting after stage `s₀`,
   `witness k` settles permanently on `x = witness k s₀ ∈ k.pairColumn`:
   * if `x ∈ set (side k)`, then at the unique stage `s₁` where `k` enumerated `x`, no `i ≤ k` ever
     acted after `s₁`, so `restraint k` stayed at `some d.use` with zero injuries after `s₁ + 1` and
     preserved `Φ_{k / 2}^{set (monitoredSide k)}(x)↓ = 0 ≠ 1` (`zero_mem_eval_of_mem_set`);
   * if `x ∉ set (side k)`, no zero computation can converge on `x` relative to
     `set (monitoredSide k)`, for otherwise `k` would eventually require and receive attention at
     `x` (`zero_notMem_eval_of_notMem_set`).

## References

* R. M. Friedberg, *Two recursively enumerable sets of incomparable degrees of unsolvability*,
  Proc. Nat. Acad. Sci. U.S.A. **43** (1957), 236–238.
* A. A. Muchnik, *On the unsolvability of the problem of reducibility in the theory of algorithms*,
  Dokl. Akad. Nauk SSSR **108** (1956), 194–197.
* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.2.1.
-/

public section

open Denumerable Encodable Filter TauCeti.Enumeration TauCeti.Priority

namespace TauCeti

namespace FriedbergMuchnik

open Oracle.Single

/-! ### Stage invariant and injury attribution -/

/-- **Restraint–witness invariant.** An active higher-priority restraint `restraint i s = some b`
(`i < j`) lies strictly below any unenumerated lower-priority witness `witness j s`. -/
theorem restraint_lt_witness_of_notMem {i j s b : ℕ} (hij : i < j)
    (hb : restraint i s = some b) (hw : witness j s ∉ stage (side j) s) :
    b < witness j s := by
  induction s with
  | zero => simp at hb
  | succ s ih =>
    rcases h : attention (state s) s with _ | ⟨k, d⟩
    · rw [restraint_succ_of_attention_eq_none h] at hb
      rw [stage_succ_of_attention_eq_none h, witness_succ_of_attention_eq_none h] at hw
      rw [witness_succ_of_attention_eq_none h]
      exact ih hb hw
    · -- Any active restraint after `k` acts has priority `i ≤ k`.
      have hik : i ≤ k := by
        by_contra hgt
        rw [restraint_succ_of_attention_eq_some_of_gt h (not_le.mp hgt)] at hb
        cases hb
      rcases lt_trichotomy j k with hjk | rfl | hkj
      · -- `i < j < k`: both `restraint i` and `witness j` are preserved by locality.
        have hb' : restraint i s = some b := by
          rwa [restraint_succ_of_attention_eq_some_of_lt h (hij.trans hjk)] at hb
        have hw' : witness j s ∉ stage (side j) s := by
          intro hmem
          apply hw
          rw [witness_succ_of_attention_eq_some_of_le h hjk.le]
          exact monotone_stage (side j) s.le_succ hmem
        rw [witness_succ_of_attention_eq_some_of_le h hjk.le]
        exact ih hb' hw'
      · -- `j = k`: impossible since `witness k s` entered `stage (side k) (s + 1)`.
        exfalso
        apply hw
        rw [witness_succ_of_attention_eq_some_of_le h le_rfl,
          stage_side_succ_of_attention_eq_some h]
        exact Finset.mem_insert_self _ _
      · -- `k < j`: `j` was initialized with `witness j (s + 1) ≥ nextFloor`.
        rw [witness_succ_of_attention_eq_some_of_gt h hkj]
        have hfl_le : nextFloor (state s) s k d ≤
            j.leastInPairColumn (nextFloor (state s) s k d) :=
          Nat.le_leastInPairColumn j _
        rcases lt_or_eq_of_le hik with hlt | rfl
        · rw [restraint_succ_of_attention_eq_some_of_lt h hlt] at hb
          exact (lt_nextFloor_of_restraint_eq_some hlt.le hb).trans_le hfl_le
        · rw [restraint_succ_of_attention_eq_some_self h] at hb
          obtain ⟨rfl⟩ := Option.some.inj hb
          exact (lt_nextFloor_use (state s) s i d).trans_le hfl_le

/-- **Injury attribution.** Every number `x` injuring requirement `e` on its monitored oracle
`stage (monitoredSide e)` at stage `s + 1` was enumerated by an action of some strictly higher
priority `k < e` with `side k = monitoredSide e` and `witness k s = x`. -/
theorem exists_lt_of_mem_injuriesAt {e s x : ℕ}
    (hx : x ∈ injuriesAt (stage (monitoredSide e)) restraint e s) :
    ∃ k < e, side k = monitoredSide e ∧ action s = some k ∧ witness k s = x := by
  obtain ⟨k, hside, hact, hw⟩ := mem_fresh_stage.mp (injuriesAt_subset_fresh hx)
  obtain ⟨d, hd⟩ := action_eq_some_iff.mp hact
  have hnotMem : witness k s ∉ stage (side k) s :=
    (requiresAttention_state_iff.mp (attention_eq_some_iff.mp hd).1).1
  obtain ⟨-, -, b, hb, hxb⟩ := mem_injuriesAt.mp hx
  refine ⟨k, ?_, hside, hact, hw⟩
  rcases lt_trichotomy k e with hlt | rfl | hgt
  · exact hlt
  · exact absurd hside.symm (monitoredSide_ne_side k)
  · have hlt : b < witness k s := restraint_lt_witness_of_notMem hgt hb hnotMem
    omega

/-- Every labelled injury event in `monitoredInjuryEvents stage monitoredSide restraint e` comes
from an action of some `k < e` on `monitoredSide e`. -/
theorem exists_lt_of_mem_monitoredInjuryEvents {e s x : ℕ} {b : Bool}
    (h : (b, s, x) ∈ monitoredInjuryEvents stage monitoredSide restraint e) :
    b = monitoredSide e ∧
      ∃ k < e, side k = b ∧ action s = some k ∧ witness k s = x := by
  obtain ⟨rfl, hx⟩ := mk_mem_monitoredInjuryEvents.mp h
  exact ⟨rfl, exists_lt_of_mem_injuriesAt hx⟩

/-! ### Epochs, stabilization, and quantitative bounds -/

/-- If no requirement `i < k` acts in `[s₁, s₂)`, then `witness k` stays constant from `s₁` to
`s₂`. -/
theorem witness_eq_of_forall_lt_action_ne {k s₁ s₂ : ℕ} (hs : s₁ ≤ s₂)
    (hno : ∀ t, s₁ ≤ t → t < s₂ → ∀ i < k, action t ≠ some i) :
    witness k s₂ = witness k s₁ := by
  induction s₂, hs using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    have hnot : t + 1 ∉ appointmentStages k := by
      rw [succ_mem_appointmentStages, succ_mem_initializationStages]
      rintro ⟨i, hik, hti⟩
      exact hno t ht (Nat.lt_succ_self t) i hik hti
    rw [witness_succ_eq_of_notMem_appointmentStages hnot,
      ih (fun u hu₁ hu₂ => hno u hu₁ (Nat.lt_succ_of_lt hu₂))]

/-- **At most one action per epoch.** Between any two stages `s₁ < s₂` at which `k` receives
attention, some higher-priority requirement `i < k` must act. -/
theorem exists_lt_action_between (k : ℕ) {s₁ s₂ : ℕ} (hlt : s₁ < s₂)
    (hs₁ : action s₁ = some k) (hs₂ : action s₂ = some k) :
    ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < k, action t = some i := by
  by_contra hno
  push Not at hno
  obtain ⟨d₁, hd₁⟩ := action_eq_some_iff.mp hs₁
  obtain ⟨d₂, hd₂⟩ := action_eq_some_iff.mp hs₂
  -- From `s₁ + 1` to `s₂`, no `i < k` acts, so `witness k s₂ = witness k s₁`.
  have hw_eq : witness k s₂ = witness k s₁ := by
    calc witness k s₂
      _ = witness k (s₁ + 1) :=
        witness_eq_of_forall_lt_action_ne (Nat.succ_le_of_lt hlt)
          (fun t ht₁ ht₂ i hik => hno t (Nat.lt_of_succ_le ht₁) ht₂ i hik)
      _ = witness k s₁ := witness_succ_of_attention_eq_some_of_le hd₁ le_rfl
  -- Yet `witness k s₁` entered `stage (side k) (s₁ + 1) ⊆ stage (side k) s₂`.
  have hmem : witness k s₂ ∈ stage (side k) s₂ := by
    rw [hw_eq]
    exact monotone_stage (side k) (Nat.succ_le_of_lt hlt)
      (stage_side_succ_of_attention_eq_some hd₁ ▸ Finset.mem_insert_self _ _)
  exact (requiresAttention_state_iff.mp (attention_eq_some_iff.mp hd₂).1).1 hmem

/-- **Quantitative attention bound `2 ^ k`.** Requirement `k` receives attention finitely often and
at most `2 ^ k` times. -/
theorem finite_attentionStages_and_ncard_le (k : ℕ) :
    (attentionStages action k).Finite ∧ (attentionStages action k).ncard ≤ 2 ^ k :=
  Priority.finite_attentionStages_and_ncard_le_two_pow
    (fun e _ _ => exists_lt_action_between e) k

/-- Requirement `k` enumerates finitely many numbers, at most `2 ^ k`. -/
theorem finite_enumeratedBy_and_ncard_le (k : ℕ) :
    (enumeratedBy k).Finite ∧ (enumeratedBy k).ncard ≤ 2 ^ k := by
  have hatt := finite_attentionStages_and_ncard_le k
  have hsub : enumeratedBy k ⊆ (fun t => witness k (t - 1)) '' attentionStages action k := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_enumeratedBy.mp hx
    exact ⟨s + 1, mem_attentionStages.mpr ⟨s, rfl, hs⟩, rfl⟩
  exact ⟨(hatt.1.image _).subset hsub,
    (Set.ncard_le_ncard hsub (hatt.1.image _)).trans
      ((Set.ncard_image_le hatt.1).trans hatt.2)⟩

/-- **Quantitative initialization bound `2 ^ e - 1`.** Requirement `e` is initialized finitely
often and at most `2 ^ e - 1` times. -/
theorem finite_initializationStages_and_ncard_le (e : ℕ) :
    (initializationStages action e).Finite ∧
      (initializationStages action e).ncard ≤ 2 ^ e - 1 :=
  Priority.finite_initializationStages_and_ncard_le
    (fun k _ _ => exists_lt_action_between k) e

/-- **Quantitative injury-set bound `2 ^ e - 1`.** Requirement `e` is injured on its monitored
oracle `stage (monitoredSide e)` by finitely many numbers, and at most `2 ^ e - 1`. -/
theorem finite_injurySet_and_ncard_le (e : ℕ) :
    (injurySet (stage (monitoredSide e)) restraint e).Finite ∧
      (injurySet (stage (monitoredSide e)) restraint e).ncard ≤ 2 ^ e - 1 := by
  have hcauses : ∀ s x, x ∈ injuriesAt (stage (monitoredSide e)) restraint e s →
      ∃ k < e, x ∈ enumeratedBy k := by
    intro s x hx
    obtain ⟨k, hke, -, hact, hw⟩ := exists_lt_of_mem_injuriesAt hx
    exact ⟨k, hke, mem_enumeratedBy.mpr ⟨s, hact, hw⟩⟩
  obtain ⟨hfin, hle⟩ := finite_injurySet_and_ncard_le_sum_of_causes enumeratedBy (2 ^ ·)
    (fun k _ => finite_enumeratedBy_and_ncard_le k) hcauses
  exact ⟨hfin, hle.trans_eq (by simpa using Nat.geomSum_eq (le_refl 2) e)⟩

/-- Priority `0` is never injured on its monitored oracle. -/
theorem injurySet_zero_eq_empty :
    injurySet (stage (monitoredSide 0)) restraint 0 = ∅ := by
  obtain ⟨hfin, hle⟩ := finite_injurySet_and_ncard_le 0
  exact (Set.ncard_eq_zero hfin).mp (Nat.le_zero.mp hle)

/-- **Quantitative injury-stages bound `2 ^ e - 1`.** Requirement `e` experiences at most
`2 ^ e - 1` injury stages on its monitored oracle. -/
theorem finite_injuryStages_and_ncard_le (e : ℕ) :
    (injuryStages (stage (monitoredSide e)) restraint e).Finite ∧
      (injuryStages (stage (monitoredSide e)) restraint e).ncard ≤ 2 ^ e - 1 := by
  obtain ⟨hfin, hle⟩ := finite_injurySet_and_ncard_le e
  exact ⟨(finite_injurySet_iff_finite_injuryStages (monotone_stage _)).mp hfin,
    (ncard_injuryStages_le (monotone_stage _) hfin).trans hle⟩

/-- **Quantitative bound on labelled `monitoredInjuryEvents`.** Requirement `e` has at most
`2 ^ e - 1` labelled injury events. -/
theorem finite_monitoredInjuryEvents_and_ncard_le (e : ℕ) :
    (monitoredInjuryEvents stage monitoredSide restraint e).Finite ∧
      (monitoredInjuryEvents stage monitoredSide restraint e).ncard ≤ 2 ^ e - 1 := by
  obtain ⟨hfin_set, hle_set⟩ := finite_injurySet_and_ncard_le e
  obtain ⟨hfin_stg, -⟩ := finite_injuryStages_and_ncard_le e
  have hfin_ev : (monitoredInjuryEvents stage monitoredSide restraint e).Finite :=
    finite_monitoredInjuryEvents_iff_finite_injuryStages.mpr hfin_stg
  have hinj : Set.InjOn (fun p : Bool × ℕ × ℕ => p.2.2)
      (monitoredInjuryEvents stage monitoredSide restraint e) := by
    rintro ⟨b₁, s₁, x₁⟩ h₁ ⟨b₂, s₂, x₂⟩ h₂ (rfl : x₁ = x₂)
    obtain ⟨rfl, hx₁⟩ := mk_mem_monitoredInjuryEvents.mp h₁
    obtain ⟨rfl, hx₂⟩ := mk_mem_monitoredInjuryEvents.mp h₂
    have hs : s₁ = s₂ := unique_entry_stage (monotone_stage _)
      (injuriesAt_subset_fresh hx₁) (injuriesAt_subset_fresh hx₂)
    rw [hs]
  refine ⟨hfin_ev, ?_⟩
  rw [← hinj.ncard_image, image_number_monitoredInjuryEvents]
  exact hle_set

/-- **Stabilization and permanent witness.** For every requirement `k`, there is a stage `s₀` from
which no higher-priority requirement `i < k` ever acts, `witness k` remains permanently fixed at
`witness k s₀ ∈ k.pairColumn`, and `k` acts at most once from `s₀` onward. -/
theorem exists_stabilization_stage (k : ℕ) :
    ∃ s₀, (∀ s ≥ s₀, ∀ i < k, action s ≠ some i) ∧
      (∀ s ≥ s₀, witness k s = witness k s₀) ∧
      {s | s₀ ≤ s ∧ action s = some k}.Subsingleton := by
  rcases k with _ | k'
  · refine ⟨0, fun _ _ _ hi => absurd hi (Nat.not_lt_zero _), ?_, ?_⟩
    · intro s _
      exact witness_eq_of_forall_lt_action_ne (Nat.zero_le s)
        (fun _ _ _ _ hi => absurd hi (Nat.not_lt_zero _))
    · rintro s₁ ⟨-, hs₁⟩ s₂ ⟨-, hs₂⟩
      rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
      · obtain ⟨t, -, -, i, hi, -⟩ := exists_lt_action_between 0 hlt hs₁ hs₂
        exact absurd hi (Nat.not_lt_zero _)
      · rfl
      · obtain ⟨t, -, -, i, hi, -⟩ := exists_lt_action_between 0 hgt hs₂ hs₁
        exact absurd hi (Nat.not_lt_zero _)
  · obtain ⟨s₀, hs₀⟩ := exists_forall_lt_of_finite (e := k')
      (fun i _ => (finite_attentionStages_and_ncard_le i).1)
    have hno : ∀ s ≥ s₀, ∀ i < k' + 1, action s ≠ some i := by
      intro s hs i hik hact
      have := hs₀ s hs i hact
      omega
    refine ⟨s₀, hno, fun s hs => witness_eq_of_forall_lt_action_ne hs
      (fun t ht _ => hno t ht), ?_⟩
    rintro s₁ ⟨hs₁₀, hs₁⟩ s₂ ⟨hs₂₀, hs₂⟩
    rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
    · obtain ⟨t, hs₁t, -, i, hik, hti⟩ := exists_lt_action_between (k' + 1) hlt hs₁ hs₂
      exact absurd hti (hno t (hs₁₀.trans hs₁t.le) i hik)
    · rfl
    · obtain ⟨t, hs₂t, -, i, hik, hti⟩ := exists_lt_action_between (k' + 1) hgt hs₂ hs₁
      exact absurd hti (hno t (hs₂₀.trans hs₂t.le) i hik)

/-- Every requirement `k` eventually holds a permanent witness in `k.pairColumn`. -/
theorem exists_eventually_witness_eq (k : ℕ) :
    ∃ x ∈ k.pairColumn, ∀ᶠ s in atTop, witness k s = x := by
  obtain ⟨s₀, -, hw, -⟩ := exists_stabilization_stage k
  exact ⟨witness k s₀, witness_mem_pairColumn k s₀, eventually_atTop.mpr ⟨s₀, hw⟩⟩

/-! ### Satisfaction of requirements and Turing incomparability -/

/-- **Satisfaction when the permanent witness enters `set (side k)`.** Once all `i < k` have stopped
acting by stage `s₀`, if the permanent witness `x = witness k s₀` belongs to `set (side k)`, then
the zero computation that triggered its enumeration is permanently preserved in the limit:
`0 ∈ Code.eval (set (monitoredSide k)).oracle (ofNat Code (k / 2)) x`. -/
theorem zero_mem_eval_of_mem_set {k s₀ : ℕ}
    (hno : ∀ s ≥ s₀, ∀ i < k, action s ≠ some i)
    (hx : witness k s₀ ∈ set (side k)) :
    0 ∈ Code.eval (set (monitoredSide k)).oracle (ofNat Code (k / 2)) (witness k s₀) := by
  set x := witness k s₀
  -- Find the unique stage `s₁` at which `x` entered `stage (side k)` via an action of `k`.
  obtain ⟨j, hside, hj_enum⟩ := mem_set_iff_enumeratedBy.mp hx
  obtain ⟨s₁, hact₁, hw₁⟩ := mem_enumeratedBy.mp hj_enum
  have hjk : j = k := by
    by_contra hjk
    have hxj : x ∈ j.pairColumn := hw₁ ▸ witness_mem_pairColumn j s₁
    exact Set.disjoint_left.mp (Nat.disjoint_pairColumn hjk) hxj (witness_mem_pairColumn k s₀)
  subst j
  obtain ⟨d, hd₁⟩ := action_eq_some_iff.mp hact₁
  obtain ⟨hreq₁, -⟩ := attention_eq_some_iff.mp hd₁
  -- No `i < k` can ever act after `s₁`, for such an action would push `witness k` strictly above
  -- `x ∈ stage (side k) (s₁ + 1)`, contradicting `witness k s₀ = x` (if `t < s₀`) or `hno`
  -- (if `t ≥ s₀`).
  have hno_after : ∀ t ≥ s₁ + 1, ∀ i < k, action t ≠ some i := by
    intro t ht i hik hti
    rcases lt_or_ge t s₀ with hts₀ | hs₀t
    · obtain ⟨d', hd'⟩ := action_eq_some_iff.mp hti
      have hx_mem_t : x ∈ stage (side k) t :=
        monotone_stage (side k) ht
          (hw₁ ▸ stage_side_succ_of_attention_eq_some hd₁ ▸ Finset.mem_insert_self _ _)
      have hx_lt_fl : x < nextFloor (state t) t i d' := lt_nextFloor_of_mem_stage hx_mem_t
      have hx_lt_wt : x < witness k (t + 1) := by
        rw [witness_succ_of_attention_eq_some_of_gt hd' hik]
        exact hx_lt_fl.trans_le (Nat.le_leastInPairColumn k _)
      have hwt_le : witness k (t + 1) ≤ x := monotone_witness k (Nat.succ_le_of_lt hts₀)
      omega
    · exact hno t hs₀t i hik hti
  -- Hence `k` itself never acts after `s₁`, so `restraint k t = some d.use` for all `t ≥ s₁ + 1`.
  have hno_self : ∀ t ≥ s₁ + 1, action t ≠ some k := by
    intro t ht htk
    obtain ⟨u, hs₁u, hut, i, hik, hui⟩ :=
      exists_lt_action_between k (Nat.lt_of_succ_le ht) hact₁ htk
    exact hno_after u (Nat.succ_le_of_lt hs₁u) i hik hui
  have hrest : ∀ t ≥ s₁ + 1, restraint k t = some d.use := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact restraint_succ_of_attention_eq_some_self hd₁
    | succ t ht ih =>
      rcases hatt : attention (state t) t with _ | ⟨m, d'⟩
      · rw [restraint_succ_of_attention_eq_none hatt, ih]
      · have hact_m : action t = some m := action_eq_some_iff.mpr ⟨d', hatt⟩
        have hkm : k < m := by
          rcases lt_trichotomy m k with hmk | rfl | hkm
          · exact absurd hact_m (hno_after t ht m hmk)
          · exact absurd hact_m (hno_self t ht)
          · exact hkm
        rw [restraint_succ_of_attention_eq_some_of_lt hatt hkm, ih]
  -- And `k` is never injured on `stage (monitoredSide k)` at or after `s₁ + 1`.
  have hinj_empty : ∀ t ≥ s₁ + 1, injuriesAt (stage (monitoredSide k)) restraint k t = ∅ := by
    intro t ht
    refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨i, hik, -, hti, -⟩ := exists_lt_of_mem_injuriesAt hz
    exact hno_after t ht i hik hti
  -- At stage `s₁ + 1`, `stage (monitoredSide k)` was protected, so the run still succeeds.
  obtain ⟨-, hstg, hout₀⟩ := requiresAttention_state_iff.mp hreq₁
  have hrun_succ : Code.evaln (Code.setAnswers (stage (monitoredSide k) (s₁ + 1))) (s₁ + 1)
      (ofNat Code (k / 2)) x = some d := by
    rw [hw₁, stageRun_eq_evalStage_setAnswers] at hstg
    have hstg' : Code.evalStage (Code.setAnswers (stage (monitoredSide k) (s₁ + 1))) (s₁ + 1)
        (ofNat Code (k / 2)) x = some d := by
      rw [stage_monitoredSide_succ_of_attention_eq_some hd₁]
      exact Code.evalStage_mono s₁.le_succ hstg
    exact (Code.evalStage_eq_some_iff.mp hstg').2.1
  -- Preservation transfers the run to the limit set `set (monitoredSide k)`.
  have hlim : Code.evaln (Code.setAnswers (set (monitoredSide k))) (s₁ + 1)
      (ofNat Code (k / 2)) x = some d := by
    rw [set_eq_stageLimit]
    exact Code.evaln_setAnswers_stageLimit_eq_some_of_injuriesAt_eq_empty
      (monotone_stage (monitoredSide k)) hrun_succ
      (fun t ht z hz => ⟨d.use, hrest t ht, hz.le⟩) hinj_empty
  rw [← hout₀]
  exact Code.evaln_sound hlim (by simp)

/-- **Satisfaction when the permanent witness stays outside `set (side k)`.** Once all `i < k` have
stopped acting by stage `s₀`, if `x = witness k s₀ ∉ set (side k)`, then `Φ_{k / 2}` relative to
`set (monitoredSide k)` cannot output `0` on `x`. -/
theorem zero_notMem_eval_of_notMem_set {k s₀ : ℕ}
    (hno : ∀ s ≥ s₀, ∀ i < k, action s ≠ some i)
    (hx : witness k s₀ ∉ set (side k)) :
    0 ∉ Code.eval (set (monitoredSide k)).oracle (ofNat Code (k / 2)) (witness k s₀) := by
  intro h0
  set x := witness k s₀
  rw [set_eq_stageLimit] at h0
  obtain ⟨d, hd0, hev⟩ := Code.exists_eventually_evaln_setAnswers_eq_some_of_mem_eval
    (monotone_stage (monitoredSide k)) tendsto_id (y := 0) h0
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.mp hev
  let s := max s₀ (max s₁ (encode (ofNat Code (k / 2)) + 1))
  have hs₀ : s₀ ≤ s := le_max_left _ _
  have hs₁' : s₁ ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hcode : encode (ofNat Code (k / 2)) < s := by
    have : encode (ofNat Code (k / 2)) + 1 ≤ s := (le_max_right _ _).trans (le_max_right _ _)
    omega
  have hout : d.output < s := by omega
  have hws : witness k s = x :=
    witness_eq_of_forall_lt_action_ne hs₀ (fun t ht _ => hno t ht)
  have hrun : stageRun (stage (monitoredSide k) s) s (k / 2) (witness k s) = some d := by
    rw [hws, stageRun_eq_evalStage_setAnswers]
    exact Code.evalStage_eq_some_iff.mpr ⟨hcode, hs₁ s hs₁', hout⟩
  have hnot_stage : witness k s ∉ stage (side k) s := by
    rw [hws]
    exact fun hm => hx (mem_set_iff_exists_stage.mpr ⟨s, hm⟩)
  have hreq : RequiresAttention (state s) s k d :=
    requiresAttention_state_iff.mpr ⟨hnot_stage, hrun, hd0⟩
  obtain ⟨⟨m, d'⟩, hmd⟩ := Option.ne_none_iff_exists'.mp fun hn =>
    attention_eq_none_iff.mp hn k d hreq
  obtain ⟨hm_req, hmin⟩ := attention_eq_some_iff.mp hmd
  obtain rfl : m = k := by
    rcases lt_trichotomy m k with hmk | rfl | hkm
    · exact absurd (action_eq_some_iff.mpr ⟨d', hmd⟩) (hno s hs₀ m hmk)
    · rfl
    · exact absurd hreq (hmin k hkm d)
  have hx_mem : x ∈ set (side m) := by
    rw [← hws]
    exact mem_set_iff_exists_stage.mpr
      ⟨s + 1, stage_side_succ_of_attention_eq_some hmd ▸ Finset.mem_insert_self _ _⟩
  exact hx hx_mem

/-- **Every requirement `R_k` is satisfied:** the `k / 2`-th single-oracle program relative to
`set (monitoredSide k)` does not compute `(set (side k)).oracle`. -/
theorem eval_ne_oracle (k : ℕ) :
    Code.eval (set (monitoredSide k)).oracle (ofNat Code (k / 2)) ≠ (set (side k)).oracle := by
  obtain ⟨s₀, hno, -, -⟩ := exists_stabilization_stage k
  intro heq
  by_cases hx : witness k s₀ ∈ set (side k)
  · have h0 := zero_mem_eval_of_mem_set hno hx
    rw [heq] at h0
    simp [hx] at h0
  · have hnot0 := zero_notMem_eval_of_notMem_set hno hx
    rw [heq] at hnot0
    simp [hx] at hnot0

end FriedbergMuchnik

/-! ### Main theorems and Turing degree corollaries -/

/-- `friedbergMuchnikSetA` is not Turing reducible to `friedbergMuchnikSetB`. -/
theorem not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB :
    ¬TuringReducible friedbergMuchnikSetA.oracle friedbergMuchnikSetB.oracle := by
  intro h
  obtain ⟨c, hc⟩ := Oracle.Single.Code.turingReducible_iff_exists_code.mp h
  have h2e := FriedbergMuchnik.eval_ne_oracle (2 * encode c)
  simp only [FriedbergMuchnik.monitoredSide_two_mul, FriedbergMuchnik.side_two_mul,
    FriedbergMuchnik.set_true_eq, FriedbergMuchnik.set_false_eq,
    Nat.mul_div_right _ Nat.zero_lt_two, ofNat_encode] at h2e
  exact h2e hc

/-- `friedbergMuchnikSetB` is not Turing reducible to `friedbergMuchnikSetA`. -/
theorem not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA :
    ¬TuringReducible friedbergMuchnikSetB.oracle friedbergMuchnikSetA.oracle := by
  intro h
  obtain ⟨c, hc⟩ := Oracle.Single.Code.turingReducible_iff_exists_code.mp h
  have hodd : (2 * encode c + 1) / 2 = encode c := by omega
  have h2e1 := FriedbergMuchnik.eval_ne_oracle (2 * encode c + 1)
  simp only [FriedbergMuchnik.monitoredSide_two_mul_add_one, FriedbergMuchnik.side_two_mul_add_one,
    FriedbergMuchnik.set_false_eq, FriedbergMuchnik.set_true_eq, hodd, ofNat_encode] at h2e1
  exact h2e1 hc

/-- `friedbergMuchnikSetA` is not computable. -/
theorem not_computablePred_mem_friedbergMuchnikSetA :
    ¬ComputablePred (· ∈ friedbergMuchnikSetA) := fun h =>
  not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB <|
    ((Set.turingReducible_empty_iff _).mpr h).trans (Set.empty_turingReducible _)

/-- `friedbergMuchnikSetB` is not computable. -/
theorem not_computablePred_mem_friedbergMuchnikSetB :
    ¬ComputablePred (· ∈ friedbergMuchnikSetB) := fun h =>
  not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA <|
    ((Set.turingReducible_empty_iff _).mpr h).trans (Set.empty_turingReducible _)

/-- **The Friedberg–Muchnik theorem [S, VII.2.1].** There exist two c.e. sets of natural numbers
that are Turing incomparable. -/
theorem friedberg_muchnik :
    ∃ A B : Set ℕ, REPred (· ∈ A) ∧ REPred (· ∈ B) ∧
      ¬TuringReducible A.oracle B.oracle ∧ ¬TuringReducible B.oracle A.oracle :=
  ⟨friedbergMuchnikSetA, friedbergMuchnikSetB,
    rePred_mem_friedbergMuchnikSetA, rePred_mem_friedbergMuchnikSetB,
    not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB,
    not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA⟩

private theorem turingReducible_set_jump_empty (b : Bool) :
    TuringReducible (FriedbergMuchnik.set b).oracle (∅ : Set ℕ).jump.oracle := by
  rw [FriedbergMuchnik.set_eq_dom_code b]
  exact Set.turingReducible_jump_of_recursiveIn ∅
    (Nat.Partrec.Code.exists_code.mpr ⟨FriedbergMuchnik.code b, rfl⟩).recursiveIn

/-- The Turing degree of `friedbergMuchnikSetA` lies strictly between `0` and `0'`. -/
theorem degree_friedbergMuchnikSetA_mem_Ioo :
    toAntisymmetrization TuringReducible friedbergMuchnikSetA.oracle ∈
      Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
        (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) := by
  have hA : TuringReducible friedbergMuchnikSetA.oracle (∅ : Set ℕ).jump.oracle :=
    FriedbergMuchnik.set_false_eq ▸ turingReducible_set_jump_empty false
  have hB : TuringReducible friedbergMuchnikSetB.oracle (∅ : Set ℕ).jump.oracle :=
    FriedbergMuchnik.set_true_eq ▸ turingReducible_set_jump_empty true
  refine ⟨?_, ?_⟩
  · rw [lt_iff_le_not_ge, turingDegree_le_iff, turingDegree_le_iff]
    exact ⟨Set.empty_turingReducible _, fun h =>
      not_computablePred_mem_friedbergMuchnikSetA ((Set.turingReducible_empty_iff _).mp h)⟩
  · rw [lt_iff_le_not_ge, turingDegree_le_iff, turingDegree_le_iff]
    exact ⟨hA, fun h => not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA (hB.trans h)⟩

/-- The Turing degree of `friedbergMuchnikSetB` lies strictly between `0` and `0'`. -/
theorem degree_friedbergMuchnikSetB_mem_Ioo :
    toAntisymmetrization TuringReducible friedbergMuchnikSetB.oracle ∈
      Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
        (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) := by
  have hA : TuringReducible friedbergMuchnikSetA.oracle (∅ : Set ℕ).jump.oracle :=
    FriedbergMuchnik.set_false_eq ▸ turingReducible_set_jump_empty false
  have hB : TuringReducible friedbergMuchnikSetB.oracle (∅ : Set ℕ).jump.oracle :=
    FriedbergMuchnik.set_true_eq ▸ turingReducible_set_jump_empty true
  refine ⟨?_, ?_⟩
  · rw [lt_iff_le_not_ge, turingDegree_le_iff, turingDegree_le_iff]
    exact ⟨Set.empty_turingReducible _, fun h =>
      not_computablePred_mem_friedbergMuchnikSetB ((Set.turingReducible_empty_iff _).mp h)⟩
  · rw [lt_iff_le_not_ge, turingDegree_le_iff, turingDegree_le_iff]
    exact ⟨hB, fun h => not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB (hA.trans h)⟩

/-- The Turing degrees of `friedbergMuchnikSetA` and `friedbergMuchnikSetB` are incomparable in
`TuringDegree`. -/
theorem incomparable_degree_friedbergMuchnikSetA_friedbergMuchnikSetB :
    ¬(toAntisymmetrization TuringReducible friedbergMuchnikSetA.oracle ≤
        toAntisymmetrization TuringReducible friedbergMuchnikSetB.oracle) ∧
      ¬(toAntisymmetrization TuringReducible friedbergMuchnikSetB.oracle ≤
        toAntisymmetrization TuringReducible friedbergMuchnikSetA.oracle) := by
  rw [turingDegree_le_iff, turingDegree_le_iff]
  exact ⟨not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB,
    not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA⟩

/-- **Degree form of the Friedberg–Muchnik theorem.** There exist two c.e. sets whose Turing degrees
are incomparable and both lie strictly between `0` and `0'`. -/
theorem exists_incomparable_ce_turingDegrees_mem_Ioo :
    ∃ A B : Set ℕ, REPred (· ∈ A) ∧ REPred (· ∈ B) ∧
      toAntisymmetrization TuringReducible A.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      toAntisymmetrization TuringReducible B.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      ¬(toAntisymmetrization TuringReducible A.oracle ≤
          toAntisymmetrization TuringReducible B.oracle) ∧
      ¬(toAntisymmetrization TuringReducible B.oracle ≤
          toAntisymmetrization TuringReducible A.oracle) :=
  ⟨friedbergMuchnikSetA, friedbergMuchnikSetB,
    rePred_mem_friedbergMuchnikSetA, rePred_mem_friedbergMuchnikSetB,
    degree_friedbergMuchnikSetA_mem_Ioo, degree_friedbergMuchnikSetB_mem_Ioo,
    incomparable_degree_friedbergMuchnikSetA_friedbergMuchnikSetB.1,
    incomparable_degree_friedbergMuchnikSetA_friedbergMuchnikSetB.2⟩

end TauCeti
