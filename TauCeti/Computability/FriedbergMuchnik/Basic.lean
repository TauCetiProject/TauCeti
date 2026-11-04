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
theorem (`friedberg_muchnik`) and its Turing-degree corollaries strictly between `0` and `0'`:

1. `restraint_lt_witness_of_notMem` and `exists_lt_of_mem_injuriesAt`: active higher-priority
   restraints lie strictly below unenumerated lower-priority witnesses, so only `k < e` can injure
   requirement `e`.
2. `exists_lt_action_between` and the `2 ^ k` / `2 ^ e - 1` bounds on `attentionStages`,
   `enumeratedBy`, `initializationStages`, `injurySet`, `injuryStages`, and
   `monitoredInjuryEvents`.
3. `zero_mem_eval_of_mem_set`, `zero_notMem_eval_of_notMem_set`, and `eval_ne_oracle`: requirement
   satisfaction in both stabilization regimes.

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
      exact witness_succ_of_attention_eq_none h ▸ ih hb hw
    · have hik : i ≤ k := not_lt.mp fun hgt => by
        rw [restraint_succ_of_attention_eq_some_of_gt h hgt] at hb; cases hb
      rcases lt_trichotomy j k with hjk | rfl | hkj
      · rw [restraint_succ_of_attention_eq_some_of_lt h (hij.trans hjk)] at hb
        rw [witness_succ_of_attention_eq_some_of_le h hjk.le] at hw ⊢
        exact ih hb fun hm => hw (monotone_stage (side j) s.le_succ hm)
      · exact absurd (witness_succ_of_attention_eq_some_of_le h le_rfl ▸
          stage_side_succ_of_attention_eq_some h ▸ Finset.mem_insert_self _ _) hw
      · rw [witness_succ_of_attention_eq_some_of_gt h hkj]
        have hfl := Nat.le_leastInPairColumn j (nextFloor (state s) s k d)
        rcases lt_or_eq_of_le hik with hlt | rfl
        · rw [restraint_succ_of_attention_eq_some_of_lt h hlt] at hb
          exact (lt_nextFloor_of_restraint_eq_some hlt.le hb).trans_le hfl
        · rw [restraint_succ_of_attention_eq_some_self h] at hb
          exact Option.some.inj hb ▸ (lt_nextFloor_use (state s) s i d).trans_le hfl

/-- **Injury attribution.** Every `x ∈ injuriesAt (stage (monitoredSide e)) restraint e s` was
enumerated by an action of some `k < e` with `side k = monitoredSide e` and `witness k s = x`. -/
theorem exists_lt_of_mem_injuriesAt {e s x : ℕ}
    (hx : x ∈ injuriesAt (stage (monitoredSide e)) restraint e s) :
    ∃ k < e, side k = monitoredSide e ∧ action s = some k ∧ witness k s = x := by
  obtain ⟨k, hside, hact, hw⟩ := mem_fresh_stage.mp (injuriesAt_subset_fresh hx)
  obtain ⟨d, hd⟩ := action_eq_some_iff.mp hact
  have hnotMem := (requiresAttention_state_iff.mp (attention_eq_some_iff.mp hd).1).1
  obtain ⟨-, -, b, hb, hxb⟩ := mem_injuriesAt.mp hx
  refine ⟨k, ?_, hside, hact, hw⟩
  rcases lt_trichotomy k e with hlt | rfl | hgt
  · exact hlt
  · exact absurd hside.symm (monitoredSide_ne_side k)
  · have := restraint_lt_witness_of_notMem hgt hb hnotMem; omega

/-- Every labelled injury event in `monitoredInjuryEvents` comes from an action of some `k < e`. -/
theorem exists_lt_of_mem_monitoredInjuryEvents {e s x : ℕ} {b : Bool}
    (h : (b, s, x) ∈ monitoredInjuryEvents stage monitoredSide restraint e) :
    b = monitoredSide e ∧ ∃ k < e, side k = b ∧ action s = some k ∧ witness k s = x := by
  obtain ⟨rfl, hx⟩ := mk_mem_monitoredInjuryEvents.mp h
  exact ⟨rfl, exists_lt_of_mem_injuriesAt hx⟩

/-! ### Epochs, stabilization, and quantitative bounds -/

/-- If no `i < k` acts in `[s₁, s₂)`, then `witness k` stays constant from `s₁` to `s₂`. -/
theorem witness_eq_of_forall_lt_action_ne {k s₁ s₂ : ℕ} (hs : s₁ ≤ s₂)
    (hno : ∀ t, s₁ ≤ t → t < s₂ → ∀ i < k, action t ≠ some i) :
    witness k s₂ = witness k s₁ := by
  induction s₂, hs using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    have hnot : t + 1 ∉ appointmentStages k := by
      rw [succ_mem_appointmentStages, succ_mem_initializationStages]
      exact fun ⟨i, hik, hti⟩ => hno t ht (Nat.lt_succ_self t) i hik hti
    rw [witness_succ_eq_of_notMem_appointmentStages hnot,
      ih fun u hu₁ hu₂ => hno u hu₁ (Nat.lt_succ_of_lt hu₂)]

/-- If no `i ≤ k` acts in `[s₁, s₂)`, then `restraint k` stays constant from `s₁` to `s₂`. -/
theorem restraint_eq_of_forall_le_action_ne {k s₁ s₂ : ℕ} (hs : s₁ ≤ s₂)
    (hno : ∀ t, s₁ ≤ t → t < s₂ → ∀ i ≤ k, action t ≠ some i) :
    restraint k s₂ = restraint k s₁ := by
  induction s₂, hs using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rcases hatt : attention (state t) t with _ | ⟨m, d⟩
    · rw [restraint_succ_of_attention_eq_none hatt,
        ih fun u hu₁ hu₂ => hno u hu₁ (Nat.lt_succ_of_lt hu₂)]
    · have hkm : k < m := not_le.mp fun hmk =>
        hno t ht (Nat.lt_succ_self t) m hmk (action_eq_some_iff.mpr ⟨d, hatt⟩)
      rw [restraint_succ_of_attention_eq_some_of_lt hatt hkm,
        ih fun u hu₁ hu₂ => hno u hu₁ (Nat.lt_succ_of_lt hu₂)]

/-- **At most one action per epoch.** Between any two actions of `k`, some `i < k` acts. -/
theorem exists_lt_action_between (k : ℕ) {s₁ s₂ : ℕ} (hlt : s₁ < s₂)
    (hs₁ : action s₁ = some k) (hs₂ : action s₂ = some k) :
    ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < k, action t = some i := by
  by_contra hno
  push Not at hno
  obtain ⟨d₁, hd₁⟩ := action_eq_some_iff.mp hs₁
  obtain ⟨d₂, hd₂⟩ := action_eq_some_iff.mp hs₂
  have hw_eq : witness k s₂ = witness k s₁ :=
    (witness_eq_of_forall_lt_action_ne (Nat.succ_le_of_lt hlt) fun t ht₁ ht₂ i hik =>
      hno t (Nat.lt_of_succ_le ht₁) ht₂ i hik).trans
      (witness_succ_of_attention_eq_some_of_le hd₁ le_rfl)
  exact (requiresAttention_state_iff.mp (attention_eq_some_iff.mp hd₂).1).1 <| hw_eq ▸
    monotone_stage (side k) (Nat.succ_le_of_lt hlt)
      (stage_side_succ_of_attention_eq_some hd₁ ▸ Finset.mem_insert_self _ _)

/-- **Quantitative attention bound `2 ^ k`.** -/
theorem finite_attentionStages_and_ncard_le (k : ℕ) :
    (attentionStages action k).Finite ∧ (attentionStages action k).ncard ≤ 2 ^ k :=
  Priority.finite_attentionStages_and_ncard_le_two_pow
    (fun e _ _ => exists_lt_action_between e) k

/-- Requirement `k` enumerates finitely many numbers, at most `2 ^ k`. -/
theorem finite_enumeratedBy_and_ncard_le (k : ℕ) :
    (enumeratedBy k).Finite ∧ (enumeratedBy k).ncard ≤ 2 ^ k := by
  have hatt := finite_attentionStages_and_ncard_le k
  have hsub : enumeratedBy k ⊆ (fun t => witness k (t - 1)) '' attentionStages action k :=
    fun _ hx =>
      let ⟨s, hs, hw⟩ := mem_enumeratedBy.mp hx; ⟨s + 1, mem_attentionStages.mpr ⟨s, rfl, hs⟩, hw⟩
  exact ⟨(hatt.1.image _).subset hsub,
    (Set.ncard_le_ncard hsub (hatt.1.image _)).trans ((Set.ncard_image_le hatt.1).trans hatt.2)⟩

/-- **Quantitative initialization bound `2 ^ e - 1`.** -/
theorem finite_initializationStages_and_ncard_le (e : ℕ) :
    (initializationStages action e).Finite ∧ (initializationStages action e).ncard ≤ 2 ^ e - 1 :=
  Priority.finite_initializationStages_and_ncard_le (fun k _ _ => exists_lt_action_between k) e

/-- **Quantitative injury-set bound `2 ^ e - 1`.** -/
theorem finite_injurySet_and_ncard_le (e : ℕ) :
    (injurySet (stage (monitoredSide e)) restraint e).Finite ∧
      (injurySet (stage (monitoredSide e)) restraint e).ncard ≤ 2 ^ e - 1 := by
  have hcauses : ∀ s x, x ∈ injuriesAt (stage (monitoredSide e)) restraint e s →
      ∃ k < e, x ∈ enumeratedBy k := fun s _ hx =>
    let ⟨k, hke, _, hact, hw⟩ := exists_lt_of_mem_injuriesAt hx
    ⟨k, hke, mem_enumeratedBy.mpr ⟨s, hact, hw⟩⟩
  obtain ⟨hfin, hle⟩ := finite_injurySet_and_ncard_le_sum_of_causes enumeratedBy (2 ^ ·)
    (fun k _ => finite_enumeratedBy_and_ncard_le k) hcauses
  exact ⟨hfin, hle.trans_eq (by simpa using Nat.geomSum_eq (le_refl 2) e)⟩

/-- Priority `0` is never injured on its monitored oracle. -/
theorem injurySet_zero_eq_empty : injurySet (stage (monitoredSide 0)) restraint 0 = ∅ := by
  obtain ⟨hfin, hle⟩ := finite_injurySet_and_ncard_le 0
  exact (Set.ncard_eq_zero hfin).mp (Nat.le_zero.mp hle)

/-- **Quantitative injury-stages bound `2 ^ e - 1`.** -/
theorem finite_injuryStages_and_ncard_le (e : ℕ) :
    (injuryStages (stage (monitoredSide e)) restraint e).Finite ∧
      (injuryStages (stage (monitoredSide e)) restraint e).ncard ≤ 2 ^ e - 1 := by
  obtain ⟨hfin, hle⟩ := finite_injurySet_and_ncard_le e
  exact ⟨(finite_injurySet_iff_finite_injuryStages (monotone_stage _)).mp hfin,
    (ncard_injuryStages_le (monotone_stage _) hfin).trans hle⟩

/-- **Quantitative bound on labelled `monitoredInjuryEvents`.** -/
theorem finite_monitoredInjuryEvents_and_ncard_le (e : ℕ) :
    (monitoredInjuryEvents stage monitoredSide restraint e).Finite ∧
      (monitoredInjuryEvents stage monitoredSide restraint e).ncard ≤ 2 ^ e - 1 := by
  obtain ⟨hfin_set, hle_set⟩ := finite_injurySet_and_ncard_le e
  have hinj : Set.InjOn (fun p : Bool × ℕ × ℕ => p.2.2)
      (monitoredInjuryEvents stage monitoredSide restraint e) := fun _ h₁ _ h₂ hx => by
    rw [mem_monitoredInjuryEvents] at h₁ h₂
    exact Prod.ext (h₁.1.trans h₂.1.symm)
      (injOn_snd_injuryEvents (monotone_stage _)
        (mem_injuryEvents.mpr h₁.2) (mem_injuryEvents.mpr h₂.2) hx)
  refine ⟨finite_monitoredInjuryEvents_iff_finite_injuryStages.mpr
    (finite_injuryStages_and_ncard_le e).1, ?_⟩
  rw [← hinj.ncard_image, image_number_monitoredInjuryEvents]
  exact hle_set

/-- **Stabilization and permanent witness.** From some stage `s₀` onward, no `i < k` acts,
`witness k` stays at `witness k s₀`, and `k` acts at most once. -/
theorem exists_stabilization_stage (k : ℕ) :
    ∃ s₀, (∀ s ≥ s₀, ∀ i < k, action s ≠ some i) ∧
      (∀ s ≥ s₀, witness k s = witness k s₀) ∧
      {s | s₀ ≤ s ∧ action s = some k}.Subsingleton := by
  have ⟨s₀, hno⟩ : ∃ s₀, ∀ s ≥ s₀, ∀ i < k, action s ≠ some i := by
    rcases k with _ | k'
    · exact ⟨0, fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
    · obtain ⟨s₀, hs₀⟩ := exists_forall_lt_of_finite (e := k')
        fun i _ => (finite_attentionStages_and_ncard_le i).1
      exact ⟨s₀, fun s hs i hik hact => by have := hs₀ s hs i hact; omega⟩
  refine ⟨s₀, hno, fun s hs => witness_eq_of_forall_lt_action_ne hs fun t ht _ => hno t ht, ?_⟩
  rintro s₁ ⟨hs₁₀, hs₁⟩ s₂ ⟨hs₂₀, hs₂⟩
  rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
  · obtain ⟨t, hs₁t, -, i, hik, hti⟩ := exists_lt_action_between k hlt hs₁ hs₂
    exact absurd hti (hno t (hs₁₀.trans hs₁t.le) i hik)
  · rfl
  · obtain ⟨t, hs₂t, -, i, hik, hti⟩ := exists_lt_action_between k hgt hs₂ hs₁
    exact absurd hti (hno t (hs₂₀.trans hs₂t.le) i hik)

/-- Every requirement `k` eventually holds a permanent witness in `k.pairColumn`. -/
theorem exists_eventually_witness_eq (k : ℕ) :
    ∃ x ∈ k.pairColumn, ∀ᶠ s in atTop, witness k s = x := by
  obtain ⟨s₀, -, hw, -⟩ := exists_stabilization_stage k
  exact ⟨witness k s₀, witness_mem_pairColumn k s₀, eventually_atTop.mpr ⟨s₀, hw⟩⟩

/-! ### Satisfaction of requirements and Turing incomparability -/

/-- **Satisfaction when the permanent witness enters `set (side k)`.** -/
theorem zero_mem_eval_of_mem_set {k s₀ : ℕ}
    (hno : ∀ s ≥ s₀, ∀ i < k, action s ≠ some i) (hx : witness k s₀ ∈ set (side k)) :
    0 ∈ Code.eval (set (monitoredSide k)).oracle (ofNat Code (k / 2)) (witness k s₀) := by
  set x := witness k s₀
  obtain ⟨j, -, hj_enum⟩ := mem_set_iff_enumeratedBy.mp hx
  obtain ⟨s₁, hact₁, hw₁⟩ := mem_enumeratedBy.mp hj_enum
  have hjk : j = k := not_ne_iff.mp fun hjk =>
    have hxj : x ∈ j.pairColumn := hw₁ ▸ witness_mem_pairColumn j s₁
    Set.disjoint_left.mp (Nat.disjoint_pairColumn hjk) hxj (witness_mem_pairColumn k s₀)
  subst j
  obtain ⟨d, hd₁⟩ := action_eq_some_iff.mp hact₁
  obtain ⟨hreq₁, -⟩ := attention_eq_some_iff.mp hd₁
  have hno_after : ∀ t ≥ s₁ + 1, ∀ i < k, action t ≠ some i := by
    intro t ht i hik hti
    rcases lt_or_ge t s₀ with hts₀ | hs₀t
    · obtain ⟨d', hd'⟩ := action_eq_some_iff.mp hti
      have hx_lt : x < witness k (t + 1) := by
        rw [witness_succ_of_attention_eq_some_of_gt hd' hik]
        exact (lt_nextFloor_of_mem_stage (monotone_stage (side k) ht
          (hw₁ ▸ stage_side_succ_of_attention_eq_some hd₁ ▸ Finset.mem_insert_self _ _))).trans_le
          (Nat.le_leastInPairColumn k _)
      exact hx_lt.not_ge (monotone_witness k hts₀)
    · exact hno t hs₀t i hik hti
  have hno_self : ∀ t ≥ s₁ + 1, action t ≠ some k := fun t ht htk => by
    obtain ⟨u, hs₁u, -, i, hik, hui⟩ :=
      exists_lt_action_between k (Nat.lt_of_succ_le ht) hact₁ htk
    exact hno_after u (Nat.succ_le_of_lt hs₁u) i hik hui
  have hrest : ∀ t ≥ s₁ + 1, restraint k t = some d.use := fun t ht =>
    (restraint_eq_of_forall_le_action_ne ht fun u hu _ i hik =>
      (lt_or_eq_of_le hik).elim (hno_after u hu i) fun h => h ▸ hno_self u hu).trans
      (restraint_succ_of_attention_eq_some_self hd₁)
  have hinj_empty : ∀ t ≥ s₁ + 1, injuriesAt (stage (monitoredSide k)) restraint k t = ∅ :=
    fun t ht => Finset.eq_empty_of_forall_notMem fun _ hz =>
      let ⟨i, hik, _, hti, _⟩ := exists_lt_of_mem_injuriesAt hz; hno_after t ht i hik hti
  obtain ⟨-, hstg, hout₀⟩ := requiresAttention_state_iff.mp hreq₁
  rw [hw₁, stageRun_eq_evalStage_setAnswers] at hstg
  have hrun_succ := (Code.evalStage_eq_some_iff.mp
    (stage_monitoredSide_succ_of_attention_eq_some hd₁ ▸ Code.evalStage_mono s₁.le_succ hstg)).2.1
  have hlim : Code.evaln (Code.setAnswers (set (monitoredSide k))) (s₁ + 1)
      (ofNat Code (k / 2)) x = some d := by
    rw [set_eq_stageLimit]
    exact Code.evaln_setAnswers_stageLimit_eq_some_of_injuriesAt_eq_empty
      (monotone_stage _) hrun_succ (fun t ht _ hz => ⟨d.use, hrest t ht, hz.le⟩) hinj_empty
  rw [← hout₀]
  exact Code.evaln_sound hlim (by simp)

/-- **Satisfaction when the permanent witness stays outside `set (side k)`.** -/
theorem zero_notMem_eval_of_notMem_set {k s₀ : ℕ}
    (hno : ∀ s ≥ s₀, ∀ i < k, action s ≠ some i) (hx : witness k s₀ ∉ set (side k)) :
    0 ∉ Code.eval (set (monitoredSide k)).oracle (ofNat Code (k / 2)) (witness k s₀) := by
  intro h0
  rw [set_eq_stageLimit] at h0
  obtain ⟨d, hd0, hev⟩ := Code.exists_eventually_evaln_setAnswers_eq_some_of_mem_eval
    (monotone_stage (monitoredSide k)) tendsto_id (y := 0) h0
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.mp hev
  let s := max s₀ (max s₁ (encode (ofNat Code (k / 2)) + 1))
  have hs₀ : s₀ ≤ s := le_max_left _ _
  have hs₁' : s₁ ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hcode : encode (ofNat Code (k / 2)) < s :=
    Nat.lt_of_succ_le ((le_max_right _ _).trans (le_max_right _ _))
  have hws : witness k s = witness k s₀ :=
    witness_eq_of_forall_lt_action_ne hs₀ fun t ht _ => hno t ht
  have hreq : RequiresAttention (state s) s k d := requiresAttention_state_iff.mpr
    ⟨hws ▸ fun hm => hx (mem_set_iff_exists_stage.mpr ⟨s, hm⟩),
      by rw [hws, stageRun_eq_evalStage_setAnswers]
         exact Code.evalStage_eq_some_iff.mpr ⟨hcode, hs₁ s hs₁', by omega⟩, hd0⟩
  obtain ⟨⟨m, d'⟩, hmd⟩ := Option.ne_none_iff_exists'.mp fun hn =>
    attention_eq_none_iff.mp hn k d hreq
  obtain ⟨-, hmin⟩ := attention_eq_some_iff.mp hmd
  obtain rfl : m = k := by
    rcases lt_trichotomy m k with hmk | rfl | hkm
    · exact absurd (action_eq_some_iff.mpr ⟨d', hmd⟩) (hno s hs₀ m hmk)
    · rfl
    · exact absurd hreq (hmin k hkm d)
  exact hx <| hws ▸ mem_set_iff_exists_stage.mpr
    ⟨s + 1, stage_side_succ_of_attention_eq_some hmd ▸ Finset.mem_insert_self _ _⟩

/-- **Every requirement `R_k` is satisfied.** -/
theorem eval_ne_oracle (k : ℕ) :
    Code.eval (set (monitoredSide k)).oracle (ofNat Code (k / 2)) ≠ (set (side k)).oracle := by
  obtain ⟨s₀, hno, -, -⟩ := exists_stabilization_stage k
  intro heq
  by_cases hx : witness k s₀ ∈ set (side k)
  · have h0 := zero_mem_eval_of_mem_set hno hx; rw [heq] at h0; simp [hx] at h0
  · have hnot0 := zero_notMem_eval_of_notMem_set hno hx; rw [heq] at hnot0; simp [hx] at hnot0

end FriedbergMuchnik

/-! ### Main theorems and Turing degree corollaries -/

/-- `friedbergMuchnikSetA` is not Turing reducible to `friedbergMuchnikSetB`. -/
theorem not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB :
    ¬TuringReducible friedbergMuchnikSetA.oracle friedbergMuchnikSetB.oracle := fun h => by
  obtain ⟨c, hc⟩ := Oracle.Single.Code.turingReducible_iff_exists_code.mp h
  have h2e := FriedbergMuchnik.eval_ne_oracle (2 * encode c)
  simp only [FriedbergMuchnik.monitoredSide_two_mul, FriedbergMuchnik.side_two_mul,
    FriedbergMuchnik.set_true_eq, FriedbergMuchnik.set_false_eq,
    Nat.mul_div_right _ Nat.zero_lt_two, ofNat_encode] at h2e
  exact h2e hc

/-- `friedbergMuchnikSetB` is not Turing reducible to `friedbergMuchnikSetA`. -/
theorem not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA :
    ¬TuringReducible friedbergMuchnikSetB.oracle friedbergMuchnikSetA.oracle := fun h => by
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

/-- **The Friedberg–Muchnik theorem [S, VII.2.1].** -/
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
        (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) :=
  Set.degree_mem_Ioo_of_incomparable
    (FriedbergMuchnik.set_false_eq ▸ turingReducible_set_jump_empty false)
    (FriedbergMuchnik.set_true_eq ▸ turingReducible_set_jump_empty true)
    not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB
    not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA

/-- The Turing degree of `friedbergMuchnikSetB` lies strictly between `0` and `0'`. -/
theorem degree_friedbergMuchnikSetB_mem_Ioo :
    toAntisymmetrization TuringReducible friedbergMuchnikSetB.oracle ∈
      Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
        (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) :=
  Set.degree_mem_Ioo_of_incomparable
    (FriedbergMuchnik.set_true_eq ▸ turingReducible_set_jump_empty true)
    (FriedbergMuchnik.set_false_eq ▸ turingReducible_set_jump_empty false)
    not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA
    not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB

/-- The Turing degrees of `friedbergMuchnikSetA` and `friedbergMuchnikSetB` are incomparable. -/
theorem incomparable_degree_friedbergMuchnikSetA_friedbergMuchnikSetB :
    ¬(toAntisymmetrization TuringReducible friedbergMuchnikSetA.oracle ≤
        toAntisymmetrization TuringReducible friedbergMuchnikSetB.oracle) ∧
      ¬(toAntisymmetrization TuringReducible friedbergMuchnikSetB.oracle ≤
        toAntisymmetrization TuringReducible friedbergMuchnikSetA.oracle) := by
  rw [turingDegree_le_iff, turingDegree_le_iff]
  exact ⟨not_turingReducible_friedbergMuchnikSetA_friedbergMuchnikSetB,
    not_turingReducible_friedbergMuchnikSetB_friedbergMuchnikSetA⟩

/-- **Degree form of the Friedberg–Muchnik theorem.** -/
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
