/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Priority.Records
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Initialization stages and epoch-bounded attention counting

In a priority schedule `action : ℕ → Option ℕ`, an action of `i < e` at stage `s` initializes `e`
at run index `s + 1 ∈ initializationStages action e = ⋃ i < e, attentionStages action i`. When `e`
acts at most once per epoch between higher-priority actions, every action of `e` after its first is
preceded by a distinct initialization stage, giving `(attentionStages action e).ncard ≤
(initializationStages action e).ncard + 1` and the inductive `2 ^ e` / `2 ^ e - 1` bounds.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters VII.1 and VII.2.
-/

public section

open Set

namespace TauCeti.Priority

variable {action : ℕ → Option ℕ}

/-- The run indices `s + 1` at which some higher-priority `i < e` acted at stage `s`. -/
def initializationStages (action : ℕ → Option ℕ) (e : ℕ) : Set ℕ :=
  {t | ∃ s i, t = s + 1 ∧ action s = some i ∧ i < e}

/-- Membership in `initializationStages`. -/
theorem mem_initializationStages {e t : ℕ} :
    t ∈ initializationStages action e ↔ ∃ s i, t = s + 1 ∧ action s = some i ∧ i < e := Iff.rfl

/-- `s + 1` is an initialization stage of `e` iff some `i < e` acts at stage `s`. -/
@[simp] theorem succ_mem_initializationStages {e s : ℕ} :
    s + 1 ∈ initializationStages action e ↔ ∃ i < e, action s = some i := by
  simp [initializationStages, and_comm]

/-- Stage `0` is never an initialization stage. -/
@[simp] theorem zero_notMem_initializationStages {e : ℕ} : 0 ∉ initializationStages action e := by
  simp [initializationStages]

/-- Priority `0` has no higher-priority requirements and is never initialized. -/
@[simp] theorem initializationStages_zero (action : ℕ → Option ℕ) :
    initializationStages action 0 = ∅ := by ext; simp [mem_initializationStages]

/-- A lower-priority requirement has at least the initialization stages of a higher-priority one. -/
theorem initializationStages_mono (action : ℕ → Option ℕ) :
    Monotone (initializationStages action) :=
  fun _ _ hde _ ⟨s, i, ht, hs, hi⟩ => ⟨s, i, ht, hs, hi.trans_le hde⟩

/-- Stepping from priority `e` to `e + 1` adds the attention stages of `e`. -/
theorem initializationStages_succ (action : ℕ → Option ℕ) (e : ℕ) :
    initializationStages action (e + 1) =
      initializationStages action e ∪ attentionStages action e := by
  ext t
  simp only [mem_initializationStages, mem_union, mem_attentionStages]
  refine ⟨fun ⟨s, i, ht, hs, hi⟩ => (Nat.lt_succ_iff_lt_or_eq.mp hi).imp
      (fun hlt => ⟨s, i, ht, hs, hlt⟩) (fun he : i = e => ⟨s, ht, he ▸ hs⟩), ?_⟩
  rintro (⟨s, i, ht, hs, hi⟩ | ⟨s, ht, hs⟩)
  · exact ⟨s, i, ht, hs, Nat.lt_succ_of_lt hi⟩
  · exact ⟨s, e, ht, hs, Nat.lt_succ_self e⟩

/-- The initialization stages of `e` are the union of the attention stages of `i < e`. -/
theorem initializationStages_eq_biUnion (action : ℕ → Option ℕ) (e : ℕ) :
    initializationStages action e = ⋃ i ∈ Finset.range e, attentionStages action i := by
  ext t
  simp only [mem_initializationStages, mem_iUnion, Finset.mem_range, mem_attentionStages]
  exact ⟨fun ⟨s, i, ht, hs, hi⟩ => ⟨i, hi, s, ht, hs⟩,
    fun ⟨i, hi, s, ht, hs⟩ => ⟨s, i, ht, hs, hi⟩⟩

/-- Initialization stages and attention stages of the same requirement are disjoint. -/
theorem disjoint_initializationStages_attentionStages (action : ℕ → Option ℕ) (e : ℕ) :
    Disjoint (initializationStages action e) (attentionStages action e) := by
  rw [initializationStages_eq_biUnion]
  exact disjoint_iUnion₂_left.mpr fun _ hi => disjoint_attentionStages (Finset.mem_range.mp hi).ne

/-- If every `i < e` receives attention finitely often, `e` is initialized finitely often. -/
theorem finite_initializationStages_of_attention {e : ℕ}
    (h : ∀ i < e, (attentionStages action i).Finite) : (initializationStages action e).Finite := by
  rw [initializationStages_eq_biUnion]
  exact (Finset.range e).finite_toSet.biUnion fun i hi => h i (Finset.mem_range.mp hi)

/-- The number of initializations of `e` sums the attention counts of `i < e`. -/
theorem ncard_initializationStages_eq_sum {e : ℕ}
    (h : ∀ i < e, (attentionStages action i).Finite) :
    (initializationStages action e).ncard =
      ∑ i ∈ Finset.range e, (attentionStages action i).ncard := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hlt : ∀ i < e, (attentionStages action i).Finite := fun i hi => h i (Nat.lt_succ_of_lt hi)
    rw [initializationStages_succ, ncard_union_eq
      (disjoint_initializationStages_attentionStages action e)
      (finite_initializationStages_of_attention hlt) (h e (Nat.lt_succ_self e)),
      ih hlt, Finset.sum_range_succ]

/-- Sending each attention stage `s + 1` after the first (`s₀ + 1`) to the latest initialization
stage below `s + 1` injects `attentionStages action e \ {s₀ + 1}` into
`initializationStages action e`. -/
private theorem exists_mapsTo_injOn_attentionStages_sdiff {e s₀ : ℕ}
    (hs₀ : action s₀ = some e) (hs₀_min : ∀ s, action s = some e → s₀ ≤ s)
    (hepoch : ∀ s₁ s₂, s₁ < s₂ → action s₁ = some e → action s₂ = some e →
      ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < e, action t = some i) :
    ∃ prev : ℕ → ℕ,
      MapsTo prev (attentionStages action e \ {s₀ + 1}) (initializationStages action e) ∧
        InjOn prev (attentionStages action e \ {s₀ + 1}) := by
  classical
  -- Map each `u` to the largest initialization stage of `e` strictly below `u`.
  let F : ℕ → Finset ℕ := fun u => (Finset.range u).filter (· ∈ initializationStages action e)
  let prev : ℕ → ℕ := fun u => (F u).sup id
  have hmemF {a b : ℕ} (hab : a < b) (ha : action a = some e) (hb : action b = some e) :
      ∃ t, a < t ∧ t + 1 ∈ F (b + 1) := by
    obtain ⟨t, hat, htb, i, hie, hti⟩ := hepoch a b hab ha hb
    exact ⟨t, hat, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_lt_succ htb),
      succ_mem_initializationStages.mpr ⟨i, hie, hti⟩⟩⟩
  -- Between `s₀` and any later action `s`, some `i < e` acts, so `F (s + 1)` is nonempty and its
  -- supremum `prev (s + 1)` is an initialization stage below `s + 1`.
  have hprev {s : ℕ} (hs : action s = some e) (hlt : s₀ < s) :
      prev (s + 1) ∈ initializationStages action e ∧ prev (s + 1) < s + 1 := by
    obtain ⟨t, -, htmem⟩ := hmemF hlt hs₀ hs
    obtain ⟨w, hw, hsup⟩ := Finset.exists_mem_eq_sup _ ⟨t + 1, htmem⟩ id
    have hpw : prev (s + 1) = w := by simpa [prev] using hsup
    rw [hpw]
    exact ⟨(Finset.mem_filter.mp hw).2, Finset.mem_range.mp (Finset.mem_filter.mp hw).1⟩
  -- An initialization stage in `(s₁ + 1, s₂ + 1)` forces `prev` to grow strictly across later
  -- actions of `e`, making `prev` injective off `s₀ + 1`.
  have hstrict {s₁ s₂ : ℕ} (hs₁ : action s₁ = some e) (hs₂ : action s₂ = some e)
      (h₀₁ : s₀ < s₁) (h₁₂ : s₁ < s₂) : prev (s₁ + 1) < prev (s₂ + 1) := by
    have hp₁ := (hprev hs₁ h₀₁).2
    obtain ⟨t, hs₁t, htmem⟩ := hmemF h₁₂ hs₁ hs₂
    have htle : t + 1 ≤ prev (s₂ + 1) := Finset.le_sup (f := id) htmem
    omega
  refine ⟨prev, fun _ ⟨hatt, hne₀⟩ => ?_, ?_⟩
  · obtain ⟨s, rfl, hs⟩ := mem_attentionStages.mp hatt
    exact (hprev hs (lt_of_le_of_ne (hs₀_min s hs) fun h => hne₀ (by simp [h]))).1
  · rintro _ ⟨hatt₁, h₁⟩ _ ⟨hatt₂, h₂⟩ heq
    obtain ⟨s₁, rfl, hs₁⟩ := mem_attentionStages.mp hatt₁
    obtain ⟨s₂, rfl, hs₂⟩ := mem_attentionStages.mp hatt₂
    have h₀₁ : s₀ < s₁ := lt_of_le_of_ne (hs₀_min s₁ hs₁) fun h => h₁ (by simp [h])
    have h₀₂ : s₀ < s₂ := lt_of_le_of_ne (hs₀_min s₂ hs₂) fun h => h₂ (by simp [h])
    rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
    · exact absurd heq (hstrict hs₁ hs₂ h₀₁ hlt).ne
    · rfl
    · exact absurd heq.symm (hstrict hs₂ hs₁ h₀₂ hgt).ne

/-- **At most one action per epoch.** If `e` is initialized finitely often and some `i < e` acts
between any two actions of `e`, then `e` acts at most `(initializationStages action e).ncard + 1`
times. -/
theorem finite_attentionStages_and_ncard_le_succ_initializationStages {e : ℕ}
    (hfin : (initializationStages action e).Finite)
    (hepoch : ∀ s₁ s₂, s₁ < s₂ → action s₁ = some e → action s₂ = some e →
      ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < e, action t = some i) :
    (attentionStages action e).Finite ∧
      (attentionStages action e).ncard ≤ (initializationStages action e).ncard + 1 := by
  classical
  by_cases hne : ∃ s, action s = some e
  · -- Separate the least action `s₀` from the later attention stages, which inject into
    -- `initializationStages action e`.
    let s₀ := Nat.find hne
    have hs₀ : action s₀ = some e := Nat.find_spec hne
    obtain ⟨prev, hmaps, hinj⟩ := exists_mapsTo_injOn_attentionStages_sdiff hs₀
      (fun _ => Nat.find_min' hne) hepoch
    have hdiff_fin := Finite.of_finite_image (hfin.subset hmaps.image_subset) hinj
    have hins := insert_sdiff_self_of_mem (mem_attentionStages.mpr ⟨s₀, rfl, hs₀⟩)
    refine ⟨hins ▸ hdiff_fin.insert (s₀ + 1), ?_⟩
    rw [← hins, ncard_insert_of_notMem (by simp) hdiff_fin, ← hinj.ncard_image]
    exact Nat.add_le_add_right (ncard_le_ncard hmaps.image_subset hfin) 1
  · have hemp : attentionStages action e = ∅ := eq_empty_iff_forall_notMem.mpr fun _ h => by
      obtain ⟨s, -, hs⟩ := mem_attentionStages.mp h
      exact hne ⟨s, hs⟩
    simp [hemp]

private theorem finite_initializationStages_and_ncard_le_of_lt {e : ℕ}
    (h : ∀ i < e, (attentionStages action i).Finite ∧ (attentionStages action i).ncard ≤ 2 ^ i) :
    (initializationStages action e).Finite ∧ (initializationStages action e).ncard ≤ 2 ^ e - 1 :=
  ⟨finite_initializationStages_of_attention fun i hi => (h i hi).1, by
    rw [ncard_initializationStages_eq_sum fun i hi => (h i hi).1]
    exact (Finset.sum_le_sum fun i hi => (h i (Finset.mem_range.mp hi)).2).trans_eq
      ((Nat.geomSum_eq (le_refl 2) e).trans (Nat.div_one _))⟩

/-- **Exponential attention bound.** When every requirement acts at most once per epoch, priority
`e` receives attention at most `2 ^ e` times. -/
theorem finite_attentionStages_and_ncard_le_two_pow
    (hepoch : ∀ e s₁ s₂, s₁ < s₂ → action s₁ = some e → action s₂ = some e →
      ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < e, action t = some i) (e : ℕ) :
    (attentionStages action e).Finite ∧ (attentionStages action e).ncard ≤ 2 ^ e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    obtain ⟨hinit_fin, hinit_le⟩ := finite_initializationStages_and_ncard_le_of_lt ih
    obtain ⟨hfin, hle⟩ :=
      finite_attentionStages_and_ncard_le_succ_initializationStages hinit_fin (hepoch e)
    have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    exact ⟨hfin, by omega⟩

/-- **Initialization bound `2 ^ e - 1`.** When every requirement acts at most once per epoch,
priority `e` is initialized at most `2 ^ e - 1` times. -/
theorem finite_initializationStages_and_ncard_le
    (hepoch : ∀ e s₁ s₂, s₁ < s₂ → action s₁ = some e → action s₂ = some e →
      ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < e, action t = some i) (e : ℕ) :
    (initializationStages action e).Finite ∧ (initializationStages action e).ncard ≤ 2 ^ e - 1 :=
  finite_initializationStages_and_ncard_le_of_lt fun i _ =>
    finite_attentionStages_and_ncard_le_two_pow hepoch i

end TauCeti.Priority
