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

In a priority schedule `action : ℕ → Option ℕ`, an action of a higher-priority requirement `i < e`
at stage `s` initializes requirement `e` in the transition to stage `s + 1`. The set
`initializationStages action e` collects these run indices `s + 1`; it is the disjoint union of
`attentionStages action i` over `i < e`.

The intervals between consecutive elements of `initializationStages action e` are the **epochs** of
requirement `e`. When `e` can act at most once in each epoch — between any two actions of `e` some
higher-priority requirement `i < e` acts — every action of `e` after its first is preceded by a
distinct initialization stage of `e`. Hence `e` acts at most `(initializationStages action e).ncard
+ 1` times. Applying this bound inductively across all priorities yields the classical finite-injury
attention and initialization budgets `2 ^ e` and `2 ^ e - 1` of the original Friedberg–Muchnik
method, without assuming effective bounds or auxiliary bookkeeping stages.

## Main definitions

* `TauCeti.Priority.initializationStages`: the run indices `s + 1` at which some requirement `i < e`
  acted at stage `s`.

## Main results

* `TauCeti.Priority.initializationStages_eq_biUnion`,
  `TauCeti.Priority.ncard_initializationStages_eq_sum`: `initializationStages action e` is the
  disjoint union of `attentionStages action i` for `i < e`, and its cardinality sums theirs.
* `TauCeti.Priority.finite_attentionStages_and_ncard_le_succ_initializationStages`: if `e` acts at
  most once between actions of priority `< e` and its initialization stages are finite, then
  `attentionStages action e` is finite of cardinality at most
  `(initializationStages action e).ncard + 1`.
* `TauCeti.Priority.finite_attentionStages_and_ncard_le_two_pow`,
  `TauCeti.Priority.finite_initializationStages_and_ncard_le`: when every requirement acts at most
  once per epoch, priority `e` receives attention at most `2 ^ e` times and is initialized at most
  `2 ^ e - 1` times.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters VII.1 and VII.2.
-/

public section

open Set

namespace TauCeti.Priority

variable {action : ℕ → Option ℕ}

/-- The run indices `s + 1` at which some higher-priority requirement `i < e` acted at stage `s`,
initializing requirement `e`. -/
def initializationStages (action : ℕ → Option ℕ) (e : ℕ) : Set ℕ :=
  {t | ∃ s i, t = s + 1 ∧ action s = some i ∧ i < e}

/-- Membership in `initializationStages`. -/
theorem mem_initializationStages {e t : ℕ} :
    t ∈ initializationStages action e ↔ ∃ s i, t = s + 1 ∧ action s = some i ∧ i < e :=
  Iff.rfl

/-- `s + 1` is an initialization stage of `e` exactly when some `i < e` acts at stage `s`. -/
@[simp]
theorem succ_mem_initializationStages {e s : ℕ} :
    s + 1 ∈ initializationStages action e ↔ ∃ i < e, action s = some i := by
  simp [initializationStages, and_comm]

/-- Stage `0` is never an initialization stage. -/
@[simp]
theorem zero_notMem_initializationStages {e : ℕ} : 0 ∉ initializationStages action e := by
  simp [initializationStages]

/-- Priority `0` has no higher-priority requirements and is never initialized. -/
@[simp]
theorem initializationStages_zero (action : ℕ → Option ℕ) : initializationStages action 0 = ∅ := by
  ext t
  simp [mem_initializationStages]

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
  constructor
  · rintro ⟨s, i, rfl, hs, hi⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact Or.inl ⟨s, i, rfl, hs, hlt⟩
    · exact Or.inr ⟨s, rfl, hs⟩
  · rintro (⟨s, i, rfl, hs, hi⟩ | ⟨s, rfl, hs⟩)
    · exact ⟨s, i, rfl, hs, Nat.lt_succ_of_lt hi⟩
    · exact ⟨s, e, rfl, hs, Nat.lt_succ_self e⟩

/-- The initialization stages of `e` are the union of the attention stages of `i < e`. -/
theorem initializationStages_eq_biUnion (action : ℕ → Option ℕ) (e : ℕ) :
    initializationStages action e = ⋃ i ∈ Finset.range e, attentionStages action i := by
  ext t
  simp only [mem_initializationStages, mem_iUnion, Finset.mem_range, mem_attentionStages]
  constructor
  · rintro ⟨s, i, rfl, hs, hi⟩
    exact ⟨i, hi, s, rfl, hs⟩
  · rintro ⟨i, hi, s, rfl, hs⟩
    exact ⟨s, i, rfl, hs, hi⟩

/-- Distinct requirements have disjoint attention stages, since `action s` selects at most one
priority per stage. -/
theorem disjoint_attentionStages {d e : ℕ} (h : d ≠ e) :
    Disjoint (attentionStages action d) (attentionStages action e) := by
  refine disjoint_left.mpr fun _ hd he => ?_
  obtain ⟨s, rfl, hsd⟩ := mem_attentionStages.mp hd
  obtain ⟨t, ht, hte⟩ := mem_attentionStages.mp he
  obtain rfl : s = t := Nat.succ.inj ht
  exact h (Option.some.inj (hsd.symm.trans hte))

/-- Initialization stages and attention stages of the same requirement are disjoint. -/
theorem disjoint_initializationStages_attentionStages (action : ℕ → Option ℕ) (e : ℕ) :
    Disjoint (initializationStages action e) (attentionStages action e) := by
  refine disjoint_left.mpr fun _ hinit hatt => ?_
  obtain ⟨s, i, rfl, hs, hi⟩ := hinit
  obtain ⟨t, ht, he⟩ := mem_attentionStages.mp hatt
  obtain rfl : s = t := Nat.succ.inj ht
  exact hi.ne (Option.some.inj (hs.symm.trans he))

/-- If every higher-priority requirement receives attention finitely often, requirement `e` is
initialized finitely often. -/
theorem finite_initializationStages_of_attention {e : ℕ}
    (h : ∀ i < e, (attentionStages action i).Finite) :
    (initializationStages action e).Finite := by
  rw [initializationStages_eq_biUnion]
  exact (Finset.range e).finite_toSet.biUnion fun i hi => h i (Finset.mem_range.mp hi)

/-- Because at most one requirement acts at each stage, the number of initializations of `e` is the
sum of the attention counts of `i < e`. -/
theorem ncard_initializationStages_eq_sum {e : ℕ}
    (h : ∀ i < e, (attentionStages action i).Finite) :
    (initializationStages action e).ncard =
      ∑ i ∈ Finset.range e, (attentionStages action i).ncard := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hlt : ∀ i < e, (attentionStages action i).Finite :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    rw [initializationStages_succ,
      ncard_union_eq (disjoint_initializationStages_attentionStages action e)
        (finite_initializationStages_of_attention hlt) (h e (Nat.lt_succ_self e)),
      ih hlt, Finset.sum_range_succ]

/-- **At most one action per epoch.** Suppose requirement `e` is initialized finitely often and
between any two stages at which `e` acts some higher-priority requirement `i < e` acts. Then `e`
receives attention finitely often, and at most `(initializationStages action e).ncard + 1` times. -/
theorem finite_attentionStages_and_ncard_le_succ_initializationStages {e : ℕ}
    (hfin : (initializationStages action e).Finite)
    (hepoch : ∀ s₁ s₂, s₁ < s₂ → action s₁ = some e → action s₂ = some e →
      ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < e, action t = some i) :
    (attentionStages action e).Finite ∧
      (attentionStages action e).ncard ≤ (initializationStages action e).ncard + 1 := by
  classical
  by_cases hne : ∃ s, action s = some e
  · -- `s₀` is the first stage at which `e` acts; every later action of `e` is preceded by a
    -- greatest initialization stage `prev u < u`, injecting `attentionStages \ {s₀ + 1}` into
    -- `initializationStages`.
    let s₀ := Nat.find hne
    have hs₀ : action s₀ = some e := Nat.find_spec hne
    have hs₀_min : ∀ s, action s = some e → s₀ ≤ s := fun s hs => Nat.find_min' hne hs
    let F : ℕ → Finset ℕ := fun u => (Finset.range u).filter (· ∈ initializationStages action e)
    let prev : ℕ → ℕ := fun u => (F u).sup id
    have hprev_mem {s : ℕ} (hs : action s = some e) (hlt : s₀ < s) :
        prev (s + 1) ∈ initializationStages action e ∧ prev (s + 1) < s + 1 := by
      obtain ⟨t, hts₀, hts, i, hie, hti⟩ := hepoch s₀ s hlt hs₀ hs
      have htmem : t + 1 ∈ F (s + 1) := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.succ_lt_succ hts),
          succ_mem_initializationStages.mpr ⟨i, hie, hti⟩⟩
      obtain ⟨w, hw, hsup⟩ := Finset.exists_mem_eq_sup _ ⟨t + 1, htmem⟩ id
      have hp : prev (s + 1) = w := hsup
      rw [hp]
      exact ⟨(Finset.mem_filter.mp hw).2, Finset.mem_range.mp (Finset.mem_filter.mp hw).1⟩
    have hmaps : MapsTo prev (attentionStages action e \ {s₀ + 1})
        (initializationStages action e) := by
      rintro u ⟨hatt, hne₀⟩
      obtain ⟨s, rfl, hs⟩ := mem_attentionStages.mp hatt
      have hne_s : s ≠ s₀ := fun h => hne₀ (by simp [h])
      exact (hprev_mem hs (lt_of_le_of_ne (hs₀_min s hs) hne_s.symm)).1
    have hstrict {s₁ s₂ : ℕ} (hs₁ : action s₁ = some e) (hs₂ : action s₂ = some e)
        (h₀₁ : s₀ < s₁) (h₁₂ : s₁ < s₂) : prev (s₁ + 1) < prev (s₂ + 1) := by
      have hp₁ := (hprev_mem hs₁ h₀₁).2
      obtain ⟨t, hs₁t, hts₂, i, hie, hti⟩ := hepoch s₁ s₂ h₁₂ hs₁ hs₂
      have htmem : t + 1 ∈ F (s₂ + 1) := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.succ_lt_succ hts₂),
          succ_mem_initializationStages.mpr ⟨i, hie, hti⟩⟩
      have htle : t + 1 ≤ prev (s₂ + 1) := Finset.le_sup (f := id) htmem
      omega
    have hinj : InjOn prev (attentionStages action e \ {s₀ + 1}) := by
      rintro _ ⟨hatt₁, h₁⟩ _ ⟨hatt₂, h₂⟩ heq
      obtain ⟨s₁, rfl, hs₁⟩ := mem_attentionStages.mp hatt₁
      obtain ⟨s₂, rfl, hs₂⟩ := mem_attentionStages.mp hatt₂
      have h₀₁ : s₀ < s₁ := lt_of_le_of_ne (hs₀_min s₁ hs₁) (fun h => h₁ (by simp [h]))
      have h₀₂ : s₀ < s₂ := lt_of_le_of_ne (hs₀_min s₂ hs₂) (fun h => h₂ (by simp [h]))
      rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
      · exact absurd heq (hstrict hs₁ hs₂ h₀₁ hlt).ne
      · rfl
      · exact absurd heq.symm (hstrict hs₂ hs₁ h₀₂ hgt).ne
    have hdiff_fin : (attentionStages action e \ {s₀ + 1}).Finite :=
      Finite.of_finite_image (hfin.subset hmaps.image_subset) hinj
    have hinsert : insert (s₀ + 1) (attentionStages action e \ {s₀ + 1}) =
        attentionStages action e :=
      insert_sdiff_self_of_mem (mem_attentionStages.mpr ⟨s₀, rfl, hs₀⟩)
    have hatt_fin : (attentionStages action e).Finite := hinsert ▸ hdiff_fin.insert (s₀ + 1)
    have hnotMem : s₀ + 1 ∉ attentionStages action e \ {s₀ + 1} := by simp
    refine ⟨hatt_fin, ?_⟩
    rw [← hinsert, ncard_insert_of_notMem hnotMem hdiff_fin, ← hinj.ncard_image]
    exact Nat.add_le_add_right (ncard_le_ncard hmaps.image_subset hfin) 1
  · have hemp : attentionStages action e = ∅ := by
      ext t
      simp only [mem_attentionStages, mem_empty_iff_false, iff_false]
      rintro ⟨s, -, hs⟩
      exact hne ⟨s, hs⟩
    simp [hemp]

/-- **Exponential attention bound.** If every requirement acts at most once between actions of
higher-priority requirements, then requirement `e` receives attention finitely often and at most
`2 ^ e` times. -/
theorem finite_attentionStages_and_ncard_le_two_pow
    (hepoch : ∀ e s₁ s₂, s₁ < s₂ → action s₁ = some e → action s₂ = some e →
      ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < e, action t = some i) (e : ℕ) :
    (attentionStages action e).Finite ∧ (attentionStages action e).ncard ≤ 2 ^ e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    have hlt_fin : ∀ i < e, (attentionStages action i).Finite := fun i hi => (ih i hi).1
    have hinit_fin := finite_initializationStages_of_attention hlt_fin
    obtain ⟨hfin, hle⟩ :=
      finite_attentionStages_and_ncard_le_succ_initializationStages hinit_fin (hepoch e)
    refine ⟨hfin, hle.trans ?_⟩
    rw [ncard_initializationStages_eq_sum hlt_fin]
    have hsum : ∑ i ∈ Finset.range e, (attentionStages action i).ncard ≤ 2 ^ e - 1 :=
      (Finset.sum_le_sum fun i hi => (ih i (Finset.mem_range.mp hi)).2).trans_eq
        (by simpa using Nat.geomSum_eq (le_refl 2) e)
    have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega

/-- **Initialization bound `2 ^ e - 1`.** If every requirement acts at most once between actions of
higher-priority requirements, then requirement `e` is initialized finitely often and at most
`2 ^ e - 1` times. -/
theorem finite_initializationStages_and_ncard_le
    (hepoch : ∀ e s₁ s₂, s₁ < s₂ → action s₁ = some e → action s₂ = some e →
      ∃ t, s₁ < t ∧ t < s₂ ∧ ∃ i < e, action t = some i) (e : ℕ) :
    (initializationStages action e).Finite ∧
      (initializationStages action e).ncard ≤ 2 ^ e - 1 := by
  have hatt := fun i (_ : i < e) => finite_attentionStages_and_ncard_le_two_pow hepoch i
  refine ⟨finite_initializationStages_of_attention fun i hi => (hatt i hi).1, ?_⟩
  rw [ncard_initializationStages_eq_sum fun i hi => (hatt i hi).1]
  exact (Finset.sum_le_sum fun i hi => (hatt i (Finset.mem_range.mp hi)).2).trans_eq
    (by simpa using Nat.geomSum_eq (le_refl 2) e)

end TauCeti.Priority
