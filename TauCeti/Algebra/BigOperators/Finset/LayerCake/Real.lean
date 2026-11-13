/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.NormNum

/-!
# Finite real layer cakes

A finite collection of nonnegative real numbers admits a common layer-cake decomposition:
each value is the sum of the widths of the layers below it. The coefficients are supported
at nonnegative breakpoints and are nonnegative. The same coefficients express the distance
between two values as the weighted number of levels separating them.

These finite identities turn sums of nonnegative functions and their translation distances
into weighted sums of cardinalities of superlevel sets, without integration.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, proof of Proposition G.5.2.
-/

public section

open Finset

namespace Finset

/-- A finite set of nonnegative real values has a common finite layer-cake decomposition.
The coefficient at a breakpoint is the width up to the next value. Every breakpoint lies
below a value in the given set and is either zero or itself one of the given values. -/
theorem exists_finsupp_sum_ite_lt_eq (s : Finset ℝ) (hs : ∀ a ∈ s, 0 ≤ a) :
    ∃ w : ℝ →₀ ℝ, 0 ≤ w ∧
      (∀ t ∈ w.support, 0 ≤ t ∧ t ∈ insert 0 s ∧ ∃ a ∈ s, t < a) ∧
      ∀ a ∈ s, w.sum (fun t c => if t < a then c else 0) = a := by
  classical
  induction s using Finset.induction_on_max with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | insert a s hmax ih =>
    have ha : 0 ≤ a := hs a (mem_insert_self _ _)
    obtain ⟨w, hw, hws, hwe⟩ := ih (fun b hb => hs b (mem_insert_of_mem hb))
    rcases s.eq_empty_or_nonempty with rfl | hne
    · by_cases ha0 : a = 0
      · subst a
        exact ⟨0, by simp, by simp, by simp⟩
      · refine ⟨Finsupp.single 0 a, fun t => (Finsupp.single_nonneg.2 ha) t, ?_, ?_⟩
        · intro t ht
          have ht0 : t = 0 := ((Finsupp.mem_support_single _ _ _).1 ht).1
          subst t
          exact ⟨le_refl _, by simp, a, mem_singleton_self _,
            lt_of_le_of_ne ha (Ne.symm ha0)⟩
        · simp [lt_of_le_of_ne ha (Ne.symm ha0)]
    · let b := s.max' hne
      have hb : b ∈ s := s.max'_mem hne
      have hba : b < a := hmax b hb
      have hb0 : 0 ≤ b := hs b (mem_insert_of_mem hb)
      have hwb (t : ℝ) (ht : t ∈ w.support) : t < b := by
        obtain ⟨_, _, c, hc, htc⟩ := hws t ht
        exact htc.trans_le (s.le_max' c hc)
      have hsum : w.sum (fun t c => if t < a then c else 0) = b := by
        rw [← hwe b hb]
        exact Finsupp.sum_congr fun t ht => by simp [(hwb t ht).trans hba, hwb t ht]
      refine ⟨w + Finsupp.single b (a - b), fun t =>
        add_nonneg (hw t) (Finsupp.single_nonneg.2 (sub_nonneg.2 hba.le) t), ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_union.1 (Finsupp.support_add ht) with ht | ht
        · obtain ⟨ht0, htmem, c, hc, htc⟩ := hws t ht
          exact ⟨ht0, (insert_subset_insert 0 (subset_insert a s)) htmem,
            c, mem_insert_of_mem hc, htc⟩
        · obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).1 ht
          exact ⟨hb0, mem_insert_of_mem (mem_insert_of_mem hb),
            a, mem_insert_self _ _, hba⟩
      · intro c hc
        rw [Finsupp.sum_add_index (by simp) (by intros; split_ifs <;> simp),
          Finsupp.sum_single_index (by simp)]
        rcases mem_insert.1 hc with rfl | hc
        · simp [hba, hsum]
        · have hcb : c ≤ b := s.le_max' c hc
          simp [not_lt_of_ge hcb, hwe c hc]

end Finset

namespace Finsupp

/-- With nonnegative layer widths, the distance between two layer-cake sums is the weighted
number of thresholds separating their endpoints. -/
theorem abs_sum_ite_lt_sub (w : ℝ →₀ ℝ) (hw : 0 ≤ w) (a b : ℝ) :
    |w.sum (fun t c => if t < a then c else 0) -
      w.sum (fun t c => if t < b then c else 0)| =
    w.sum (fun t c => c * |(if t < a then (1 : ℝ) else 0) -
      (if t < b then (1 : ℝ) else 0)|) := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [abs_sub_comm] using this b a (le_of_not_ge hab)
  have hle : w.sum (fun t c => if t < a then c else 0) ≤
      w.sum (fun t c => if t < b then c else 0) := by
    apply Finset.sum_le_sum
    intro t _
    dsimp
    split_ifs <;> grind [hw t]
  rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
  simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> norm_num; grind

end Finsupp
