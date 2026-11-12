/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Filter.EventuallyConst

/-!
# Sequences of sets with summable consecutive symmetric differences

If consecutive sets of a sequence differ by sets of summable measure, the Borel--Cantelli lemma
shows that almost every point eventually stays inside the sets or eventually stays outside them.
Membership in the sets therefore converges almost everywhere to membership in their `liminf`.
This turns a sequence of approximate constructions whose corrections have summable mass into a
limiting set, as in the allocation of disjoint sets of prescribed mass in a laminar family.

## Main statements

* `TauCeti.MeasureTheory.ae_eventually_mem_iff_mem_liminf`
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal symmDiff

namespace TauCeti.MeasureTheory

variable {α F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F}

/-- If consecutive sets of a sequence differ by sets of summable measure, then for almost every
point, membership in the sets is eventually the same as membership in their `liminf`. -/
theorem ae_eventually_mem_iff_mem_liminf {s : ℕ → Set α}
    (hs : ∑' n, μ (s (n + 1) ∆ s n) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ s n ↔ x ∈ liminf s atTop := by
  filter_upwards [ae_eventually_notMem hs] with x hx
  obtain ⟨N, hN⟩ := eventuallyConst_atTop.1 <| (eventuallyConst_atTop_nat (f := (x ∈ s ·))).2 <|
    (eventually_atTop.1 hx).imp fun N hN n hn ↦ propext <| by
      have := hN n hn
      rw [mem_symmDiff] at this
      tauto
  have hconst (n : ℕ) (hn : N ≤ n) : x ∈ s n ↔ x ∈ s N := Iff.of_eq (hN n hn)
  have hlim : x ∈ liminf s atTop ↔ x ∈ s N := by
    rw [mem_liminf_iff_eventually_mem]
    refine ⟨fun h ↦ ?_, fun h ↦ eventually_atTop.2 ⟨N, fun n hn ↦ (hconst n hn).2 h⟩⟩
    obtain ⟨M, hM⟩ := eventually_atTop.1 h
    exact (hconst (max M N) (le_max_right M N)).1 (hM _ (le_max_left M N))
  exact eventually_atTop.2 ⟨N, fun n hn ↦ (hconst n hn).trans hlim.symm⟩

end TauCeti.MeasureTheory
