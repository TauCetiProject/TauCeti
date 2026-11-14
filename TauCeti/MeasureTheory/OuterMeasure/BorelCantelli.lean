/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Sequences of sets with summable consecutive symmetric differences and Borel--Cantelli limits

If consecutive sets of a sequence differ by sets of summable measure, the Borel--Cantelli lemma
shows that almost every point eventually stays inside the sets or eventually stays outside them.
Membership in the sets therefore converges almost everywhere to membership in their `liminf`.
This turns a sequence of approximate constructions whose corrections have summable mass into a
limiting set, as in the allocation of disjoint sets of prescribed mass in a laminar family.

Similarly, if for every positive threshold `ε > 0` the deviation sets `{x | ε ≤ dist (f n x) (a x)}`
have summable outer measure, Borel--Cantelli along the countable sequence `ε = (k + 1)⁻¹` yields
almost-everywhere convergence `f n x → a x`.

## Main statements

* `TauCeti.MeasureTheory.ae_eventually_mem_iff_mem_liminf`
* `TauCeti.MeasureTheory.ae_tendsto_of_tsum_measure_ge_ne_top`
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal symmDiff Topology

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

/-- **Borel--Cantelli criterion for almost-everywhere convergence.** If for every `ε > 0` the
deviation sets `{x | ε ≤ dist (f n x) (a x)}` have summable outer measure, then `f n x → a x`
almost everywhere. No measurability assumptions on `f` or `a` are required. -/
theorem ae_tendsto_of_tsum_measure_ge_ne_top {β : Type*} [PseudoMetricSpace β]
    {f : ℕ → α → β} {a : α → β}
    (h : ∀ {ε : ℝ}, 0 < ε → ∑' n, μ {x | ε ≤ dist (f n x) (a x)} ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (a x)) := by
  have hbc (k : ℕ) : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, dist (f n x) (a x) < (k + 1 : ℝ)⁻¹ := by
    simpa only [mem_ofPred_eq, not_le] using
      ae_eventually_notMem (h (inv_pos.mpr (by positivity)))
  filter_upwards [ae_all_iff.2 hbc] with x hx
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hx k] with n hn
  exact hn.trans (by simpa only [one_div] using hk)

end TauCeti.MeasureTheory
