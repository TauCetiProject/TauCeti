/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Order.Filter.EventuallyConst

/-!
# Borel--Cantelli consequences for sequences

If consecutive sets of a sequence differ by sets of summable measure, the Borel--Cantelli lemma
shows that almost every point eventually stays inside the sets or eventually stays outside them.
Membership in the sets therefore converges almost everywhere to membership in their `liminf`.
This turns a sequence of approximate constructions whose corrections have summable mass into a
limiting set, as in the allocation of disjoint sets of prescribed mass in a laminar family.

For functions into a pseudometric space, summable bounds on consecutive distances outside events of
summable measure imply that almost every pointwise sequence is Cauchy, and summability of the outer
measures of the sets `{x | ε ≤ dist (f n x) (g x)}` for every `ε > 0` implies `f n x → g x` almost
everywhere.

## Main statements

* `TauCeti.MeasureTheory.ae_eventually_mem_iff_mem_liminf`: almost-everywhere stabilization to
  `liminf` under summable consecutive symmetric differences.
* `TauCeti.MeasureTheory.ae_cauchySeq_of_summable_of_tsum_measure_dist_gt_ne_top`:
  almost-everywhere Cauchyness from summable consecutive distance bounds outside events of summable
  measure.
* `TauCeti.MeasureTheory.ae_tendsto_of_tsum_dist_ge_ne_top`: almost-everywhere convergence in a
  pseudometric space from summable deviation outer measures.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal symmDiff Topology

namespace TauCeti.MeasureTheory

variable {α F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F}

/-- If the outer measures of a sequence of sets are eventually bounded by a series with
finite sum, then almost every point eventually lies outside the sets. -/
theorem ae_eventually_notMem_of_eventually_measure_le {s : ℕ → Set α} {b : ℕ → ℝ≥0∞}
    (hb : (∑' n, b n) < ∞) (h : ∀ᶠ n in atTop, μ (s n) ≤ b n) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hs : ∑' n, μ (s (n + N)) ≠ ∞ :=
    ((tsum_le_tsum fun n ↦ hN _ (Nat.le_add_left N n)).trans
      (tsum_comp_le_tsum_of_injective (add_left_injective N) b)).trans_lt hb |>.ne
  filter_upwards [ae_eventually_notMem hs] with x hx
  rwa [← map_add_atTop_eq_nat N, eventually_map]

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

/-- If consecutive distances are bounded by a summable real sequence outside events of
summable measure, then almost every pointwise sequence is Cauchy. -/
theorem ae_cauchySeq_of_summable_of_tsum_measure_dist_gt_ne_top {E : Type*} [PseudoMetricSpace E]
    {f : ℕ → α → E} {r : ℕ → ℝ} (hr : Summable r)
    (hμ : ∑' n, μ {x | r n < dist (f n x) (f (n + 1) x)} ≠ ∞) :
    ∀ᵐ x ∂μ, CauchySeq (fun n ↦ f n x) := by
  filter_upwards [ae_eventually_notMem hμ] with x hx
  apply cauchySeq_of_summable_dist
  refine hr.of_norm_bounded_eventually_nat ?_
  filter_upwards [hx] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using not_lt.mp hn

/-- **First Borel--Cantelli criterion for almost-everywhere convergence.** In a pseudometric space,
if for every `ε > 0` the sets `{x | ε ≤ dist (f n x) (g x)}` have summable outer measure, then
`f n x → g x` almost everywhere. -/
theorem ae_tendsto_of_tsum_dist_ge_ne_top {E : Type*} [PseudoMetricSpace E]
    {f : ℕ → α → E} {g : α → E}
    (h : ∀ ⦃ε : ℝ⦄, 0 < ε → (∑' n, μ {x | ε ≤ dist (f n x) (g x)}) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  have hbc (m : ℕ) : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, dist (f n x) (g x) < (m + 1 : ℝ)⁻¹ := by
    simpa only [Set.mem_ofPred_eq, not_le] using
      ae_eventually_notMem (h (inv_pos.mpr (by positivity)))
  filter_upwards [ae_all_iff.2 hbc] with x hx
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hx m] with n hn
  exact hn.trans (by simpa only [one_div] using hm)

end TauCeti.MeasureTheory
