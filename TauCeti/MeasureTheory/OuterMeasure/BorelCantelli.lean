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
For metric-valued functions, summable bounds on consecutive distances outside events of
summable measure imply that almost every pointwise sequence is Cauchy.

Similarly, if the deviation sets `{x | ε ≤ dist (X n x) (Y x)}` of a sequence of functions into a
pseudometric space have summable outer measure for every `ε > 0`, applying Borel--Cantelli along
radii `(j + 1)⁻¹` gives almost-everywhere convergence `X n x → Y x`, in particular whenever the
tail measures are bounded by `ENNReal.ofReal (v n / ε ^ 2)` for a summable sequence `v`.

## Main statements

* `TauCeti.MeasureTheory.ae_eventually_mem_iff_mem_liminf`
* `TauCeti.MeasureTheory.ae_cauchySeq_of_summable_of_tsum_measure_dist_gt_ne_top`
* `TauCeti.MeasureTheory.ae_tendsto_of_tsum_measure_ge_ne_top`
* `TauCeti.MeasureTheory.ae_tendsto_of_measure_ge_le_ofReal_div_sq`
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

/-- If for every `ε > 0` the deviation sets `{x | ε ≤ dist (X n x) (Y x)}` have summable outer
measure, then `X n x` converges to `Y x` as `n → ∞` for `μ`-almost every `x`. -/
theorem ae_tendsto_of_tsum_measure_ge_ne_top {E : Type*} [PseudoMetricSpace E] {X : ℕ → α → E}
    {Y : α → E} (h : ∀ ε > 0, (∑' n, μ {x | ε ≤ dist (X n x) (Y x)}) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ X n x) atTop (𝓝 (Y x)) := by
  have hbc (j : ℕ) : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, dist (X n x) (Y x) < (j + 1 : ℝ)⁻¹ := by
    simpa only [mem_ofPred_eq, not_le] using ae_eventually_notMem (h _ (inv_pos.2 (by positivity)))
  filter_upwards [ae_all_iff.2 hbc] with x hx
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hx j] with n hn
  exact hn.trans (by simpa only [one_div] using hj)

/-- If the deviation tails `μ {x | ε ≤ dist (X n x) (Y x)}` are bounded by
`ENNReal.ofReal (v n / ε ^ 2)` for a summable real sequence `v`, then `X n x` converges to `Y x`
for `μ`-almost every `x`. -/
theorem ae_tendsto_of_measure_ge_le_ofReal_div_sq {E : Type*} [PseudoMetricSpace E]
    {X : ℕ → α → E} {Y : α → E} {v : ℕ → ℝ} (hv : Summable v)
    (h : ∀ (n : ℕ) {ε : ℝ}, 0 < ε →
      μ {x | ε ≤ dist (X n x) (Y x)} ≤ ENNReal.ofReal (v n / ε ^ 2)) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ X n x) atTop (𝓝 (Y x)) :=
  ae_tendsto_of_tsum_measure_ge_ne_top fun ε hε ↦
    ne_top_of_le_ne_top (hv.div_const (ε ^ 2)).tsum_ofReal_ne_top
      (tsum_le_tsum fun n ↦ h n hε)

end TauCeti.MeasureTheory
