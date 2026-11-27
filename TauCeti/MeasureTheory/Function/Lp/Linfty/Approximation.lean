/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Linfty.Sigma
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.StronglyMeasurable.CountablyValued
import TauCeti.Topology.Algebra.InfiniteSum.Basic

/-!
# Approximation in Bochner `L∞`

Finitely-valued simple functions are not norm dense in Banach-valued `L∞`: a class whose values
fill a ball of an infinite-dimensional space is not uniformly close to any function with finitely
many values. This file records the two approximation statements that replace simple-function
density at the exponent `∞`.

* In the support-restricted space `L∞_σ` (`TauCeti.linftySigma`), bounded countably-valued
  functions `∑ₙ 𝟙_{Aₙ} cₙ`, with pairwise disjoint measurable `Aₙ` of finite measure, are norm
  dense. The approximant can be chosen with `‖cₙ‖ ≤ ‖f‖` and hence with norm at most `‖f‖`
  (`TauCeti.exists_ae_eq_tsum_indicator_const_dist_lt`), and the closure of these classes is
  exactly `L∞_σ` (`TauCeti.closure_setOf_ae_eq_tsum_indicator_const`).
* In native `L∞`, simple functions approximate locally in measure: on a set of finite measure and
  outside a set of arbitrarily small measure, a simple function of finite-measure support bounded
  by `‖f‖` is uniformly close to `f`
  (`MeasureTheory.Lp.exists_simpleFunc_norm_le_measure_inter_dist_lt`).

The pointwise constructions are
`MeasureTheory.AEFinStronglyMeasurable.exists_dist_tsum_indicator_const_lt` and
`MeasureTheory.AEStronglyMeasurable.exists_simpleFunc_measure_inter_dist_lt`, applied with the
closed ball of radius `‖f‖` as the set of values.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Lemma 1.2.19 and Remarks 1.2.20–1.2.21.
-/

public section

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}

namespace TauCeti

variable [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- **Countably-valued approximation in `L∞_σ`.** Every class `f ∈ L∞_σ` is within `ε` of the
class of a countable sum `∑ₙ 𝟙_{Aₙ} cₙ` over pairwise disjoint measurable sets of finite measure,
with `‖cₙ‖ ≤ ‖f‖`. The approximating class lies in `L∞_σ` and has norm at most `‖f‖`. -/
theorem exists_ae_eq_tsum_indicator_const_dist_lt {f : Lp E ∞ μ} (hf : f ∈ linftySigma 𝕜 E μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : ℕ → Set α) (c : ℕ → E), (∀ n, MeasurableSet (A n)) ∧ (∀ n, μ (A n) < ∞) ∧
      Pairwise (Disjoint on A) ∧ (∀ n, ‖c n‖ ≤ ‖f‖) ∧
      ∃ g ∈ linftySigma 𝕜 E μ, g =ᵐ[μ] (fun x ↦ ∑' n, (A n).indicator (fun _ ↦ c n) x) ∧
        ‖g‖ ≤ ‖f‖ ∧ dist f g < ε := by
  obtain ⟨A, c, hA, hμA, hAd, hc, hae⟩ :=
    (mem_linftySigma_iff.1 hf).exists_dist_tsum_indicator_const_lt
      (K := Metric.closedBall 0 ‖f‖) ⟨0, Metric.mem_closedBall_self (norm_nonneg f)⟩
      (by simpa using Lp.ae_norm_le_norm_top f) (half_pos hε)
  simp only [mem_closedBall_zero_iff] at hc
  set G : α → E := fun x ↦ ∑' n, (A n).indicator (fun _ ↦ c n) x
  have hG : FinStronglyMeasurable G μ := finStronglyMeasurable_tsum_indicator_const hA hμA hAd c
  have hGf (x : α) : ‖G x‖ ≤ ‖f‖ := by
    by_cases hx : ∃ n, x ∈ A n
    · obtain ⟨n, hn⟩ := hx
      simpa [G, TauCeti.tsum_indicator_apply_of_mem hAd _ hn] using hc n
    · simp only [not_exists] at hx
      simp [G, indicator_of_notMem (hx _)]
  have hGmem : MemLp G ∞ μ :=
    memLp_top_of_bound hG.stronglyMeasurable.aestronglyMeasurable ‖f‖ (.of_forall hGf)
  refine ⟨A, c, hA, hμA, hAd, hc, hGmem.toLp G, ?_, hGmem.coeFn_toLp, ?_, ?_⟩
  · exact (mem_linftySigma_iff_of_ae_eq hGmem.coeFn_toLp).2 hG.aefinStronglyMeasurable
  · refine Lp.norm_le_of_ae_bound_top (norm_nonneg f) ?_
    filter_upwards [hGmem.coeFn_toLp] with x hx
    exact hx ▸ hGf x
  · refine (Lp.dist_le_of_ae_dist_le_top (half_pos hε).le ?_).trans_lt (half_lt_self hε)
    filter_upwards [hae, hGmem.coeFn_toLp] with x hx hGx
    exact hGx ▸ hx.le

/-- **Density of countably-valued functions in `L∞_σ`.** The closure in native `L∞` of the
classes of countable sums `∑ₙ 𝟙_{Aₙ} cₙ`, over pairwise disjoint measurable sets of finite
measure, is the support-restricted space `L∞_σ`. -/
theorem closure_setOf_ae_eq_tsum_indicator_const :
    closure {g : Lp E ∞ μ | ∃ (A : ℕ → Set α) (c : ℕ → E), (∀ n, MeasurableSet (A n)) ∧
      (∀ n, μ (A n) < ∞) ∧ Pairwise (Disjoint on A) ∧
      g =ᵐ[μ] fun x ↦ ∑' n, (A n).indicator (fun _ ↦ c n) x} = linftySigma 𝕜 E μ := by
  refine (closure_minimal ?_ isClosed_linftySigma).antisymm fun f hf ↦ ?_
  · rintro g ⟨A, c, hA, hμA, hAd, hg⟩
    exact (mem_linftySigma_iff_of_ae_eq hg).2
      (finStronglyMeasurable_tsum_indicator_const hA hμA hAd c).aefinStronglyMeasurable
  · refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    obtain ⟨A, c, hA, hμA, hAd, -, g, -, hg, -, hfg⟩ :=
      exists_ae_eq_tsum_indicator_const_dist_lt hf hε
    exact ⟨g, ⟨A, c, hA, hμA, hAd, hg⟩, hfg⟩

end TauCeti

namespace MeasureTheory.Lp

/-- **Local approximation by simple functions in `L∞`.** For `f ∈ L∞`, a set `B` of finite
measure, `ε > 0` and `δ > 0`, there is a simple function `φ` of finite-measure support with
`‖φ‖ ≤ ‖f‖` everywhere such that `‖f - φ‖ < ε` on `B` outside a set of measure less than `δ`. -/
theorem exists_simpleFunc_norm_le_measure_inter_dist_lt (f : Lp E ∞ μ) {B : Set α}
    (hB : μ B ≠ ∞) {ε : ℝ} (hε : 0 < ε) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ φ : SimpleFunc α E, (∀ x, ‖φ x‖ ≤ ‖f‖) ∧ μ (support φ) < ∞ ∧
      μ (B ∩ {x | ε ≤ dist (f x) (φ x)}) < δ := by
  obtain ⟨φ, hφ, hsupp, hB⟩ := (Lp.aestronglyMeasurable f).exists_simpleFunc_measure_inter_dist_lt
    (K := Metric.closedBall 0 ‖f‖) ⟨0, Metric.mem_closedBall_self (norm_nonneg f)⟩
    (by simpa using Lp.ae_norm_le_norm_top f) hB hε hδ
  refine ⟨φ, fun x ↦ ?_, hsupp, hB⟩
  rcases hφ (mem_range_self x) with h | h
  · simp [h]
  · simpa using h

end MeasureTheory.Lp
