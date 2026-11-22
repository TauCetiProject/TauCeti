/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Function.Lp.CompactlySupported
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Pointwise behaviour of infinite sums in `Lᵖ`

If a family `u` in `Lᵖ` has sum `v` in the `Lᵖ` norm, then `‖v x‖ₑ ≤ ∑' i, ‖u i x‖ₑ` at almost
every point. Unlike `MeasureTheory.Lp.hasSum_coeFn_tsum`, this needs neither a countable index
type nor summability of the norms `‖u i‖`: it only uses that some sequence of finite partial sums
converges to `v` almost everywhere. A typical use is a sum of functions with disjoint supports in
`L²`, whose norms are square-summable but need not be summable.

For a countable family of compactly supported continuous functions whose `Lᵖ` classes sum to `v`
with summable `Lᵖ` norms, the pointwise values `ψ i t` have sum `v t` and are norm-summable for
almost every `t` (`CompactlySupportedContinuousMap.ae_hasSum_of_hasSum_toLp`).

Also records `TauCeti.integrable_tsum_of_summable_integral_norm`, showing that a countable
pointwise `tsum` of integrable functions with summable `L¹` norms is integrable.

## Main declarations

* `MeasureTheory.Lp.ae_enorm_le_tsum_enorm_of_hasSum`: the pointwise bound.
* `MeasureTheory.Lp.ae_eq_of_hasSum_of_ae_hasSum`: for a countable family, the sum in `Lᵖ`
  agrees almost everywhere with the pointwise sum, wherever the latter exists.
* `CompactlySupportedContinuousMap.ae_hasSum_of_hasSum_toLp`: almost-everywhere absolute series
  convergence for representatives of a norm-summable `Lᵖ` series in `C_c(X, E)`.
* `TauCeti.integrable_tsum_of_summable_integral_norm`: a countable pointwise `tsum` of integrable
  functions with summable `L¹` norms is integrable.
-/

public section

open Filter
open scoped CompactlySupported ENNReal Topology

namespace MeasureTheory

namespace Lp

variable {α E κ : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If a family `u` in `Lᵖ` has sum `v`, then at almost every point the extended norm of `v` is at
most the sum of the extended norms of the `u i`. -/
theorem ae_enorm_le_tsum_enorm_of_hasSum {u : κ → Lp E p μ} {v : Lp E p μ} (h : HasSum u v) :
    ∀ᵐ x ∂μ, ‖v x‖ₑ ≤ ∑' i, ‖u i x‖ₑ := by
  -- A summable family in the metric space `Lᵖ` has countable support, so we may sum over it.
  have := h.summable.countable_support.to_subtype
  obtain ⟨S, -, hS⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hasSum_subtype_support.2 h)).exists_seq_tendsto_ae'
  have hsum : ∀ᵐ x ∂μ, ∀ n, (⇑(∑ i ∈ S n, u i) : α → E) x = ∑ i ∈ S n, u i x :=
    ae_all_iff.2 fun n => coeFn_fun_finsetSum (S n) _
  filter_upwards [hS, hsum] with x hx hxsum
  refine le_of_tendsto' (continuous_eNorm.tendsto _ |>.comp hx) fun n => ?_
  simp only [Function.comp_apply, hxsum n]
  exact (eNorm_sum_le _ _).trans <| (_root_.sum_le_tsum _).trans <|
    tsum_comp_le_tsum_of_injective Subtype.val_injective fun i => ‖u i x‖ₑ

/-- If a countable family `u` in `Lᵖ` has sum `v`, and at almost every point the values `u i x`
have sum `g x`, then `v = g` almost everywhere: the `Lᵖ` sum agrees with the pointwise sum. -/
theorem ae_eq_of_hasSum_of_ae_hasSum [Countable κ] {u : κ → Lp E p μ} {v : Lp E p μ}
    {g : α → E} (h : HasSum u v) (hg : ∀ᵐ x ∂μ, HasSum (fun i ↦ u i x) (g x)) :
    v =ᵐ[μ] g := by
  obtain ⟨S, hS, hSv⟩ := (tendstoInMeasure_of_tendsto_Lp h).exists_seq_tendsto_ae'
  have hsum : ∀ᵐ x ∂μ, ∀ n, (⇑(∑ i ∈ S n, u i) : α → E) x = ∑ i ∈ S n, u i x :=
    ae_all_iff.2 fun n => coeFn_fun_finsetSum (S n) _
  filter_upwards [hSv, hsum, hg] with x hx hxsum hgx
  simp only [hxsum] at hx
  exact tendsto_nhds_unique hx (hgx.comp hS)

end Lp

end MeasureTheory

namespace CompactlySupportedContinuousMap

open MeasureTheory

open Topology in
private theorem hasSum_of_tendsto_subseq_of_summable_norm {E ι : Type*} [NormedAddCommGroup E]
    {x : ι → E} {v : E} (hx : Summable fun i => ‖x i‖) {S : ℕ → Finset ι}
    (hS : Tendsto S atTop atTop) (ht : Tendsto (fun n => ∑ i ∈ S n, x i) atTop (𝓝 v)) :
    HasSum x v := by
  classical
  change Tendsto (fun s : Finset ι => ∑ b ∈ s, x b) atTop (𝓝 v)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s₀, hs₀⟩ := Metric.tendsto_atTop.1 hx.hasSum (ε / 4) (by positivity)
  have hdiff (t : Finset ι) (ht' : s₀ ⊆ t) : ‖∑ i ∈ t, x i - ∑ i ∈ s₀, x i‖ < ε / 4 := by
    rw [← Finset.sum_sdiff ht', add_sub_cancel_right]
    refine (norm_sum_le _ _).trans_lt ?_
    have hle : ∑ i ∈ t \ s₀, ‖x i‖ ≤ (∑' i, ‖x i‖) - ∑ i ∈ s₀, ‖x i‖ := by
      linarith [Finset.sum_sdiff ht' (f := fun i => ‖x i‖),
        hx.sum_le_tsum t fun _ _ => norm_nonneg _]
    have hs := hs₀ s₀ Finset.Subset.rfl
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2
      (hx.sum_le_tsum s₀ fun _ _ => norm_nonneg _))] at hs
    linarith
  obtain ⟨N, hSN, hNt⟩ := ((hS.eventually (eventually_ge_atTop s₀)).and
    (ht.eventually (Metric.ball_mem_nhds v (ε := ε / 2) (by positivity)))).exists
  refine ⟨s₀, fun s hs => ?_⟩
  rw [dist_eq_norm]
  have h1 := hdiff s hs
  have h2 := hdiff (S N) hSN
  have h3 : ‖∑ i ∈ S N, x i - v‖ < ε / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hNt
  have htri : ‖∑ i ∈ s, x i - v‖ ≤
      ‖∑ i ∈ s, x i - ∑ i ∈ s₀, x i‖ + ‖∑ i ∈ S N, x i - ∑ i ∈ s₀, x i‖ +
        ‖∑ i ∈ S N, x i - v‖ := by
    calc ‖∑ i ∈ s, x i - v‖
        = ‖(∑ i ∈ s, x i - ∑ i ∈ s₀, x i) - (∑ i ∈ S N, x i - ∑ i ∈ s₀, x i) +
            (∑ i ∈ S N, x i - v)‖ := by abel_nf
      _ ≤ ‖(∑ i ∈ s, x i - ∑ i ∈ s₀, x i) - (∑ i ∈ S N, x i - ∑ i ∈ s₀, x i)‖ +
            ‖∑ i ∈ S N, x i - v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
  linarith

open Topology in
/-- If a countable family of compactly supported continuous functions has sum `v` in `Lᵖ` with
summable `Lᵖ` norms, then at almost every point `t` the pointwise series `ψ i t` converges
absolutely to `v t`. -/
theorem ae_hasSum_of_hasSum_toLp {X E ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    [Countable ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] {ψ : ι → C_c(X, E)} {v : Lp E p μ}
    (hsum : HasSum (fun i => toLp p μ 𝕜 (ψ i)) v)
    (hnorm : Summable fun i => ‖toLp p μ 𝕜 (ψ i)‖) :
    ∀ᵐ t ∂μ, HasSum (fun i => ψ i t) (v t) ∧ Summable fun i => ‖ψ i t‖ := by
  have heNorm : ∑' i, ‖toLp p μ 𝕜 (ψ i)‖ₑ ≠ ∞ :=
    tsum_eNorm_ne_top_iff_summable_norm.2 hnorm
  obtain ⟨S, hS, hSv⟩ := (tendstoInMeasure_of_tendsto_Lp hsum).exists_seq_tendsto_ae'
  have hfin : ∀ᵐ t ∂μ, ∀ n, (⇑(∑ i ∈ S n, toLp p μ 𝕜 (ψ i)) : X → E) t =
      ∑ i ∈ S n, toLp p μ 𝕜 (ψ i) t :=
    ae_all_iff.2 fun n => Lp.coeFn_fun_finsetSum (S n) _
  filter_upwards [hSv, hfin,
    summable_norm_of_tsum_eLpNorm_ne_top Fact.out (by simpa [Lp.eNorm_def] using heNorm),
    ae_all_iff.2 fun i => (coeFn_toLp (p := p) (μ := μ) 𝕜 (ψ i)).mono fun _ h => h]
    with t ht hft hnt hcoe
  simp only [hft, hcoe] at ht
  have hnt' : Summable fun i => ‖ψ i t‖ := by simpa only [hcoe] using hnt
  exact ⟨hasSum_of_tendsto_subseq_of_summable_norm hnt' hS ht, hnt'⟩

end CompactlySupportedContinuousMap

namespace TauCeti

open MeasureTheory

/-- If `F i` are integrable over a countable index type `ι` and `∑' i, ∫ x, ‖F i x‖ ∂μ < ∞`,
then the pointwise `tsum` is integrable. This pairs with
`MeasureTheory.hasSum_integral_of_summable_integral_norm`. -/
theorem integrable_tsum_of_summable_integral_norm {α ι E : Type*} [MeasurableSpace α]
    {μ : Measure α} [Countable ι] [NormedAddCommGroup E] [CompleteSpace E] {F : ι → α → E}
    (hF_int : ∀ i, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ x, ‖F i x‖ ∂μ) :
    Integrable (fun x ↦ ∑' i, F i x) μ := by
  have heNorm : ∑' i, ‖(hF_int i).toL1 (F i)‖ₑ ≠ ∞ :=
    tsum_eNorm_ne_top_iff_summable_norm.2 <| by
      simpa only [L1.norm_of_fun_eq_integral_norm (hF_int _)] using hF_sum
  refine (L1.integrable_coeFn (∑' i, (hF_int i).toL1 (F i))).congr ?_
  filter_upwards [Lp.coeFn_tsum heNorm,
    ae_all_iff.2 fun i ↦ (hF_int i).coeFn_toL1] with x hx hcoe
  exact hx.trans (tsum_congr fun i ↦ hcoe i)

end TauCeti
