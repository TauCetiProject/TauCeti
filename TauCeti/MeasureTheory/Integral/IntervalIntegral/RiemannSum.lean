/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform convergence of Riemann sums for continuous parametric integrands

For a family `g : α → ℝ → E` valued in a real Banach space `E` that is jointly continuous on
`K ×ˢ Icc a b` for a compact subset `K` of a topological space `α` and `a ≤ b`, the left-endpoint
uniform-partition Riemann sums
`((b - a) / n) • ∑ k ∈ Finset.range n, g x (a + k * (b - a) / n)`
converge uniformly for `x ∈ K` to `∫ t in a..b, g x t` as `n → ∞`, without assuming a metric or
uniform structure on the parameter space `α`.

This parametric uniform convergence is designed to approximate parameter-dependent integrals—such
as Cauchy contour integrals—by finite linear combinations of point evaluations uniformly on compact
subsets, yielding convergence in the compact-open topology on spaces of holomorphic functions.

## Main results

* `TauCeti.intervalIntegral.norm_riemannSum_Icc_sub_integral_le`: quantitative error bound for the
  `n`-point left-endpoint Riemann sum of an interval-integrable function on `Icc a b`.
* `TauCeti.intervalIntegral.tendstoUniformlyOn_riemannSum_Icc`: uniform convergence on compact
  parameter sets over `Icc a b`.
* `TauCeti.intervalIntegral.tendstoUniformlyOn_riemannSum_unitInterval`: specialization to
  `Icc 0 1`.
* `TauCeti.intervalIntegral.tendsto_riemannSum_Icc`,
  `TauCeti.intervalIntegral.tendsto_riemannSum_unitInterval`: non-parametric corollaries.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti

namespace intervalIntegral

section Parametric

variable {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

private noncomputable def uniformPartition (a b : ℝ) (n k : ℕ) : ℝ :=
  a + (k : ℝ) * (b - a) / (n : ℝ)

private theorem uniformPartition_eq (a b : ℝ) (n k : ℕ) :
    uniformPartition a b n k = a + (k : ℝ) * (b - a) / (n : ℝ) := rfl

private theorem uniformPartition_sub (a b : ℝ) (n k : ℕ) :
    uniformPartition a b n (k + 1) - uniformPartition a b n k = (b - a) / (n : ℝ) := by
  dsimp [uniformPartition]; push_cast; ring

private theorem uniformPartition_le_succ {a b : ℝ} (hab : a ≤ b) (n k : ℕ) :
    uniformPartition a b n k ≤ uniformPartition a b n (k + 1) := by
  have hstep : 0 ≤ (b - a) / (n : ℝ) := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg n)
  linarith [uniformPartition_sub a b n k]

private theorem uniformPartition_mem_Icc {a b : ℝ} (hab : a ≤ b) {n k : ℕ} (hn : 1 ≤ n)
    (hk : k ≤ n) : uniformPartition a b n k ∈ Icc a b := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨?_, ?_⟩
  · dsimp [uniformPartition]
    have : 0 ≤ (k : ℝ) * (b - a) / (n : ℝ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg k) hba) hn_pos.le
    linarith
  · dsimp [uniformPartition]
    have hk_le : (k : ℝ) * (b - a) / (n : ℝ) ≤ b - a := by
      rw [div_le_iff₀ hn_pos]
      nlinarith [(Nat.cast_le.mpr hk : (k : ℝ) ≤ n)]
    linarith

omit [CompleteSpace E] in
private theorem norm_uniformPartition_subinterval_le {a b C : ℝ} (hab : a ≤ b) {n k : ℕ}
    (hn : 1 ≤ n) (hk : k < n) {f : ℝ → E}
    (hf : IntervalIntegrable f volume (uniformPartition a b n k) (uniformPartition a b n (k + 1)))
    (hosc : ∀ ⦃s⦄, s ∈ Icc a b → ∀ ⦃t⦄, t ∈ Icc a b → |s - t| ≤ (b - a) / (n : ℝ) →
      ‖f s - f t‖ ≤ C) :
    ‖(∫ _ in uniformPartition a b n k..uniformPartition a b n (k + 1),
          f (uniformPartition a b n k)) -
        ∫ t in uniformPartition a b n k..uniformPartition a b n (k + 1), f t‖ ≤
      C * ((b - a) / (n : ℝ)) := by
  have hle := uniformPartition_le_succ hab n k
  have hsub := uniformPartition_sub a b n k
  have hstep_nonneg : 0 ≤ (b - a) / (n : ℝ) :=
    div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg n)
  rw [← _root_.intervalIntegral.integral_sub intervalIntegrable_const hf,
    ← abs_of_nonneg hstep_nonneg, ← hsub]
  refine _root_.intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  rw [uIoc_of_le hle] at ht
  refine hosc (uniformPartition_mem_Icc hab hn hk.le)
    ⟨(uniformPartition_mem_Icc hab hn hk.le).1.trans ht.1.le,
      ht.2.trans (uniformPartition_mem_Icc hab hn (Nat.succ_le_of_lt hk)).2⟩ ?_
  rw [abs_sub_comm, abs_of_pos (sub_pos.mpr ht.1)]
  linarith [ht.2, hsub]

/-- Quantitative error bound for the `n`-point left-endpoint Riemann sum of an interval-integrable
function `f : ℝ → E` on `Icc a b` (`a ≤ b`, `1 ≤ n`): if `‖f s - f t‖ ≤ C` whenever
`s, t ∈ Icc a b` satisfy `|s - t| ≤ (b - a) / n`, then the Riemann sum is within `C * (b - a)` of
`∫ t in a..b, f t`. -/
theorem norm_riemannSum_Icc_sub_integral_le {a b C : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 1 ≤ n)
    {f : ℝ → E} (hf : IntervalIntegrable f volume a b)
    (hosc : ∀ ⦃s⦄, s ∈ Icc a b → ∀ ⦃t⦄, t ∈ Icc a b → |s - t| ≤ (b - a) / (n : ℝ) →
      ‖f s - f t‖ ≤ C) :
    ‖(((b - a) / (n : ℝ)) • ∑ k ∈ Finset.range n, f (a + (k : ℝ) * (b - a) / (n : ℝ))) -
        ∫ t in a..b, f t‖ ≤ C * (b - a) := by
  rcases hab.eq_or_lt with rfl | hab_lt
  · simp
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- Split the interval integral across the `n` uniform subintervals.
  have hint (k : ℕ) (hk : k < n) :
      IntervalIntegrable f volume (uniformPartition a b n k) (uniformPartition a b n (k + 1)) := by
    refine hf.mono_set ?_
    rw [uIcc_of_le (uniformPartition_le_succ hab n k), uIcc_of_le hab]
    exact Icc_subset_Icc (uniformPartition_mem_Icc hab hn hk.le).1
      (uniformPartition_mem_Icc hab hn (Nat.succ_le_of_lt hk)).2
  have hsum_int :
      (∫ t in a..b, f t) =
        ∑ k ∈ Finset.range n,
          ∫ t in uniformPartition a b n k..uniformPartition a b n (k + 1), f t := by
    have h0 : uniformPartition a b n 0 = a := by simp [uniformPartition]
    have hn' : uniformPartition a b n n = b := by
      dsimp [uniformPartition]; rw [mul_div_cancel_left₀ _ hn_pos.ne', add_sub_cancel]
    simpa only [h0, hn'] using
      (_root_.intervalIntegral.sum_integral_adjacent_intervals hint).symm
  -- Rewrite the Riemann sum as the sum of constant integrals on the same subintervals.
  have hsum_riem :
      (((b - a) / (n : ℝ)) • ∑ k ∈ Finset.range n, f (a + (k : ℝ) * (b - a) / (n : ℝ))) =
        ∑ k ∈ Finset.range n,
          ∫ _ in uniformPartition a b n k..uniformPartition a b n (k + 1),
            f (uniformPartition a b n k) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← uniformPartition_eq, _root_.intervalIntegral.integral_const, uniformPartition_sub]
  -- Bound each subinterval error via `hosc` and sum using the triangle inequality.
  rw [hsum_riem, hsum_int, ← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ Finset.range n,
          ((∫ _ in uniformPartition a b n k..uniformPartition a b n (k + 1),
              f (uniformPartition a b n k)) -
            ∫ t in uniformPartition a b n k..uniformPartition a b n (k + 1), f t)‖
      ≤ ∑ k ∈ Finset.range n,
          ‖(∫ _ in uniformPartition a b n k..uniformPartition a b n (k + 1),
              f (uniformPartition a b n k)) -
            ∫ t in uniformPartition a b n k..uniformPartition a b n (k + 1), f t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, C * ((b - a) / (n : ℝ)) :=
        Finset.sum_le_sum fun k hk =>
          norm_uniformPartition_subinterval_le hab hn (Finset.mem_range.mp hk)
            (hint k (Finset.mem_range.mp hk)) hosc
    _ = C * (b - a) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [hn_pos.ne']

/-- Left-endpoint uniform-partition Riemann sums of a jointly continuous integrand on
`K ×ˢ Icc a b` (`K` compact, `a ≤ b`) converge uniformly on `K` to the interval integral. -/
theorem tendstoUniformlyOn_riemannSum_Icc {K : Set α} (hK : IsCompact K) {a b : ℝ} (hab : a ≤ b)
    {g : α → ℝ → E} (hg : ContinuousOn (Function.uncurry g) (K ×ˢ Icc a b)) :
    TendstoUniformlyOn
      (fun (n : ℕ) x =>
        ((b - a) / (n : ℝ)) • ∑ k ∈ Finset.range n, g x (a + (k : ℝ) * (b - a) / (n : ℝ)))
      (fun x => ∫ t in a..b, g x t) atTop K := by
  rcases hab.eq_or_lt with rfl | hab_lt
  · rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Eventually.of_forall fun _ _ _ => by simp [hε]
  have hba : 0 < b - a := sub_pos.mpr hab_lt
  have hswap : ContinuousOn (Function.uncurry fun t x => g x t) (Icc a b ×ˢ K) :=
    hg.comp continuous_swap.continuousOn fun _ hp => ⟨hp.2, hp.1⟩
  have heq : Equicontinuous (fun (x : K) (t : Icc a b) => g x t) := by
    intro t₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨v, hv, hvt⟩ := hK.mem_uniformity_of_prod hswap t₀.property
      (Metric.dist_mem_uniformity hε)
    have hv' : (Subtype.val : Icc a b → ℝ) ⁻¹' {y | y ∈ Icc a b → y ∈ v} ∈ 𝓝 t₀ := by
      rw [nhds_subtype_eq_comap]
      exact Filter.preimage_mem_comap (mem_inf_principal.mp hv)
    filter_upwards [hv'] with t ht x
    rw [dist_comm]
    exact hvt t (ht t.property) x x.property
  have hueq := CompactSpace.uniformEquicontinuous_of_equicontinuous heq
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformEquicontinuous_iff.mp hueq (ε / (2 * (b - a)))
    (div_pos hε (mul_pos zero_lt_two hba))
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn x hx
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hstep_lt : (b - a) / (n : ℝ) < δ := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hn1), ← div_lt_iff₀' hδ]
    exact hN.trans_le (Nat.cast_le.mpr ((le_max_left N 1).trans hn))
  have hg_cont : ContinuousOn (g x) (Icc a b) :=
    hg.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht => ⟨hx, ht⟩
  rw [dist_comm, dist_eq_norm]
  calc ‖(((b - a) / (n : ℝ)) • ∑ k ∈ Finset.range n, g x (a + (k : ℝ) * (b - a) / (n : ℝ))) -
          ∫ t in a..b, g x t‖
      ≤ ε / (2 * (b - a)) * (b - a) :=
        norm_riemannSum_Icc_sub_integral_le hab hn1 (hg_cont.intervalIntegrable_of_Icc hab)
          fun s hs t ht hst => by
            rw [← dist_eq_norm]
            exact (hFδ ⟨s, hs⟩ ⟨t, ht⟩
              (by simpa [Subtype.dist_eq, Real.dist_eq] using hst.trans_lt hstep_lt) ⟨x, hx⟩).le
    _ = ε / 2 := by field_simp [hba.ne']
    _ < ε := half_lt_self hε

/-- Specialization of `tendstoUniformlyOn_riemannSum_Icc` to the unit interval `Icc 0 1`. -/
theorem tendstoUniformlyOn_riemannSum_unitInterval {K : Set α} (hK : IsCompact K)
    {g : α → ℝ → E} (hg : ContinuousOn (Function.uncurry g) (K ×ˢ Icc 0 1)) :
    TendstoUniformlyOn
      (fun (n : ℕ) x => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, g x ((k : ℝ) / (n : ℝ)))
      (fun x => ∫ t in (0 : ℝ)..1, g x t) atTop K := by
  simpa only [sub_zero, one_div, zero_add, mul_one] using
    tendstoUniformlyOn_riemannSum_Icc hK zero_le_one hg

/-- Left-endpoint uniform-partition Riemann sums of a continuous function `f : ℝ → E` on `Icc a b`
(`a ≤ b`) converge to `∫ t in a..b, f t`. -/
theorem tendsto_riemannSum_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → E} (hf : ContinuousOn f (Icc a b)) :
    Tendsto
      (fun n : ℕ => ((b - a) / (n : ℝ)) • ∑ k ∈ Finset.range n, f (a + (k : ℝ) * (b - a) / (n : ℝ)))
      atTop (𝓝 (∫ t in a..b, f t)) := by
  have h := tendstoUniformlyOn_riemannSum_Icc (K := ({()} : Set Unit)) isCompact_singleton hab
    (g := fun _ t => f t) (hf.comp continuous_snd.continuousOn fun _ hp => hp.2)
  exact h.tendsto_at (mem_singleton ())

/-- Left-endpoint uniform-partition Riemann sums of a continuous function `f : ℝ → E` on `Icc 0 1`
converge to `∫ t in (0 : ℝ)..1, f t`. -/
theorem tendsto_riemannSum_unitInterval {f : ℝ → E} (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, f ((k : ℝ) / (n : ℝ)))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  simpa only [sub_zero, one_div, zero_add, mul_one] using tendsto_riemannSum_Icc zero_le_one hf

end Parametric

end intervalIntegral

end TauCeti
