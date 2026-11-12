/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.WeightedQuadraticVariation.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.RiemannSums
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Adapted weighted quadratic sums converge to time integrals

For an adapted real process H with almost surely continuous paths and uniformly bounded
second moments on a compact interval, the sums

`∑ H(tᵢ) (B(tᵢ₊₁) - B(tᵢ))²`

converge in probability to the ordinary samplewise integral of H in time. In particular this
applies to bounded continuous adapted weights. The grid is deterministic, may have repeated
dates, and need not be nested. Brownian increment laws relative to the filtration suffice;
neither continuity of B nor usual filtration conditions enter this argument.

The centered sums have second moment at most `2 M T δ`, where M bounds the expected squared
heights, T bounds the final date, and δ bounds the mesh. The remaining time sums converge
pathwise by continuity. These are the quadratic terms in the partition proof of Itô's formula;
no stochastic integral or bracket is assumed here.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open Finset hiding Iic mem_Iic
open scoped Topology NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- A uniform bound M on the expected squared predictable heights bounds the second moment
(mean square) of the centered quadratic error by twice M times the horizon and the mesh. -/
theorem integral_sq_sum_mul_sq_sub_sub_le (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Iic n))
    {H : ℕ → Ω → ℝ} (hH : ∀ i < n, Measurable[ℱ (t i)] (H i))
    (hHi : ∀ i < n, MemLp (H i) 2 P) {M T : ℝ≥0}
    (hM : ∀ i < n, (∫ ω, H i ω ^ 2 ∂P) ≤ M) (hT : t n ≤ T)
    {δ : ℝ} (hδ : 0 ≤ δ) (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    (∫ ω, (∑ i ∈ range n, H i ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
      ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) ≤ 2 * M * T * δ := by
  rw [hB.integral_sq_sum_mul_sq_sub_sub ht hH hHi]
  have hsum : (∑ i ∈ range n, (∫ ω, H i ω ^ 2 ∂P) *
      ((t (i + 1) : ℝ) - t i) ^ 2) ≤
      M * δ * ∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) := by
    rw [mul_sum]
    refine sum_le_sum fun i hi ↦ ?_
    have hi := mem_range.mp hi
    have hstep : 0 ≤ (t (i + 1) : ℝ) - t i :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht hi.le hi (Nat.le_succ i)))
    calc
      _ ≤ (M : ℝ) * ((t (i + 1) : ℝ) - t i) ^ 2 :=
        mul_le_mul_of_nonneg_right (hM i hi) (sq_nonneg _)
      _ ≤ (M : ℝ) * (((t (i + 1) : ℝ) - t i) * δ) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hmesh i hi]) M.coe_nonneg
      _ = _ := by ring
  rw [sum_range_sub (fun i ↦ (t i : ℝ))] at hsum
  have hn : (t n : ℝ) ≤ T := NNReal.coe_le_coe.mpr hT
  have hbound : (M : ℝ) * δ * ((t n : ℝ) - t 0) ≤ M * δ * T :=
    mul_le_mul_of_nonneg_left (by linarith [NNReal.coe_nonneg (t 0)]) (by positivity)
  nlinarith

/-- Centered quadratic sums converge to zero in mean square when the predictable heights
have uniformly bounded second moments and the deterministic mesh vanishes. -/
theorem tendsto_integral_sq_sum_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} {t : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (t k) (Iic (n k))) {H : ι → ℕ → Ω → ℝ}
    (hH : ∀ k i, i < n k → Measurable[ℱ (t k i)] (H k i))
    (hHi : ∀ k i, i < n k → MemLp (H k i) 2 P) {M T : ℝ≥0}
    (hM : ∀ k i, i < n k → (∫ ω, H k i ω ^ 2 ∂P) ≤ M)
    (hT : ∀ k, t k (n k) ≤ T) {δ : ι → ℝ} (hδ : ∀ k, 0 ≤ δ k)
    (hmesh : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∫ ω, (∑ i ∈ range (n k), H k i ω *
      ((B (t k (i + 1)) ω - B (t k i) ω) ^ 2 - ((t k (i + 1) : ℝ) - t k i))) ^ 2 ∂P)
      l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim.const_mul (2 * (M : ℝ) * T))
    (fun k ↦ integral_nonneg fun ω ↦ sq_nonneg _) ?_
  exact fun k ↦ hB.integral_sq_sum_mul_sq_sub_sub_le (ht k) (hH k) (hHi k)
    (hM k) (hT k) (hδ k) (hmesh k)

/-- Centered predictable quadratic errors vanish in probability under a uniform second-moment
bound on the heights. No sample-path regularity of the heights is required. -/
theorem tendstoInMeasure_sum_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} {t : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (t k) (Iic (n k))) {H : ι → ℕ → Ω → ℝ}
    (hH : ∀ k i, i < n k → Measurable[ℱ (t k i)] (H k i))
    (hHi : ∀ k i, i < n k → MemLp (H k i) 2 P) {M T : ℝ≥0}
    (hM : ∀ k i, i < n k → (∫ ω, H k i ω ^ 2 ∂P) ≤ M)
    (hT : ∀ k, t k (n k) ≤ T) {δ : ι → ℝ} (hδ : ∀ k, 0 ≤ δ k)
    (hmesh : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    TendstoInMeasure P (fun k ω ↦ ∑ i ∈ range (n k), H k i ω *
      ((B (t k (i + 1)) ω - B (t k i) ω) ^ 2 - ((t k (i + 1) : ℝ) - t k i)))
      l (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hB.tendsto_integral_sq_sum_mul_sq_sub_sub ht hH hHi hM hT hδ hmesh hlim).sqrt
  simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at hlim
  convert hlim using 1
  ext k
  simp only [Pi.sub_def, sub_zero]
  have hZ : MemLp (fun ω ↦ ∑ i ∈ range (n k), H k i ω *
      ((B (t k (i + 1)) ω - B (t k i) ω) ^ 2 - ((t k (i + 1) : ℝ) - t k i))) 2 P :=
    memLp_finsetSum _ fun i hi ↦ hB.memLp_mul_sq_sub_sub
      (ht k (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))
      (hH k i (mem_range.mp hi)) (hHi k i (mem_range.mp hi))
  rw [hZ.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs]

/-- Left-weighted Brownian quadratic sums converge in probability to the samplewise time
integral of an adapted almost surely continuous process with uniformly bounded second moments.
The integral uses real time via `Real.toNNReal`; no value outside the interval is used. -/
theorem tendstoInMeasure_sum_eval_mul_sq_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {H : ℝ≥0 → Ω → ℝ} {a b M : ℝ≥0}
    (hH : ∀ u ∈ Icc a b, StronglyMeasurable[ℱ u] (H u))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (H · ω) (Icc a b))
    (hHi : ∀ u ∈ Icc a b, MemLp (H u) 2 P)
    (hM : ∀ u ∈ Icc a b, (∫ ω, H u ω ^ 2 ∂P) ≤ M)
    {n : ℕ → ℕ} {t : ℕ → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (t k) (Iic (n k)))
    (ha : ∀ k, t k 0 = a) (hb : ∀ k, t k (n k) = b)
    {δ : ℕ → ℝ} (hδ : ∀ k, 0 ≤ δ k)
    (hmesh : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ω ↦ ∑ i ∈ range (n k),
      H (t k i) ω * (B (t k (i + 1)) ω - B (t k i) ω) ^ 2) atTop
      (fun ω ↦ ∫ u in (a : ℝ)..b, H u.toNNReal ω) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmem k i (hi : i ≤ n k) : t k i ∈ Icc a b := by
    constructor
    · simpa [ha k] using ht k (Nat.zero_le _) hi (Nat.zero_le i)
    · simpa [hb k] using ht k hi self_mem_Iic hi
  have hcenter := hB.tendstoInMeasure_sum_mul_sq_sub_sub ht
    (fun k i hi ↦ (hH _ (hmem k i hi.le)).measurable)
    (fun k i hi ↦ hHi _ (hmem k i hi.le))
    (fun k i hi ↦ hM _ (hmem k i hi.le))
    (fun k ↦ (hb k).le) hδ hmesh hlim
  -- Select an almost surely convergent centered subsequence; the time sums converge on
  -- every continuous sample path, and hence on the same subsequence.
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun k ↦ ?_)).mpr
  · intro ns hns
    obtain ⟨ms, hms, hc⟩ := (hcenter.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hcont, hc] with ω hω hcω
    have hreal : ContinuousOn (fun u : ℝ ↦ H u.toNNReal ω) (Icc (a : ℝ) b) :=
      hω.comp continuous_real_toNNReal.continuousOn (fun u hu ↦ by
        have hu0 : 0 ≤ u := a.coe_nonneg.trans hu.1
        constructor
        · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]
          exact hu.1
        · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]
          exact hu.2)
    have hr := hreal.tendsto_sum_tagged_smul_sub
      (τ := fun k i ↦ (t k i : ℝ)) (ξ := fun k i ↦ (t k i : ℝ))
      (fun k i hi j hj hij ↦ by exact_mod_cast ht k hi hj hij)
      (fun k ↦ by exact_mod_cast ha k) (fun k ↦ by exact_mod_cast hb k)
      (fun k i hi ↦ ⟨le_rfl, by exact_mod_cast ht k hi.le hi (Nat.le_succ i)⟩) hmesh hlim
    simp only [Real.toNNReal_coe, smul_eq_mul] at hr
    have h := hcω.add ((hr.comp hns.tendsto_atTop).comp hms.tendsto_atTop)
    simp only [zero_add] at h
    convert h using 1
    ext k
    simp only [Function.comp_apply]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  · have hBm (u : ℝ≥0) : Measurable (B u) :=
      (hB.adapted u).mono (ℱ.le _) le_rfl
    exact (Finset.measurable_sum _ fun i hi ↦
      ((hH _ (hmem k i (mem_range.mp hi).le)).mono (ℱ.le _)).measurable.mul
        (((hBm (t k (i + 1))).sub (hBm (t k i))).pow_const 2)).aestronglyMeasurable

end TauCeti.Probability.IsFilteredPreBrownianReal
