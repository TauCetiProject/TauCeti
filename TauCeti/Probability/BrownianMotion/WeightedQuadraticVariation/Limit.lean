/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.WeightedQuadraticVariation.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.RiemannSums
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Algebra.Order.BigOperators.Ring.Finset

/-!
# Adapted weighted quadratic sums converge to time integrals

For an adapted real process H with almost surely continuous paths and uniformly bounded
second moments on a compact interval, the sums

`∑ H(tᵢ) (B(tᵢ₊₁) - B(tᵢ))²`

converge in probability to the ordinary samplewise integral of H in time. In particular this
applies to bounded continuous adapted weights. The grid is deterministic, may have repeated
dates, and need not be nested. Brownian increment laws relative to the filtration suffice;
neither continuity of B nor usual filtration conditions enter this argument.

The centered sums have second moment at most `2 M (tₙ - t₀) δ`, where M bounds the expected
squared heights and δ bounds the mesh. The remaining time sums converge
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
(mean square) of the centered quadratic error by twice M times the elapsed time and the mesh. -/
theorem integral_sq_sum_mul_sq_sub_sub_le (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Iic n))
    {H : ℕ → Ω → ℝ} (hH : ∀ i < n, Measurable[ℱ (t i)] (H i))
    (hHi : ∀ i < n, MemLp (H i) 2 P) {M : ℝ}
    (hM : ∀ i < n, (∫ ω, H i ω ^ 2 ∂P) ≤ M)
    {δ : ℝ} (hmesh : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    (∫ ω, (∑ i ∈ range n, H i ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
      ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) ≤ 2 * M * ((t n : ℝ) - t 0) * δ := by
  by_cases hn : n = 0
  · subst n
    simp
  have hM0 : 0 ≤ M :=
    (integral_nonneg fun ω ↦ sq_nonneg (H 0 ω)).trans (hM 0 (Nat.pos_of_ne_zero hn))
  rw [hB.integral_sq_sum_mul_sq_sub_sub ht hH hHi]
  calc
    _ ≤ 2 * ∑ i ∈ range n, M * ((t (i + 1) : ℝ) - t i) ^ 2 := by
      gcongr with i hi
      exact hM i (mem_range.mp hi)
    _ = 2 * M * ∑ i ∈ range n, ((t (i + 1) : ℝ) - t i) ^ 2 := by
      rw [← mul_sum, ← mul_assoc]
    _ ≤ 2 * M * (((t n : ℝ) - t 0) * δ) :=
      mul_le_mul_of_nonneg_left
        (sum_range_sq_sub_le (fun i ↦ (t i : ℝ)) n
          (fun _ hi _ hj hij ↦ NNReal.coe_le_coe.mpr (ht hi hj hij)) hmesh)
        (by positivity)
    _ = _ := by ring

/-- Centered quadratic sums with uniformly bounded elapsed times converge to zero in mean square
when the predictable heights have uniformly bounded second moments and the deterministic mesh
vanishes. -/
theorem tendsto_integral_sq_sum_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} {t : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (t k) (Iic (n k))) {H : ι → ℕ → Ω → ℝ}
    (hH : ∀ k i, i < n k → Measurable[ℱ (t k i)] (H k i))
    (hHi : ∀ k i, i < n k → MemLp (H k i) 2 P) {M L : ℝ}
    (hM : ∀ k i, i < n k → (∫ ω, H k i ω ^ 2 ∂P) ≤ M)
    (hL : ∀ k, (t k (n k) : ℝ) - t k 0 ≤ L) {δ : ι → ℝ}
    (hmesh : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∫ ω, (∑ i ∈ range (n k), H k i ω *
      ((B (t k (i + 1)) ω - B (t k i) ω) ^ 2 - ((t k (i + 1) : ℝ) - t k i))) ^ 2 ∂P)
      l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using
      (hlim.max (tendsto_const_nhds (x := (0 : ℝ)))).const_mul (2 * max M 0 * max L 0))
    (fun k ↦ integral_nonneg fun ω ↦ sq_nonneg _) ?_
  intro k
  refine (hB.integral_sq_sum_mul_sq_sub_sub_le (ht k) (hH k) (hHi k)
    (fun i hi ↦ (hM k i hi).trans (le_max_left M 0))
    (fun i hi ↦ (hmesh k i hi).trans (le_max_left (δ k) 0))).trans ?_
  dsimp only
  gcongr
  exact (hL k).trans (le_max_left L 0)

/-- Centered predictable quadratic errors vanish in probability along vanishing-mesh deterministic
grids with uniformly bounded elapsed times, under a uniform second-moment bound on the heights.
No sample-path regularity of the heights is required. -/
theorem tendstoInMeasure_sum_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} {t : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (t k) (Iic (n k))) {H : ι → ℕ → Ω → ℝ}
    (hH : ∀ k i, i < n k → Measurable[ℱ (t k i)] (H k i))
    (hHi : ∀ k i, i < n k → MemLp (H k i) 2 P) {M L : ℝ}
    (hM : ∀ k i, i < n k → (∫ ω, H k i ω ^ 2 ∂P) ≤ M)
    (hL : ∀ k, (t k (n k) : ℝ) - t k 0 ≤ L) {δ : ι → ℝ}
    (hmesh : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    TendstoInMeasure P (fun k ω ↦ ∑ i ∈ range (n k), H k i ω *
      ((B (t k (i + 1)) ω - B (t k i) ω) ^ 2 - ((t k (i + 1) : ℝ) - t k i)))
      l (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_integral_norm_sq
  · filter_upwards [] with k
    have hZ : MemLp (fun ω ↦ ∑ i ∈ range (n k), H k i ω *
        ((B (t k (i + 1)) ω - B (t k i) ω) ^ 2 - ((t k (i + 1) : ℝ) - t k i))) 2 P :=
      memLp_finsetSum _ fun i hi ↦ hB.memLp_mul_sq_sub_sub
        (ht k (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))
        (hH k i (mem_range.mp hi)) (hHi k i (mem_range.mp hi))
    simpa only [sub_zero] using hZ.norm.integrable_sq
  · simpa only [sub_zero, Real.norm_eq_abs, sq_abs] using
      hB.tendsto_integral_sq_sum_mul_sq_sub_sub ht hH hHi hM hL hmesh hlim

/-- Left-weighted Brownian quadratic sums converge in probability to the samplewise time
integral of an adapted almost surely continuous process with uniformly bounded second moments.
The integral uses real time via `Real.toNNReal`; no value outside the interval is used. -/
theorem tendstoInMeasure_sum_mul_sq_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {H : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0} {M : ℝ}
    (hH : ∀ u ∈ Icc a b, Measurable[ℱ u] (H u))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (H · ω) (Icc a b))
    (hHi : ∀ u ∈ Icc a b, MemLp (H u) 2 P)
    (hM : ∀ u ∈ Icc a b, (∫ ω, H u ω ^ 2 ∂P) ≤ M)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} {t : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (t k) (Iic (n k)))
    (ha : ∀ k, t k 0 = a) (hb : ∀ k, t k (n k) = b)
    {δ : ι → ℝ}
    (hmesh : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    TendstoInMeasure P (fun k ω ↦ ∑ i ∈ range (n k),
      H (t k i) ω * (B (t k (i + 1)) ω - B (t k i) ω) ^ 2) l
      (fun ω ↦ ∫ u in (a : ℝ)..b, H u.toNNReal ω) := by
  -- The mesh induces a countably generated filter, so sequential arguments suffice
  -- even when the original indexing filter is not countably generated.
  suffices h : TendstoInMeasure P (fun k ω ↦ ∑ i ∈ range (n k),
      H (t k i) ω * (B (t k (i + 1)) ω - B (t k i) ω) ^ 2)
      (comap δ (𝓝 0)) (fun ω ↦ ∫ u in (a : ℝ)..b, H u.toNNReal ω) from
    fun ε hε ↦ (h ε hε).mono_left hlim.le_comap
  have hlim : Tendsto δ (comap δ (𝓝 0)) (𝓝 0) := tendsto_comap
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmem k i (hi : i ≤ n k) : t k i ∈ Icc a b := by
    constructor
    · simpa [ha k] using ht k (Nat.zero_le _) hi (Nat.zero_le i)
    · simpa [hb k] using ht k hi self_mem_Iic hi
  have hcenter := hB.tendstoInMeasure_sum_mul_sq_sub_sub ht
    (fun k i hi ↦ hH _ (hmem k i hi.le))
    (fun k i hi ↦ hHi _ (hmem k i hi.le))
    (fun k i hi ↦ hM _ (hmem k i hi.le))
    (L := (b : ℝ) - a) (fun k ↦ by rw [ha k, hb k]) hmesh hlim
  intro ε hε
  apply tendsto_of_seq_tendsto
  intro ks hks
  suffices hseq : TendstoInMeasure P (fun j ω ↦ ∑ i ∈ range (n (ks j)),
      H (t (ks j) i) ω * (B (t (ks j) (i + 1)) ω - B (t (ks j) i) ω) ^ 2) atTop
      (fun ω ↦ ∫ u in (a : ℝ)..b, H u.toNNReal ω) from hseq ε hε
  -- Select an almost surely convergent centered subsequence; the time sums converge on
  -- every continuous sample path, and hence on the same subsequence.
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun k ↦ ?_)).mpr
  · intro ns hns
    obtain ⟨ms, hms, hc⟩ := ((hcenter.comp hks).comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hcont, hc] with ω hω hcω
    have hr := hω.tendsto_sum_tagged_sub_smul_toNNReal (ξ := t) ht ha hb
      (fun k i hi ↦ ⟨le_rfl, ht k hi.le hi (Nat.le_succ i)⟩) hmesh hlim
    simp only [smul_eq_mul] at hr
    have h := hcω.add (((hr.comp hks).comp hns.tendsto_atTop).comp hms.tendsto_atTop)
    simp only [zero_add] at h
    refine h.congr fun k ↦ ?_
    simp only [Function.comp_apply]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  · have hBm (u : ℝ≥0) : Measurable (B u) :=
      (hB.adapted u).mono (ℱ.le _) le_rfl
    exact (Finset.measurable_sum _ fun i hi ↦
      ((hH _ (hmem (ks k) i (mem_range.mp hi).le)).mono (ℱ.le _) le_rfl).mul
        (((hBm (t (ks k) (i + 1))).sub
          (hBm (t (ks k) i))).pow_const 2)).aestronglyMeasurable

end TauCeti.Probability.IsFilteredPreBrownianReal
