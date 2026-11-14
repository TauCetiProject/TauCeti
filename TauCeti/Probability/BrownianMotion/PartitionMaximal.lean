/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.QuadraticVariation
public import TauCeti.Probability.BrownianMotion.Martingale
public import TauCeti.Probability.Process.Filtration.Comp
public import TauCeti.MeasureTheory.Function.Lp.Order
import TauCeti.Algebra.Order.BigOperators.Ring.Finset
import TauCeti.Probability.Martingale.MaximalInequality.L2
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Maximal errors of Brownian quadratic sums

The centered squared-increment sums on a deterministic increasing grid form a discrete
martingale on the sampled filtration. Doob's inequality therefore bounds the expected square
of the largest error over **all prefixes** by eight times the sum of squared cell lengths.
In particular these maxima converge in probability on bounded horizons as the mesh vanishes.
This is the grid-point part of uniform quadratic-variation convergence, needed when passing
from partition identities to stochastic change-of-variables formulas.

Only pre-Brownian laws are needed for the moment and convergence estimates; a measurable
modification supplies the natural filtration. No path continuity or usual conditions are
required. Repeated dates and empty grids are allowed. The maxima here range over grid
dates, not over the intervening continuous-time paths.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.5 and §3.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal Topology

namespace TauCeti.Probability

/-- The quadratic sum through the first `n` intervals minus unit-rate elapsed time:
`∑ᵢ<n (ΔBᵢ)² - (τₙ - τ₀)`. -/
def quadraticSumSubTime {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, ((B (τ (i + 1)) ω - B (τ i) ω) ^ 2 - ((τ (i + 1) : ℝ) - τ i))

/-- Express the time-centered quadratic sum as a sum of centered squared increments. -/
theorem quadraticSumSubTime_def {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) (n : ℕ) :
    quadraticSumSubTime B τ n = fun ω ↦
      ∑ i ∈ range n, ((B (τ (i + 1)) ω - B (τ i) ω) ^ 2 - ((τ (i + 1) : ℝ) - τ i)) :=
  (rfl)

/-- Evaluate the time-centered quadratic sum as a sum of centered squared increments. -/
theorem quadraticSumSubTime_apply {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0)
    (n : ℕ) (ω : Ω) :
    quadraticSumSubTime B τ n ω =
      ∑ i ∈ range n, ((B (τ (i + 1)) ω - B (τ i) ω) ^ 2 - ((τ (i + 1) : ℝ) - τ i)) :=
  (rfl)

/-- Separate the squared increments from their telescoping time correction. -/
theorem quadraticSumSubTime_eq_sum_sub {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (τ : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    quadraticSumSubTime B τ n ω =
      (∑ i ∈ range n, (B (τ (i + 1)) ω - B (τ i) ω) ^ 2) - ((τ n : ℝ) - τ 0) := by
  rw [quadraticSumSubTime_apply, sum_sub_distrib, sum_range_sub (fun i ↦ (τ i : ℝ))]

/-- Express the centered prefix sum using the uncentered quadratic sum. -/
theorem quadraticSumSubTime_eq_quadraticSum_sub {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (τ : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    quadraticSumSubTime B τ n ω = quadraticSum B (fun i : Fin (n + 1) ↦ τ i) ω -
      ((τ n : ℝ) - τ 0) := by
  rw [quadraticSumSubTime_eq_sum_sub]
  simp only [quadraticSum_def, sum_range, Fin.val_succ, Fin.val_castSucc]

/-- The empty prefix has zero centered quadratic sum. -/
@[simp]
theorem quadraticSumSubTime_zero {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) :
    quadraticSumSubTime B τ 0 = 0 := by
  ext ω
  simp [quadraticSumSubTime]

/-- Adding one interval adds its centered squared increment. -/
theorem quadraticSumSubTime_succ {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0)
    (n : ℕ) (ω : Ω) :
    quadraticSumSubTime B τ (n + 1) ω = quadraticSumSubTime B τ n ω +
      ((B (τ (n + 1)) ω - B (τ n) ω) ^ 2 - ((τ (n + 1) : ℝ) - τ n)) := by
  simp only [quadraticSumSubTime, sum_range_succ]

/-- Only grid dates and process values on the observed prefix affect the centered sum. -/
theorem quadraticSumSubTime_congr {Ω : Type*} {B C : ℝ≥0 → Ω → ℝ}
    {τ σ : ℕ → ℝ≥0} {n : ℕ} {ω : Ω} (hτ : ∀ i ≤ n, τ i = σ i)
    (hB : ∀ i ≤ n, B (τ i) ω = C (σ i) ω) :
    quadraticSumSubTime B τ n ω = quadraticSumSubTime C σ n ω := by
  apply sum_congr rfl
  intro i hi
  have hi := mem_range.mp hi
  rw [hB (i + 1) (by omega), hB i (by omega), hτ (i + 1) (by omega), hτ i (by omega)]

end TauCeti.Probability

namespace MeasureTheory.Adapted

open TauCeti.Probability

/-- On an ordered finite prefix, the centered quadratic sum is measurable at its last date. -/
theorem stronglyMeasurable_quadraticSumSubTime {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : Adapted ℱ B)
    {τ : ℕ → ℝ≥0} {n : ℕ} (hτ : MonotoneOn τ (Set.Iic n)) :
    StronglyMeasurable[ℱ (τ n)] (quadraticSumSubTime B τ n) := by
  rw [quadraticSumSubTime_def]
  refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
  have hi := mem_range.mp hi
  exact ((hB.stronglyAdapted.stronglyMeasurable_le
    (hτ (by simp; omega) (by simp) (by omega : i + 1 ≤ n))).sub
      (hB.stronglyAdapted.stronglyMeasurable_le
        (hτ (by simp; omega) (by simp) (by omega : i ≤ n)))).pow 2 |>.sub
          stronglyMeasurable_const

end MeasureTheory.Adapted

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {τ : ℕ → ℝ≥0}

/-- Every Brownian time-centered quadratic sum is square integrable, even on an unordered grid. -/
theorem memLp_quadraticSumSubTime (hB : IsPreBrownianReal B P) (τ : ℕ → ℝ≥0) (n : ℕ) :
    MemLp (quadraticSumSubTime B τ n) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [funext (quadraticSumSubTime_eq_quadraticSum_sub B τ n)]
  exact (hB.memLp_quadraticSum _).sub (memLp_const _)

/-- The largest absolute centered quadratic sum on a finite prefix is square integrable. -/
theorem memLp_partialSups_abs_quadraticSumSubTime (hB : IsPreBrownianReal B P)
    (τ : ℕ → ℝ≥0) (n : ℕ) :
    MemLp (partialSups (fun j ω ↦ |quadraticSumSubTime B τ j ω|) n) 2 P :=
  MemLp.partialSups (fun j _ ↦ (hB.memLp_quadraticSumSubTime τ j).norm)

/-- A Brownian time-centered quadratic sum on an ordered prefix has expectation zero. -/
@[simp]
theorem integral_quadraticSumSubTime (hB : IsPreBrownianReal B P) (n : ℕ)
    (hτ : MonotoneOn τ (Set.Iic n)) : ∫ ω, quadraticSumSubTime B τ n ω ∂P = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [quadraticSumSubTime_def, integral_finsetSum]
  · apply sum_eq_zero
    intro i hi
    have hi := mem_range.mp hi
    exact hB.integral_sq_sub_sub_eq_zero
      (hτ (by simp; omega) (by simp; omega) (Nat.le_succ i))
  · intro i _
    exact hB.memLp_sq_sub_sub.integrable one_le_two

/-- The second moment of a Brownian time-centered quadratic sum is twice the sum of
squared cell lengths. -/
theorem integral_sq_quadraticSumSubTime (hB : IsPreBrownianReal B P) (n : ℕ)
    (hτ : MonotoneOn τ (Set.Iic n)) :
    ∫ ω, quadraticSumSubTime B τ n ω ^ 2 ∂P =
      2 * ∑ i ∈ range n, ((τ (i + 1) : ℝ) - τ i) ^ 2 := by
  have hfin : Monotone (fun i : Fin (n + 1) ↦ τ i) := fun i j h ↦
    hτ (Set.mem_Iic.2 (Nat.le_of_lt_succ i.isLt))
      (Set.mem_Iic.2 (Nat.le_of_lt_succ j.isLt)) h
  simpa only [quadraticSumSubTime_eq_quadraticSum_sub, Fin.val_last, Fin.val_zero,
    Fin.val_succ, Fin.val_castSucc, sum_range] using hB.integral_sq_quadraticSum_sub hfin

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {τ : ℕ → ℝ≥0}

/-- The time-centered quadratic sums form a martingale on the sampled filtration. -/
theorem martingale_quadraticSumSubTime (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : Monotone τ) : Martingale (quadraticSumSubTime B τ) (ℱ.comp hτ) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine martingale_of_condExp_sub_eq_zero_nat (fun n ↦ ?_)
    (fun n ↦ (hB.toIsPreBrownianReal.memLp_quadraticSumSubTime τ n).integrable one_le_two)
    (fun n ↦ ?_)
  · exact (hB.adapted.stronglyMeasurable_quadraticSumSubTime
      (hτ.monotoneOn (s := Set.Iic n))).mono (Filtration.comp_apply ℱ hτ n).symm.le
  · have heq : quadraticSumSubTime B τ (n + 1) - quadraticSumSubTime B τ n =
        fun ω ↦ (B (τ (n + 1)) ω - B (τ n) ω) ^ 2 - ((τ (n + 1) : ℝ) - τ n) := by
      ext ω
      simp [quadraticSumSubTime_succ]
    rw [heq, Filtration.comp_apply]
    have hsub := MeasureTheory.condExp_sub (m := ℱ (τ n))
      ((hB.toIsPreBrownianReal.memLp_sq_sub (τ (n + 1)) (τ n)).integrable one_le_two)
      (integrable_const ((τ (n + 1) : ℝ) - τ n))
    simp only [Pi.sub_def] at hsub
    filter_upwards [hsub, hB.condExp_sub_sq (hτ (Nat.le_succ n))] with ω hω hsq
    simpa only [hsq, condExp_const (ℱ.le (τ n)), sub_self, Pi.zero_apply] using hω

private theorem integral_sq_partialSups_abs_quadraticSumSubTime_le_filtered
    (hB : IsFilteredPreBrownianReal ℱ B P) (n : ℕ) (hτ : MonotoneOn τ (Set.Iic n)) :
    ∫ ω, (partialSups (fun j ω ↦ |quadraticSumSubTime B τ j ω|) n ω) ^ 2 ∂P ≤
      8 * ∑ i ∈ range n, ((τ (i + 1) : ℝ) - τ i) ^ 2 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  -- Only the finite prefix is ordered: hold the last date fixed to sample a full martingale.
  let τ' : ℕ → ℝ≥0 := fun j ↦ τ (min j n)
  have hτ' : Monotone τ' := fun _ _ hij ↦
    hτ (Set.mem_Iic.2 (min_le_right _ _)) (Set.mem_Iic.2 (min_le_right _ _))
      (min_le_min_right n hij)
  have heq (j : ℕ) (hj : j ≤ n) : quadraticSumSubTime B τ' j = quadraticSumSubTime B τ j := by
    funext ω
    exact quadraticSumSubTime_congr (fun i hi ↦ congrArg τ (min_eq_left (hi.trans hj)))
      (fun i hi ↦ by simp only [τ', min_eq_left (hi.trans hj)])
  have hL' := hB.toIsPreBrownianReal.memLp_quadraticSumSubTime τ' n
  have hm := (hB.martingale_quadraticSumSubTime hτ').integral_sq_partialSups_norm_le n hL'
  have hmaxEq : partialSups (fun j ω ↦ |quadraticSumSubTime B τ' j ω|) n =
      partialSups (fun j ω ↦ |quadraticSumSubTime B τ j ω|) n := by
    simp only [partialSups_apply]
    exact Finset.sup'_congr _ rfl fun j hj ↦ by rw [heq j (mem_Iic.mp hj)]
  rw [heq n le_rfl] at hm
  simp only [Real.norm_eq_abs, sq_abs, hmaxEq] at hm
  rw [hB.toIsPreBrownianReal.integral_sq_quadraticSumSubTime n hτ] at hm
  linarith

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {τ : ℕ → ℝ≥0}

/-- The expected square of the largest absolute time-centered quadratic sum at the first
`n + 1` grid points is at most eight times the sum of squared interval lengths. -/
theorem integral_sq_partialSups_abs_quadraticSumSubTime_le (hB : IsPreBrownianReal B P)
    (n : ℕ) (hτ : MonotoneOn τ (Set.Iic n)) :
    ∫ ω, (partialSups (fun j ω ↦ |quadraticSumSubTime B τ j ω|) n ω) ^ 2 ∂P ≤
      8 * ∑ i ∈ range n, ((τ (i + 1) : ℝ) - τ i) ^ 2 := by
  -- A measurable modification has a natural filtration; only countably many grid values
  -- are needed to transfer the finite maximum back to the original process.
  let B' t := (hB.integrable_eval t).aestronglyMeasurable.mk (B t)
  have hBB' (t) : B t =ᵐ[P] B' t := (hB.integrable_eval t).aestronglyMeasurable.ae_eq_mk
  have hB' := (hB.congr hBB').isFilteredPreBrownianReal_natural
    (fun t ↦ (hB.integrable_eval t).aestronglyMeasurable.stronglyMeasurable_mk)
  have heq : (fun ω ↦ (partialSups (fun j ω ↦ |quadraticSumSubTime B τ j ω|) n ω) ^ 2) =ᵐ[P]
      (fun ω ↦ (partialSups (fun j ω ↦ |quadraticSumSubTime B' τ j ω|) n ω) ^ 2) := by
    have hdates : ∀ᵐ ω ∂P, ∀ i : ℕ, B (τ i) ω = B' (τ i) ω :=
      ae_all_iff.mpr (fun i ↦ hBB' (τ i))
    filter_upwards [hdates] with ω hω
    congr 1
    simp only [partialSups_apply, Finset.sup'_apply]
    exact Finset.sup'_congr _ rfl fun j _ ↦ congrArg abs
      (quadraticSumSubTime_congr (fun _ _ ↦ rfl) (fun i _ ↦ hω i))
  rw [integral_congr_ae heq]
  exact hB'.integral_sq_partialSups_abs_quadraticSumSubTime_le_filtered n hτ

/-- On a grid with cell lengths at most `δ`, the expected squared maximal absolute error is
at most `8 (τₙ - τ₀) δ`. -/
theorem integral_sq_partialSups_abs_quadraticSumSubTime_le_of_sub_le (hB : IsPreBrownianReal B P)
    (n : ℕ) (hτ : MonotoneOn τ (Set.Iic n)) {δ : ℝ}
    (hmesh : ∀ i < n, (τ (i + 1) : ℝ) - τ i ≤ δ) :
    ∫ ω, (partialSups (fun j ω ↦ |quadraticSumSubTime B τ j ω|) n ω) ^ 2 ∂P ≤
      8 * ((τ n : ℝ) - τ 0) * δ := by
  calc
    _ ≤ 8 * ∑ i ∈ range n, ((τ (i + 1) : ℝ) - τ i) ^ 2 :=
      hB.integral_sq_partialSups_abs_quadraticSumSubTime_le n hτ
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (sum_range_sq_sub_le (fun i ↦ (τ i : ℝ)) n
          (fun _ hi _ hj hij ↦ NNReal.coe_le_coe.mpr (hτ hi hj hij)) hmesh) (by norm_num)

/-- Maximal prefix errors tend to zero in mean square for vanishing-mesh grids on a
bounded horizon. The grids need not be nested or have the same number of intervals. -/
theorem tendsto_integral_sq_partialSups_abs_quadraticSumSubTime (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (grid k) (Set.Iic (N k)))
    {T : ℝ≥0} (hT : ∀ k, grid k (N k) ≤ T) {δ : ι → ℝ}
    (hmesh : ∀ k i, i < N k → (grid k (i + 1) : ℝ) - grid k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∫ ω,
      (partialSups (fun j ω ↦ |quadraticSumSubTime B (grid k) j ω|) (N k) ω) ^ 2 ∂P)
        l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using
      (hδ.max (tendsto_const_nhds (x := (0 : ℝ)))).const_mul (8 * (T : ℝ)))
    (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) fun k ↦ ?_
  calc
    _ ≤ 8 * ((grid k (N k) : ℝ) - grid k 0) * max (δ k) 0 :=
      hB.integral_sq_partialSups_abs_quadraticSumSubTime_le_of_sub_le (N k) (ht k)
        (fun i hi ↦ (hmesh k i hi).trans (le_max_left _ _))
    _ ≤ 8 * (T : ℝ) * max (δ k) 0 := by
      have hle : (grid k (N k) : ℝ) - grid k 0 ≤ T :=
        (sub_le_self _ (NNReal.coe_nonneg _)).trans (NNReal.coe_le_coe.2 (hT k))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num))
        (le_max_right _ _)

/-- Maximal prefix errors converge in probability along every bounded-horizon vanishing-mesh
family. Unlike convergence of the terminal sum alone, this controls every grid date. -/
theorem tendstoInMeasure_partialSups_abs_quadraticSumSubTime (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (grid k) (Set.Iic (N k)))
    {T : ℝ≥0} (hT : ∀ k, grid k (N k) ≤ T) {δ : ι → ℝ}
    (hmesh : ∀ k i, i < N k → (grid k (i + 1) : ℝ) - grid k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    TendstoInMeasure P
      (fun k ↦ partialSups (fun j ω ↦ |quadraticSumSubTime B (grid k) j ω|) (N k)) l 0 := by
  apply tendstoInMeasure_of_tendsto_integral_norm_sq
  · exact Eventually.of_forall fun k ↦ by
      simpa only [Pi.zero_apply, sub_zero] using
        (hB.memLp_partialSups_abs_quadraticSumSubTime (grid k) (N k)).norm.integrable_sq
  · simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, sq_abs] using
      hB.tendsto_integral_sq_partialSups_abs_quadraticSumSubTime ht hT hmesh hδ

end ProbabilityTheory.IsPreBrownianReal
