/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.QuadraticVariation
public import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Martingale.MaximalInequality.L2
import TauCeti.Probability.Moments.Chebyshev

/-!
# Maximal errors of Brownian quadratic sums

The centered squared-increment sums on a deterministic increasing grid form a discrete
martingale on the sampled filtration. Doob's inequality therefore bounds the expected square
of the largest error over **all prefixes** by eight times the sum of squared cell lengths.
In particular these maxima converge in probability on bounded horizons as the mesh vanishes.
This is the grid-point part of uniform quadratic-variation convergence, needed when passing
from partition identities to stochastic change-of-variables formulas.

Only filtration-relative pre-Brownian laws are used; no path continuity or usual conditions
are required. Repeated dates and empty grids are allowed. The maxima here range over trading
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

/-- The quadratic-sum error through the first `n` intervals of a deterministic grid:
`∑ᵢ<n (ΔBᵢ)² - (τₙ - τ₀)`. -/
def quadraticError {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, ((B (τ (i + 1)) ω - B (τ i) ω) ^ 2 - ((τ (i + 1) : ℝ) - τ i))

/-- Express the error as a sum of centered squared increments. -/
theorem quadraticError_def {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) (n : ℕ) :
    quadraticError B τ n = fun ω ↦
      ∑ i ∈ range n, ((B (τ (i + 1)) ω - B (τ i) ω) ^ 2 - ((τ (i + 1) : ℝ) - τ i)) :=
  (rfl)

/-- Express the centered prefix sum using the uncentered quadratic sum. -/
theorem quadraticError_eq_quadraticSum_sub {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0)
    (n : ℕ) (ω : Ω) :
    quadraticError B τ n ω = quadraticSum B (fun i : Fin (n + 1) ↦ τ i) ω -
      ((τ n : ℝ) - τ 0) := by
  rw [quadraticError, sum_sub_distrib, sum_range_sub (fun i ↦ (τ i : ℝ))]
  simp only [quadraticSum_def, sum_range, Fin.val_succ, Fin.val_castSucc]

/-- The empty prefix has zero error. -/
@[simp]
theorem quadraticError_zero {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) :
    quadraticError B τ 0 = 0 := by
  ext ω
  simp [quadraticError]

/-- Adding one interval adds its centered squared increment. -/
theorem quadraticError_succ {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    quadraticError B τ (n + 1) ω = quadraticError B τ n ω +
      ((B (τ (n + 1)) ω - B (τ n) ω) ^ 2 - ((τ (n + 1) : ℝ) - τ n)) := by
  simp only [quadraticError, sum_range_succ]

end TauCeti.Probability

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

/-- Every Brownian quadratic-sum error is square integrable, even on an unordered grid. -/
theorem memLp_quadraticError {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (τ : ℕ → ℝ≥0) (n : ℕ) :
    MemLp (quadraticError B τ n) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [funext (quadraticError_eq_quadraticSum_sub B τ n)]
  exact (hB.memLp_quadraticSum _).sub (memLp_const _)

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability

namespace IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {τ : ℕ → ℝ≥0}

/-- The centered quadratic sums form a martingale on the sampled filtration. -/
theorem martingale_quadraticError (hB : IsFilteredPreBrownianReal ℱ B P) (hτ : Monotone τ) :
    Martingale (quadraticError B τ)
      ⟨fun n ↦ ℱ (τ n), fun _ _ h ↦ ℱ.mono (hτ h), fun n ↦ ℱ.le (τ n)⟩ P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine martingale_of_condExp_sub_eq_zero_nat (fun n ↦ ?_)
    (fun n ↦ (hB.toIsPreBrownianReal.memLp_quadraticError τ n).integrable one_le_two)
    (fun n ↦ ?_)
  · refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
    have hi : i + 1 ≤ n := mem_range.mp hi
    exact ((hB.adapted.stronglyAdapted.stronglyMeasurable_le (hτ hi)).sub
      (hB.adapted.stronglyAdapted.stronglyMeasurable_le (hτ (by omega : i ≤ n)))).pow 2 |>.sub
        stronglyMeasurable_const
  · have heq : quadraticError B τ (n + 1) - quadraticError B τ n =
        fun ω ↦ (B (τ (n + 1)) ω - B (τ n) ω) ^ 2 - ((τ (n + 1) : ℝ) - τ n) := by
      ext ω
      simp [quadraticError_succ]
    rw [heq]
    have hsub := MeasureTheory.condExp_sub (m := ℱ (τ n))
      ((hB.toIsPreBrownianReal.memLp_sq_sub (τ (n + 1)) (τ n)).integrable one_le_two)
      (integrable_const ((τ (n + 1) : ℝ) - τ n))
    simp only [Pi.sub_def] at hsub
    filter_upwards [hsub, hB.condExp_sub_sq (hτ (Nat.le_succ n))] with ω hω hsq
    simpa only [hsq, condExp_const (ℱ.le (τ n)), sub_self, Pi.zero_apply] using hω

/-- The expected square of the largest quadratic-sum error at the first `n + 1` grid
points is at most eight times the sum of squared interval lengths. -/
theorem integral_sq_partialSups_quadraticError_le (hB : IsFilteredPreBrownianReal ℱ B P)
    (n : ℕ) (hτ : MonotoneOn τ (Set.Iic n)) :
    ∫ ω, (partialSups (fun j ω ↦ |quadraticError B τ j ω|) n ω) ^ 2 ∂P ≤
      8 * ∑ i ∈ range n, ((τ (i + 1) : ℝ) - τ i) ^ 2 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hfin : Monotone (fun i : Fin (n + 1) ↦ τ i) := fun i j h ↦
    hτ (Set.mem_Iic.2 (Nat.le_of_lt_succ i.isLt))
      (Set.mem_Iic.2 (Nat.le_of_lt_succ j.isLt)) h
  -- Only the finite prefix is ordered: hold the last date fixed to sample a full martingale.
  let τ' : ℕ → ℝ≥0 := fun j ↦ τ (min j n)
  have hτ' : Monotone τ' := fun _ _ hij ↦
    hτ (Set.mem_Iic.2 (min_le_right _ _)) (Set.mem_Iic.2 (min_le_right _ _))
      (min_le_min_right n hij)
  have heq (j : ℕ) (hj : j ≤ n) : quadraticError B τ' j = quadraticError B τ j := by
    ext ω
    apply sum_congr rfl
    intro i hi
    have hi := mem_range.mp hi
    simp only [τ', min_eq_left (by omega : i ≤ n), min_eq_left (by omega : i + 1 ≤ n)]
  have hL' := hB.toIsPreBrownianReal.memLp_quadraticError τ' n
  have hm := (hB.martingale_quadraticError hτ').integral_sq_partialSups_norm_le n hL'
  have hmaxEq : partialSups (fun j ω ↦ |quadraticError B τ' j ω|) n =
      partialSups (fun j ω ↦ |quadraticError B τ j ω|) n := by
    simp only [partialSups_apply]
    exact Finset.sup'_congr _ rfl fun j hj ↦ by rw [heq j (mem_Iic.mp hj)]
  rw [heq n le_rfl] at hm
  simp only [Real.norm_eq_abs, sq_abs, hmaxEq] at hm
  have he : ∫ ω, quadraticError B τ n ω ^ 2 ∂P =
      2 * ∑ i ∈ range n, ((τ (i + 1) : ℝ) - τ i) ^ 2 := by
    simpa only [quadraticError_eq_quadraticSum_sub, Fin.val_last, Fin.val_zero, Fin.val_succ,
      Fin.val_castSucc, sum_range] using hB.toIsPreBrownianReal.integral_sq_quadraticSum_sub hfin
  rw [he] at hm
  linarith

/-- On a grid of mesh at most `δ`, the expected square of the largest prefix error is
at most `8 (τₙ - τ₀) δ`. -/
theorem integral_sq_partialSups_quadraticError_le_mesh (hB : IsFilteredPreBrownianReal ℱ B P)
    (n : ℕ) (hτ : MonotoneOn τ (Set.Iic n)) {δ : ℝ}
    (hmesh : ∀ i < n, (τ (i + 1) : ℝ) - τ i ≤ δ) :
    ∫ ω, (partialSups (fun j ω ↦ |quadraticError B τ j ω|) n ω) ^ 2 ∂P ≤
      8 * ((τ n : ℝ) - τ 0) * δ := by
  have hfin : Monotone (fun i : Fin (n + 1) ↦ τ i) := fun i j h ↦
    hτ (Set.mem_Iic.2 (Nat.le_of_lt_succ i.isLt))
      (Set.mem_Iic.2 (Nat.le_of_lt_succ j.isLt)) h
  have hvar := hB.toIsPreBrownianReal.integral_sq_quadraticSum_sub hfin
  have hbound := hB.toIsPreBrownianReal.integral_sq_quadraticSum_sub_le hfin
    (fun i ↦ hmesh i i.isLt)
  simp only [Fin.val_last, Fin.val_zero, Fin.val_succ, Fin.val_castSucc] at hvar hbound
  have hmax := hB.integral_sq_partialSups_quadraticError_le n hτ
  rw [sum_range] at hmax
  linarith

/-- Maximal prefix errors tend to zero in mean square for vanishing-mesh grids on a
bounded horizon. The grids need not be nested or have the same number of intervals. -/
theorem tendsto_integral_sq_partialSups_quadraticError (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (grid k) (Set.Iic (N k)))
    {T : ℝ≥0} (hT : ∀ k, grid k (N k) ≤ T) {δ : ι → ℝ}
    (hmesh : ∀ k i, i < N k → (grid k (i + 1) : ℝ) - grid k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∫ ω,
      (partialSups (fun j ω ↦ |quadraticError B (grid k) j ω|) (N k) ω) ^ 2 ∂P) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using
      (hδ.max (tendsto_const_nhds (x := (0 : ℝ)))).const_mul (8 * (T : ℝ)))
    (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) fun k ↦ ?_
  calc
    _ ≤ 8 * ((grid k (N k) : ℝ) - grid k 0) * max (δ k) 0 :=
      hB.integral_sq_partialSups_quadraticError_le_mesh (N k) (ht k)
        (fun i hi ↦ (hmesh k i hi).trans (le_max_left _ _))
    _ ≤ 8 * (T : ℝ) * max (δ k) 0 := by
      have hle : (grid k (N k) : ℝ) - grid k 0 ≤ T :=
        (sub_le_self _ (NNReal.coe_nonneg _)).trans (NNReal.coe_le_coe.2 (hT k))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num))
        (le_max_right _ _)

/-- Maximal prefix errors converge in probability along every bounded-horizon vanishing-mesh
family. Unlike convergence of the terminal sum alone, this controls every trading date. -/
theorem tendstoInMeasure_partialSups_quadraticError (hB : IsFilteredPreBrownianReal ℱ B P)
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0}
    (ht : ∀ k, MonotoneOn (grid k) (Set.Iic (N k)))
    {T : ℝ≥0} (hT : ∀ k, grid k (N k) ≤ T) {δ : ι → ℝ}
    (hmesh : ∀ k i, i < N k → (grid k (i + 1) : ℝ) - grid k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    TendstoInMeasure P
      (fun k ↦ partialSups (fun j ω ↦ |quadraticError B (grid k) j ω|) (N k)) l 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hM (k : ι) : MemLp
      (partialSups (fun j ω ↦ |quadraticError B (grid k) j ω|) (N k)) 2 P := by
    rw [partialSups_apply]
    refine Finset.sup'_induction _ _ (p := fun g ↦ MemLp g 2 P)
      (fun _ hf _ hg ↦ hf.sup hg) fun j _ ↦ ?_
    exact (hB.toIsPreBrownianReal.memLp_quadraticError (grid k) j).norm
  refine tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((hB.tendsto_integral_sq_partialSups_quadraticError ht hT hmesh hδ).div_const (ε ^ 2))
  simp only [zero_div, ENNReal.ofReal_zero, Function.comp_def] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) fun k ↦ ?_
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, Real.norm_eq_abs, sq_abs] using
    TauCeti.meas_ge_le_integral_norm_sq_div_sq (hM k).norm.integrable_sq hε

end IsFilteredPreBrownianReal

end TauCeti.Probability
