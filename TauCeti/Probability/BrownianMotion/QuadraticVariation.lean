/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Process.QuadraticVariation
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.Order.BigOperators.Ring.Finset

/-!
# Brownian quadratic sums on deterministic partitions

The sum of squared Brownian increments over a nondecreasing finite grid has mean equal to
its elapsed time and mean squared error twice the sum of squared interval lengths.
Consequently the error is at most twice the elapsed time times any bound on the mesh,
and the sums converge in mean square and in probability along every vanishing-mesh family.
These estimates are the finite-partition input to quadratic variation and Itô's formula.

The unperturbed estimates need only the finite-dimensional Brownian laws: neither path
continuity nor a filtration assumption is imposed. Repeated dates and empty grids are allowed,
and the first date need not be zero. For Brownian motion with almost-surely continuous paths,
adding a continuous finite-variation process preserves the limit in probability.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.5 and §2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal Topology

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {n : ℕ} {t : Fin (n + 1) → ℝ≥0}

/-- Every Brownian quadratic sum is square integrable, even on an unordered grid. -/
theorem memLp_quadraticSum (hB : IsPreBrownianReal B P) (t : Fin (n + 1) → ℝ≥0) :
    MemLp (quadraticSum B t) 2 P := by
  rw [quadraticSum_def]
  exact memLp_finsetSum _ fun i _ ↦ hB.memLp_sq_sub (t i.succ) (t i.castSucc)

/-- A Brownian quadratic sum has expectation equal to the elapsed time. -/
theorem integral_quadraticSum (hB : IsPreBrownianReal B P) (ht : Monotone t) :
    ∫ ω, quadraticSum B t ω ∂P = (t (Fin.last n) : ℝ) - t 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [quadraticSum_def, integral_finsetSum]
  · calc
      _ = ∑ i : Fin n, ((t i.succ : ℝ) - t i.castSucc) := by
        refine sum_congr rfl fun i _ ↦ ?_
        exact hB.integral_sq_sub_of_le (ht (Fin.castSucc_le_succ i))
      _ = _ := Fin.sum_univ_succ_sub_castSucc (fun i ↦ (t i : ℝ))
  · intro i _
    exact (hB.memLp_sq_sub (t i.succ) (t i.castSucc)).integrable one_le_two

/-- On a nondecreasing grid, the variance of a Brownian quadratic sum is twice the sum
of the squared interval lengths. -/
theorem variance_quadraticSum (hB : IsPreBrownianReal B P) (ht : Monotone t) :
    Var[quadraticSum B t; P] =
      2 * ∑ i : Fin n, ((t i.succ : ℝ) - t i.castSucc) ^ 2 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hL (i : Fin n) := hB.memLp_sq_sub (t i.succ) (t i.castSucc)
  have hind := (hB.hasIndepIncrements n t ht).comp (fun (_ : Fin n) (x : ℝ) ↦ x ^ 2) (by fun_prop)
  have hv := IndepFun.variance_sum (s := univ) (fun i _ ↦ hL i)
    (fun i _ j _ hij ↦ hind.indepFun hij)
  have heq : Var[quadraticSum B t; P] =
      ∑ i : Fin n, Var[fun ω ↦ (B (t i.succ) ω - B (t i.castSucc) ω) ^ 2; P] := by
    simpa only [quadraticSum_def, sum_fn] using hv
  rw [heq, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [variance_eq_sub (hL i)]
  simp only [Pi.pow_def, ← pow_mul, Nat.reduceMul]
  rw [hB.integral_sq_sub_of_le (ht (Fin.castSucc_le_succ i)),
    hB.integral_pow_four_sub_of_le (ht (Fin.castSucc_le_succ i))]
  ring

/-- The mean squared error of the Brownian quadratic sum is twice the sum of squared
interval lengths. -/
theorem integral_sq_quadraticSum_sub (hB : IsPreBrownianReal B P) (ht : Monotone t) :
    ∫ ω, (quadraticSum B t ω - ((t (Fin.last n) : ℝ) - t 0)) ^ 2 ∂P =
      2 * ∑ i : Fin n, ((t i.succ : ℝ) - t i.castSucc) ^ 2 := by
  rw [← hB.integral_quadraticSum ht, ← variance_eq_integral
    (hB.memLp_quadraticSum t).aemeasurable, hB.variance_quadraticSum ht]

/-- If every interval has length at most `δ`, the mean squared error is at most twice
`δ` times the elapsed time. Thus one may take `δ` to be the mesh of the grid. -/
theorem integral_sq_quadraticSum_sub_le (hB : IsPreBrownianReal B P) (ht : Monotone t)
    {δ : ℝ} (hmesh : ∀ i : Fin n, (t i.succ : ℝ) - t i.castSucc ≤ δ) :
    ∫ ω, (quadraticSum B t ω - ((t (Fin.last n) : ℝ) - t 0)) ^ 2 ∂P ≤
      2 * ((t (Fin.last n) : ℝ) - t 0) * δ := by
  rw [hB.integral_sq_quadraticSum_sub ht, mul_assoc]
  have hbound := sum_sq_le_sum_mul (s := univ)
    (f := fun i : Fin n ↦ (t i.succ : ℝ) - t i.castSucc)
    (fun i _ ↦ sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Fin.castSucc_le_succ i))))
    (fun i _ ↦ hmesh i)
  rw [Fin.sum_univ_succ_sub_castSucc (fun i ↦ (t i : ℝ))] at hbound
  exact mul_le_mul_of_nonneg_left hbound (by norm_num)

/-- Brownian quadratic sums converge in mean square to the elapsed time along every
vanishing-mesh family of deterministic partitions of a fixed interval. -/
theorem tendsto_integral_sq_quadraticSum_sub (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
    {a b : ℝ≥0} (ht : ∀ k, Monotone (grid k)) (ha : ∀ k, grid k 0 = a)
    (hb : ∀ k, grid k (Fin.last (N k)) = b) {δ : ι → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), (grid k i.succ : ℝ) - grid k i.castSucc ≤ δ k)
    (hδ : Filter.Tendsto δ l (𝓝 0)) :
    Filter.Tendsto (fun k ↦ ∫ ω, (quadraticSum B (grid k) ω - ((b : ℝ) - a)) ^ 2 ∂P)
      l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hδ.const_mul (2 * ((b : ℝ) - a)))
    (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) ?_
  intro k
  simpa only [ha k, hb k] using hB.integral_sq_quadraticSum_sub_le (ht k) (hmesh k)

/-- Brownian quadratic sums converge in probability to the elapsed time on every
vanishing-mesh family of deterministic partitions. No nestedness is needed. -/
theorem tendstoInMeasure_quadraticSum (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
    {a b : ℝ≥0} (ht : ∀ k, Monotone (grid k)) (ha : ∀ k, grid k 0 = a)
    (hb : ∀ k, grid k (Fin.last (N k)) = b) {δ : ι → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), (grid k i.succ : ℝ) - grid k i.castSucc ≤ δ k)
    (hδ : Filter.Tendsto δ l (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ quadraticSum B (grid k)) l (fun _ ↦ (b : ℝ) - a) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply tendstoInMeasure_of_tendsto_integral_norm_sq
  · exact Filter.Eventually.of_forall fun k ↦
      ((hB.memLp_quadraticSum (grid k)).sub (memLp_const ((b : ℝ) - a))).norm.integrable_sq
  · simpa only [Real.norm_eq_abs, sq_abs] using
      hB.tendsto_integral_sq_quadraticSum_sub ht ha hb hmesh hδ

end ProbabilityTheory.IsPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

open Filter Set TauCeti.Probability

/-- Brownian motion plus a continuous finite-variation process has quadratic sums converging
in probability to elapsed time, with no integrability assumption on the perturbation. -/
theorem tendstoInMeasure_quadraticSum_add_of_boundedVariationOn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B A : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {N : ℕ → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
    {a b : ℝ≥0} (hgrid : ∀ k, Monotone (grid k)) (ha : ∀ k, grid k 0 = a)
    (hb : ∀ k, grid k (Fin.last (N k)) = b) {δ : ℕ → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hAmeas : ∀ k i, AEStronglyMeasurable (A (grid k i)) P)
    (hA : ∀ᵐ ω ∂P, ContinuousOn (A · ω) (Icc a b) ∧
      BoundedVariationOn (A · ω) (Icc a b)) :
    TendstoInMeasure P (fun k ↦ quadraticSum (B + A) (grid k)) atTop
      (fun _ ↦ (b : ℝ) - a) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmem (k : ℕ) (i : Fin (N k + 1)) : grid k i ∈ Icc a b := by
    constructor
    · simpa only [ha k] using hgrid k (Fin.zero_le i)
    · simpa only [hb k] using hgrid k (Fin.le_last i)
  apply tendstoInMeasure_quadraticSum_add isCompact_Icc hgrid hmem hmesh hδ
    (fun k i ↦ (hB.hasLaw_eval (grid k i)).aemeasurable.aestronglyMeasurable) hAmeas
  · filter_upwards [hB.cont, hA] with ω hc hω
    exact ⟨hc.continuousOn, hω⟩
  · exact hB.toIsPreBrownianReal.tendstoInMeasure_quadraticSum hgrid ha hb
      (fun k i ↦ (le_abs_self _).trans (by simpa only [NNReal.dist_eq] using hmesh k i)) hδ

end ProbabilityTheory.IsBrownianReal
