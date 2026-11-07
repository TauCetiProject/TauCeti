/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.Distributions.Gaussian.Moments
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Brownian quadratic sums on deterministic partitions

The sum of squared Brownian increments over a nondecreasing finite grid has mean equal to
its elapsed time and mean squared error twice the sum of squared interval lengths.
Consequently the error is at most twice the elapsed time times any bound on the mesh,
and the sums converge in mean square and in probability along every vanishing-mesh family.
These estimates are the finite-partition input to quadratic variation and Itô's formula.

Only the finite-dimensional Brownian laws are needed: neither path continuity nor a
filtration assumption is imposed. Repeated dates and empty grids are allowed, and the first
date need not be zero.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.5 and §2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal Topology

namespace TauCeti.Probability

/-- The sum of squared increments of a real process along a finite grid. -/
def quadraticSum {Ω : Type*} {n : ℕ} (B : ℝ≥0 → Ω → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin n, (B (t i.succ) ω - B (t i.castSucc) ω) ^ 2

theorem quadraticSum_def {Ω : Type*} {n : ℕ} (B : ℝ≥0 → Ω → ℝ)
    (t : Fin (n + 1) → ℝ≥0) :
    quadraticSum B t = fun ω ↦ ∑ i : Fin n, (B (t i.succ) ω - B (t i.castSucc) ω) ^ 2 :=
  (rfl)

/-- A grid with no intervals has zero quadratic sum. -/
@[simp]
theorem quadraticSum_zero {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : Fin 1 → ℝ≥0) :
    quadraticSum B t = 0 := by
  ext ω
  simp [quadraticSum_def]

/-- Quadratic sums are nonnegative, independently of the order of the grid. -/
theorem quadraticSum_nonneg {Ω : Type*} {n : ℕ} (B : ℝ≥0 → Ω → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (ω : Ω) : 0 ≤ quadraticSum B t ω :=
  sum_nonneg fun _ _ ↦ sq_nonneg _

end TauCeti.Probability

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {n : ℕ} {t : Fin (n + 1) → ℝ≥0}

/-- Every Brownian quadratic sum is square integrable, even on an unordered grid. -/
theorem memLp_quadraticSum (hB : IsPreBrownianReal B P) (t : Fin (n + 1) → ℝ≥0) :
    MemLp (quadraticSum B t) 2 P := by
  simp only [quadraticSum_def]
  let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by
    norm_num [Real.holderTriple_iff])
  refine memLp_finsetSum _ fun i _ ↦ ?_
  have h := (hB.hasLaw_sub (t i.succ) (t i.castSucc)).memLp
    (memLp_id_gaussianReal' 4 (by norm_num))
  simpa only [pow_two, Pi.mul_def, Pi.sub_def] using
    (h.mul h : MemLp ((B (t i.succ) - B (t i.castSucc)) *
      (B (t i.succ) - B (t i.castSucc))) 2 P)

/-- A Brownian quadratic sum has expectation equal to the elapsed time. -/
theorem integral_quadraticSum (hB : IsPreBrownianReal B P) (ht : Monotone t) :
    ∫ ω, quadraticSum B t ω ∂P = (t (Fin.last n) : ℝ) - t 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [quadraticSum_def, integral_finsetSum]
  · calc
      _ = ∑ i : Fin n, ((t i.succ : ℝ) - t i.castSucc) := by
        refine sum_congr rfl fun i _ ↦ ?_
        have h := (hB.hasLaw_sub_of_le (ht (Fin.castSucc_le_succ i))).integral_comp
          (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
        simpa only [Function.comp_apply, Pi.sub_apply, integral_sq_gaussianReal,
          zero_pow two_ne_zero, add_zero, NNReal.coe_sub (ht (Fin.castSucc_le_succ i))] using h
      _ = _ := by
        rw [sum_sub_distrib]
        have h₀ := Fin.sum_univ_succ (fun i ↦ (t i : ℝ))
        have hₙ := Fin.sum_univ_castSucc (fun i ↦ (t i : ℝ))
        linarith
  · intro i _
    exact ((hB.hasLaw_sub (t i.succ) (t i.castSucc)).memLp
      (memLp_id_gaussianReal 2)).integrable_sq

/-- Independence of Brownian increments gives the exact variance of the quadratic sum. -/
theorem variance_quadraticSum (hB : IsPreBrownianReal B P) (ht : Monotone t) :
    Var[quadraticSum B t; P] =
      2 * ∑ i : Fin n, ((t i.succ : ℝ) - t i.castSucc) ^ 2 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by
    norm_num [Real.holderTriple_iff])
  have hL (i : Fin n) : MemLp (fun ω ↦ (B (t i.succ) ω - B (t i.castSucc) ω) ^ 2) 2 P := by
    have h := (hB.hasLaw_sub (t i.succ) (t i.castSucc)).memLp
      (memLp_id_gaussianReal' 4 (by norm_num))
    simpa only [pow_two, Pi.mul_def, Pi.sub_def] using (h.mul h :
      MemLp ((B (t i.succ) - B (t i.castSucc)) *
        (B (t i.succ) - B (t i.castSucc))) 2 P)
  have hind := (hB.hasIndepIncrements n t ht).comp (fun (_ : Fin n) (x : ℝ) ↦ x ^ 2) (by fun_prop)
  have hv := IndepFun.variance_sum (s := univ) (fun i _ ↦ hL i)
    (fun i _ j _ hij ↦ hind.indepFun hij)
  have heq : Var[quadraticSum B t; P] =
      ∑ i : Fin n, Var[fun ω ↦ (B (t i.succ) ω - B (t i.castSucc) ω) ^ 2; P] := by
    simpa only [quadraticSum_def, sum_fn] using hv
  rw [heq, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [variance_eq_sub (hL i)]
  have hlaw := hB.hasLaw_sub_of_le (ht (Fin.castSucc_le_succ i))
  have h₂ := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  have h₄ := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
  rw [integral_sq_gaussianReal] at h₂
  have hm := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0
    (t i.succ - t i.castSucc) 2
  norm_num at hm
  rw [hm] at h₄
  simp only [NNReal.coe_sub (ht (Fin.castSucc_le_succ i)), zero_pow two_ne_zero,
    add_zero] at h₂ h₄
  simp only [Function.comp_apply, Pi.sub_apply] at h₂ h₄
  simp only [Pi.pow_def, ← pow_mul, Nat.reduceMul]
  rw [h₂, h₄]
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
  rw [hB.integral_sq_quadraticSum_sub ht]
  have hsum : ∑ i : Fin n, ((t i.succ : ℝ) - t i.castSucc) =
      (t (Fin.last n) : ℝ) - t 0 := by
    rw [sum_sub_distrib]
    have h₀ := Fin.sum_univ_succ (fun i ↦ (t i : ℝ))
    have hₙ := Fin.sum_univ_castSucc (fun i ↦ (t i : ℝ))
    linarith
  calc
    _ ≤ 2 * ∑ i : Fin n, (((t i.succ : ℝ) - t i.castSucc) * δ) := by
      gcongr with i
      have hpos : 0 ≤ (t i.succ : ℝ) - t i.castSucc :=
        sub_nonneg.2 (by exact_mod_cast ht (Fin.castSucc_le_succ i))
      nlinarith [mul_le_mul_of_nonneg_left (hmesh i) hpos]
    _ = _ := by rw [← sum_mul, hsum]; ring

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
  have hvar : Filter.Tendsto (fun k ↦ Var[quadraticSum B (grid k); P]) l (𝓝 0) := by
    have h := hB.tendsto_integral_sq_quadraticSum_sub ht ha hb hmesh hδ
    convert h using 1
    ext k
    rw [variance_eq_integral (hB.memLp_quadraticSum (grid k)).aemeasurable,
      hB.integral_quadraticSum (ht k), ha k, hb k]
  refine tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hvar.div_const (ε ^ 2))
  simp only [zero_div, ENNReal.ofReal_zero, Function.comp_def] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) fun k ↦ ?_
  simpa only [Real.norm_eq_abs, hB.integral_quadraticSum (ht k), ha k, hb k] using
    meas_ge_le_variance_div_sq (hB.memLp_quadraticSum (grid k)) hε

end ProbabilityTheory.IsPreBrownianReal
