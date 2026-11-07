/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.Distributions.Gaussian.Moments
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Left-step approximation of the square of Brownian motion

The mean-squared increment of `B²` is `4s(t-s) + 3(t-s)²`, not the fourth moment
`3(t-s)²` of the increment of `B`. Its integral on a cell is `2s(t-s)² + (t-s)³`.
On a grid of mesh at most `δ` in `[0,T]`, the sum is at most `T²δ`; on the equal
`n`-cell grid it is exactly `T³/n`. Thus left-step approximations converge in
time-integrated mean square, as needed for the integrand in the cubic Brownian Itô identity.

Only finite-dimensional Brownian laws are used; path continuity and a filtration are not needed.
Expectations are taken before the time integral. For a jointly measurable process, Tonelli
identifies this quantity with the expected pathwise square-energy error.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The mean-squared increment of the square of Brownian motion. -/
theorem integral_sq_sub_sq_eval (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (B t ω ^ 2 - B s ω ^ 2) ^ 2 ∂P) =
      4 * (s : ℝ) * ((t : ℝ) - s) + 3 * ((t : ℝ) - s) ^ 2 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let D := B t - B s
  have hD : HasLaw D (gaussianReal 0 (t - s)) P := hB.hasLaw_sub_of_le hst
  have hind : IndepFun (B s) D P :=
    hB.hasIndepIncrements.indepFun_eval_sub zero_le hst hB.eval_zero_ae_eq_zero
  have hint (X : Ω → ℝ) (v : ℝ≥0) (hX : HasLaw X (gaussianReal 0 v) P) (k : ℕ) :
      Integrable (fun ω ↦ X ω ^ k) P := by
    apply (integrable_norm_iff (hX.aemeasurable.pow_const k).aestronglyMeasurable).1
    simpa only [norm_pow] using
      (hX.hasGaussianLaw.memLp (p := (k : ℝ≥0∞)) (by simp)).integrable_norm_pow'
  have h22 : IndepFun (fun ω ↦ B s ω ^ 2) (fun ω ↦ D ω ^ 2) P := by
    simpa only [Function.comp_def] using
      hind.comp (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2)
        (by fun_prop) (by fun_prop)
  have h13 : IndepFun (B s) (fun ω ↦ D ω ^ 3) P := by
    simpa only [Function.comp_def, id_eq] using
      hind.comp (φ := id) (ψ := fun x : ℝ ↦ x ^ 3) (by fun_prop) (by fun_prop)
  have hi22 : Integrable (fun ω ↦ B s ω ^ 2 * D ω ^ 2) P :=
    h22.integrable_mul (hint _ _ (hB.hasLaw_eval s) 2) (hint _ _ hD 2)
  have hi13 : Integrable (fun ω ↦ B s ω * D ω ^ 3) P :=
    h13.integrable_mul (hB.integrable_eval s) (hint _ _ hD 3)
  have hm22 : (∫ ω, B s ω ^ 2 * D ω ^ 2 ∂P) = (s : ℝ) * (t - s : ℝ≥0) := by
    have hs2 := (hB.hasLaw_eval s).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    have hd2 := hD.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    simp only [Function.comp_def] at hs2 hd2
    rw [h22.integral_fun_mul_eq_mul_integral (hint _ _ (hB.hasLaw_eval s) 2).1
      (hint _ _ hD 2).1, hs2, hd2]
    simp [TauCeti.Probability.integral_sq_gaussianReal]
  have hm13 : (∫ ω, B s ω * D ω ^ 3 ∂P) = 0 := by
    rw [h13.integral_fun_mul_eq_mul_integral (hB.integrable_eval s).1 (hint _ _ hD 3).1,
      hB.integral_eval, zero_mul]
  have hm4 : (∫ ω, D ω ^ 4 ∂P) = 3 * (t - s : ℝ≥0) ^ 2 := by
    calc
      _ = ∫ x, (x - 0) ^ (2 * 2) ∂gaussianReal 0 (t - s) := by
        simpa using hD.integral_comp (f := fun x : ℝ ↦ (x - 0) ^ (2 * 2)) (by fun_prop)
      _ = _ := by
        rw [TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal]
        norm_num [Nat.doubleFactorial, mul_comm]
  have hexpand (ω : Ω) : (B t ω ^ 2 - B s ω ^ 2) ^ 2 =
      4 * (B s ω ^ 2 * D ω ^ 2) + 4 * (B s ω * D ω ^ 3) + D ω ^ 4 := by
    dsimp [D]
    ring
  simp_rw [hexpand]
  have hi : Integrable (fun ω ↦ 4 * (B s ω ^ 2 * D ω ^ 2) +
      4 * (B s ω * D ω ^ 3)) P := (hi22.const_mul 4).add (hi13.const_mul 4)
  rw [integral_add hi (hint _ _ hD 4),
    integral_add (hi22.const_mul 4) (hi13.const_mul 4),
    integral_const_mul, integral_const_mul, hm22, hm13, hm4, NNReal.coe_sub hst]
  ring

/-- The expected square-energy error on one cell of a left-step approximation to `B²`.
The time integral is over real calendar time; `toNNReal` is immaterial on this interval. -/
theorem integral_integral_sq_sub_sq_eval (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ u in (s : ℝ)..t, ∫ ω, (B u.toNNReal ω ^ 2 - B s ω ^ 2) ^ 2 ∂P) =
      2 * (s : ℝ) * ((t : ℝ) - s) ^ 2 + ((t : ℝ) - s) ^ 3 := by
  calc
    _ = ∫ u in (s : ℝ)..t, 4 * (s : ℝ) * (u - s) + 3 * (u - s) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by exact_mod_cast hst)] at hu
      have hu0 : 0 ≤ u := s.coe_nonneg.trans hu.1
      have hsu : s ≤ u.toNNReal := by
        exact_mod_cast (show (s : ℝ) ≤ (u.toNNReal : ℝ) by
          rw [Real.coe_toNNReal _ hu0]
          exact hu.1)
      simpa only [Real.coe_toNNReal _ hu0] using hB.integral_sq_sub_sq_eval hsu
    _ = _ := by
      have hd (u : ℝ) : HasDerivAt
          (fun v : ℝ ↦ 2 * (s : ℝ) * (v - s) ^ 2 + (v - s) ^ 3)
          (4 * (s : ℝ) * (u - s) + 3 * (u - s) ^ 2) u := by
        convert ((((hasDerivAt_id u).sub_const (s : ℝ)).pow 2).const_mul (2 * (s : ℝ))).add
          (((hasDerivAt_id u).sub_const (s : ℝ)).pow 3) using 1
        · ext v
          simp only [Pi.add_apply, Pi.pow_apply, id_eq]
        · simp only [id_eq]
          ring
      have hc : Continuous (fun u : ℝ ↦ 4 * (s : ℝ) * (u - s) + 3 * (u - s) ^ 2) :=
        by fun_prop
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u)
        (hc.intervalIntegrable _ _)]
      ring

/-- A mesh bound for the expected square-energy error of the left-step approximation to `B²`.
Repeated grid points and an empty grid are allowed. The grid need only be monotone up to `n`. -/
theorem sum_integral_integral_sq_sub_sq_eval_le (hB : IsPreBrownianReal B P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {T δ : ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hT : (τ n : ℝ) ≤ T) (hδ0 : 0 ≤ δ)
    (hδ : ∀ i < n, (τ (i + 1) : ℝ) - τ i ≤ δ) :
    (∑ i ∈ range n, ∫ u in (τ i : ℝ)..τ (i + 1),
      ∫ ω, (B u.toNNReal ω ^ 2 - B (τ i) ω ^ 2) ^ 2 ∂P) ≤ T ^ 2 * δ := by
  have hT0 : 0 ≤ T := (τ n).coe_nonneg.trans hT
  calc
    _ ≤ ∑ i ∈ range n, δ * ((τ (i + 1) : ℝ) ^ 2 - (τ i : ℝ) ^ 2) := by
      apply sum_le_sum
      intro i hi
      have hs := hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i)
      rw [hB.integral_integral_sq_sub_sq_eval hs]
      have hdiff : 0 ≤ (τ (i + 1) : ℝ) ^ 2 - (τ i : ℝ) ^ 2 := by
        nlinarith [NNReal.coe_le_coe.mpr hs, (τ i).coe_nonneg]
      calc
        _ = ((τ (i + 1) : ℝ) - τ i) *
            ((τ (i + 1) : ℝ) ^ 2 - (τ i : ℝ) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hδ i (mem_range.mp hi)) hdiff
    _ = δ * ((τ n : ℝ) ^ 2 - (τ 0 : ℝ) ^ 2) := by
      rw [← mul_sum, sum_range_sub (fun i ↦ (τ i : ℝ) ^ 2)]
    _ ≤ _ := by
      have hsq : (τ n : ℝ) ^ 2 ≤ T ^ 2 := by nlinarith [(τ n).coe_nonneg]
      nlinarith [mul_le_mul_of_nonneg_left (show (τ n : ℝ) ^ 2 - (τ 0 : ℝ) ^ 2 ≤ T ^ 2 by
        nlinarith [sq_nonneg (τ 0 : ℝ)]) hδ0]

/-- On the equal `n`-cell grid of `[0,T]`, the time-integrated mean-squared error of the
left-step approximation to `B²` is exactly `T³/n`. -/
theorem sum_integral_integral_sq_sub_sq_eval_uniform (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ range n, ∫ u in (((i : ℝ≥0) * T / n : ℝ≥0) : ℝ)..
        ((((i + 1 : ℕ) : ℝ≥0) * T / n : ℝ≥0) : ℝ),
      ∫ ω, (B u.toNNReal ω ^ 2 - B ((i : ℝ≥0) * T / n) ω ^ 2) ^ 2 ∂P) =
      (T : ℝ) ^ 3 / n := by
  let τ (i : ℕ) : ℝ≥0 := i * T / n
  have hstep (i : ℕ) : τ i ≤ τ (i + 1) := by
    dsimp [τ]
    gcongr
    exact_mod_cast Nat.le_succ i
  have hcell (i : ℕ) :
      (∫ u in (τ i : ℝ)..τ (i + 1),
        ∫ ω, (B u.toNNReal ω ^ 2 - B (τ i) ω ^ 2) ^ 2 ∂P) =
      ((T : ℝ) / n) * ((τ (i + 1) : ℝ) ^ 2 - (τ i : ℝ) ^ 2) := by
    rw [hB.integral_integral_sq_sub_sq_eval (hstep i)]
    dsimp [τ]
    push_cast
    ring
  calc
    _ = ∑ i ∈ range n, ((T : ℝ) / n) *
        ((τ (i + 1) : ℝ) ^ 2 - (τ i : ℝ) ^ 2) := sum_congr rfl fun i _ ↦ hcell i
    _ = ((T : ℝ) / n) * ((τ n : ℝ) ^ 2 - (τ 0 : ℝ) ^ 2) := by
      rw [← mul_sum, sum_range_sub (fun i ↦ (τ i : ℝ) ^ 2)]
    _ = _ := by
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      dsimp [τ]
      push_cast
      field_simp
      ring

/-- Left-step approximations of `B²` converge in time-integrated mean square along any
family of deterministic grids whose mesh tends to zero on a fixed bounded horizon. -/
theorem tendsto_sum_integral_integral_sq_sub_sq_eval (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {τ : ι → ℕ → ℝ≥0} {n : ι → ℕ} {δ : ι → ℝ} {T : ℝ}
    (hτ : ∀ a, MonotoneOn (τ a) (Set.Iic (n a))) (hT : ∀ a, (τ a (n a) : ℝ) ≤ T)
    (hδ0 : ∀ a, 0 ≤ δ a) (hδ : ∀ a, ∀ i < n a, (τ a (i + 1) : ℝ) - τ a i ≤ δ a)
    (hlim : Filter.Tendsto δ l (nhds 0)) :
    Filter.Tendsto (fun a ↦ ∑ i ∈ range (n a), ∫ u in (τ a i : ℝ)..τ a (i + 1),
      ∫ ω, (B u.toNNReal ω ^ 2 - B (τ a i) ω ^ 2) ^ 2 ∂P) l (nhds 0) := by
  apply squeeze_zero (fun a ↦ ?_)
    (fun a ↦ hB.sum_integral_integral_sq_sub_sq_eval_le (hτ a) (hT a) (hδ0 a) (hδ a))
  · simpa using Filter.Tendsto.const_mul (T ^ 2) hlim
  · apply sum_nonneg
    intro i hi
    apply intervalIntegral.integral_nonneg_of_forall
      (NNReal.coe_le_coe.mpr (hτ a (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i)))
    intro u
    exact integral_nonneg fun ω ↦ sq_nonneg _

end ProbabilityTheory.IsPreBrownianReal
