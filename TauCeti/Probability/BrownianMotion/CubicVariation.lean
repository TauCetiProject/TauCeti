/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.BigOperators.Fin

/-!
# Cubic sums of Brownian increments

For a deterministic nondecreasing grid, the sum of the cubes of the Brownian increments
has mean zero and second moment `15 ∑ i, (Δtᵢ)³`. Consequently its second moment is at most
`15 (t_last - t_first) δ²` when every grid interval has length at most `δ`.
This gives mean-square convergence to zero along vanishing-mesh grids on a bounded horizon.
The cubic sum is the remainder in the telescoping expansion used to integrate the square
of Brownian motion.

Only the finite-dimensional Brownian laws are needed: no path regularity or filtration
hypothesis is imposed. Empty grids and repeated times are allowed.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

noncomputable section

open MeasureTheory Finset Filter
open scoped NNReal Topology

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {n : ℕ} {τ : Fin (n + 1) → ℝ≥0}

/-- Every Brownian increment has zero third moment. -/
theorem integral_cube_sub (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ∫ ω, (B t ω - B s ω) ^ 3 ∂P = 0 := by
  have h := TauCeti.Probability.centralMoment_id_two_mul_add_one_gaussianReal
    0 (nndist (t : ℝ) (s : ℝ)) 1
  simp only [centralMoment, integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply,
    id_eq, sub_zero] at h
  norm_num at h
  simpa using ((hB.hasLaw_sub t s).integral_comp
    (f := fun x : ℝ => x ^ 3) (by fun_prop)).trans h

/-- The sixth moment of a Brownian increment of length `t - s` is `15 (t - s)³`. -/
theorem integral_pow_six_sub (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (B t ω - B s ω) ^ 6 ∂P = 15 * ((t : ℝ) - s) ^ 3 := by
  have h := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 (t - s) 3
  norm_num [Nat.doubleFactorial, NNReal.coe_sub hst] at h
  simpa [mul_comm] using ((hB.hasLaw_sub_of_le hst).integral_comp
    (f := fun x : ℝ => x ^ 6) (by fun_prop)).trans h

/-- The cubic increments on a deterministic grid are square-integrable. -/
theorem memLp_cube_sub (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    MemLp (fun ω => (B t ω - B s ω) ^ 3) 2 P := by
  have h := TauCeti.memLp_two_eval_gaussianReal 0 (nndist (t : ℝ) (s : ℝ))
    (Polynomial.X ^ 3)
  simp_rw [Polynomial.eval_X_pow] at h
  exact (hB.hasLaw_sub t s).memLp_comp h

/-- The sum of cubic increments on any deterministic grid has mean zero. -/
theorem integral_sum_cube_sub (hB : IsPreBrownianReal B P) :
    ∫ ω, ∑ i : Fin n, (B (τ i.succ) ω - B (τ i.castSucc) ω) ^ 3 ∂P = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [integral_finsetSum _ fun i _ => (hB.memLp_cube_sub _ _).integrable (by norm_num)]
  exact sum_eq_zero fun i _ => hB.integral_cube_sub _ _

/-- The exact second moment of the cubic-increment sum on a deterministic grid.
Independence removes the off-diagonal terms, while each diagonal term is a sixth moment. -/
theorem integral_sq_sum_cube_sub (hB : IsPreBrownianReal B P) (hτ : Monotone τ) :
    ∫ ω, (∑ i : Fin n, (B (τ i.succ) ω - B (τ i.castSucc) ω) ^ 3) ^ 2 ∂P =
      15 * ∑ i : Fin n, ((τ i.succ : ℝ) - τ i.castSucc) ^ 3 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmem (i : Fin n) := hB.memLp_cube_sub (τ i.castSucc) (τ i.succ)
  have hind := (hB.hasIndepIncrements n τ hτ).comp (fun _ => fun x : ℝ => x ^ 3) (by fun_prop)
  have hvar := IndepFun.variance_sum (s := univ) (fun i _ => hmem i)
    (fun i _ j _ hij => hind.indepFun hij)
  rw [variance_eq_integral (memLp_finsetSum' univ (fun i _ => hmem i)).aemeasurable] at hvar
  simp_rw [Finset.sum_apply] at hvar
  rw [hB.integral_sum_cube_sub] at hvar
  simp only [sub_zero] at hvar
  rw [hvar, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [variance_eq_integral (hmem i).aemeasurable,
    hB.integral_cube_sub]
  simpa only [sub_zero, ← pow_mul] using
    hB.integral_pow_six_sub (hτ (Fin.castSucc_le_succ i))

/-- A mesh bound for the second moment of the sum of cubic Brownian increments.
The total length is the difference of the two endpoints, including for an empty grid. -/
theorem integral_sq_sum_cube_sub_le (hB : IsPreBrownianReal B P) (hτ : Monotone τ)
    {δ : ℝ≥0} (hmesh : ∀ i : Fin n, (τ i.succ : ℝ) - τ i.castSucc ≤ δ) :
    ∫ ω, (∑ i : Fin n, (B (τ i.succ) ω - B (τ i.castSucc) ω) ^ 3) ^ 2 ∂P ≤
      15 * ((τ (Fin.last n) : ℝ) - τ 0) * (δ : ℝ) ^ 2 := by
  rw [hB.integral_sq_sum_cube_sub hτ]
  have hsum : ∑ i : Fin n, ((τ i.succ : ℝ) - τ i.castSucc) =
      (τ (Fin.last n) : ℝ) - τ 0 := by
    rw [sum_sub_distrib]
    linarith [Fin.sum_univ_succ (fun i => (τ i : ℝ)),
      Fin.sum_univ_castSucc (fun i => (τ i : ℝ))]
  calc
    _ ≤ 15 * ∑ i : Fin n, ((τ i.succ : ℝ) - τ i.castSucc) * (δ : ℝ) ^ 2 := by
      gcongr with i
      have hd : 0 ≤ (τ i.succ : ℝ) - τ i.castSucc :=
        sub_nonneg.mpr (by exact_mod_cast hτ (Fin.castSucc_le_succ i))
      have hs := sq_le_sq₀ hd δ.coe_nonneg |>.mpr (hmesh i)
      nlinarith
    _ = _ := by rw [← sum_mul, hsum]; ring

/-- Cubic-increment sums converge to zero in mean square along any deterministic
vanishing-mesh sequence on a bounded time horizon. The number of intervals may vary. -/
theorem tendsto_integral_sq_sum_cube_sub (hB : IsPreBrownianReal B P)
    {N : ℕ → ℕ} {grid : (k : ℕ) → Fin (N k + 1) → ℝ≥0} {T : ℝ≥0} {δ : ℕ → ℝ≥0}
    (hgrid : ∀ k, Monotone (grid k)) (hT : ∀ k, grid k (Fin.last (N k)) ≤ T)
    (hmesh : ∀ k (i : Fin (N k)), (grid k i.succ : ℝ) - grid k i.castSucc ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω,
      (∑ i : Fin (N k), (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 3) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hbound k := hB.integral_sq_sum_cube_sub_le (hgrid k) (hmesh k)
  have hδ' : Tendsto (fun k => (δ k : ℝ)) atTop (𝓝 0) := by
    exact NNReal.continuous_coe.tendsto 0 |>.comp hδ
  refine squeeze_zero (fun k => integral_nonneg fun ω => sq_nonneg _) (fun k => ?_)
    (by simpa using (hδ'.pow 2).const_mul (15 * (T : ℝ)))
  refine (hbound k).trans ?_
  gcongr
  exact (sub_le_self _ (grid k 0).coe_nonneg).trans (by exact_mod_cast hT k)

/-- On the equal `n`-interval grid of `[0,T]`, the cubic sum has second moment
`15 T³/n²`. For `n = 0` the sum is empty and both sides are zero. -/
theorem integral_sq_sum_cube_sub_uniform (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, (∑ i : Fin n,
      (B ((i.succ : ℕ) * T / n) ω - B ((i.castSucc : ℕ) * T / n) ω) ^ 3) ^ 2 ∂P =
      15 * (T : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
  have hmono : Monotone (fun i : Fin (n + 1) => (i : ℕ) * T / n) := by
    intro i j hij
    dsimp only
    gcongr
    exact_mod_cast hij
  rw [hB.integral_sq_sum_cube_sub hmono]
  have hstep (i : Fin n) :
      (((i.succ : ℕ) * T / n : ℝ≥0) : ℝ) - ((i.castSucc : ℕ) * T / n : ℝ≥0) =
        (T : ℝ) / n := by
    push_cast
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [hstep, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · field_simp

end ProbabilityTheory.IsPreBrownianReal
