/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Algebra.BigOperators.Fin
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mean-square errors for left-step approximations of squared Brownian motion

For pre-Brownian motion `B`, the mean-square increment of `B²` is
`E[(B_t² - B_s²)²] = 4s(t-s) + 3(t-s)²` for `s ≤ t`. Integrating this over a grid
cell `[a,b]` gives `2a(b-a)² + (b-a)³`. Summing over a deterministic partition therefore
computes the exact time-integrated mean-square error of its left-step approximation.
For the equal `n`-grid of `[0,T]` the error is `T³/n`; for arbitrary nondecreasing grids
it is bounded by a constant times the mesh and tends to zero with the mesh.

These estimates supply the integrand-convergence part of the polynomial stochastic-integral
construction for `B²`. The time integrals here are iterated integrals, with expectation taken
first. Their integrands are explicit polynomials in time by the moment identity. Thus neither
joint measurability of an arbitrary raw version nor path continuity is required. No stochastic
integral is constructed here. Repeated dates and the empty zero-horizon grid are allowed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3, for the polynomial Itô approximation.
-/

open MeasureTheory ProbabilityTheory TauCeti.Probability Finset Filter Set
open scoped NNReal Topology

public section

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The mean-square increment of squared Brownian motion, for `s ≤ t`. This is distinct
from the fourth moment of the Brownian increment. -/
theorem integral_sq_sq_sub_sq (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (B t ω ^ 2 - B s ω ^ 2) ^ 2 ∂P =
      4 * (s : ℝ) * ((t : ℝ) - s) + 3 * ((t : ℝ) - s) ^ 2 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hi : IndepFun (B s) (fun ω ↦ B t ω - B s ω) P := by
    have h := (hB.indepFun_shift s).symm.comp
      (measurable_pi_apply (⟨s, self_mem_Iic⟩ : Iic s)) (measurable_pi_apply (t - s))
    simpa only [Function.comp_def, add_tsub_cancel_of_le hst, Pi.sub_apply] using h
  have hp (u : ℝ≥0) (k : ℕ) : Integrable (fun ω ↦ B u ω ^ k) P :=
    (hB.hasLaw_eval u).integrable_comp (TauCeti.integrable_pow_gaussianReal 0 u k)
  have h2 : IndepFun (fun ω ↦ B s ω ^ 2) (fun ω ↦ (B t ω - B s ω) ^ 2) P :=
    hi.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have h3 : IndepFun (B s) (fun ω ↦ (B t ω - B s ω) ^ 3) P :=
    hi.comp measurable_id (measurable_id.pow_const 3)
  have h2i : Integrable (fun ω ↦ B s ω ^ 2 * (B t ω - B s ω) ^ 2) P :=
    h2.integrable_mul (hp s 2) (hB.integrable_pow_sub s t 2)
  have h3i : Integrable (fun ω ↦ B s ω * (B t ω - B s ω) ^ 3) P :=
    h3.integrable_mul (hB.integrable_eval s) (hB.integrable_pow_sub s t 3)
  have h2v : ∫ ω, B s ω ^ 2 ∂P = (s : ℝ) := by
    calc
      _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 s :=
        (hB.hasLaw_eval s).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
      _ = _ := by rw [integral_sq_gaussianReal]; simp
  calc
    _ = ∫ ω, 4 * (B s ω ^ 2 * (B t ω - B s ω) ^ 2) +
        4 * (B s ω * (B t ω - B s ω) ^ 3) + (B t ω - B s ω) ^ 4 ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω ↦ by ring
    _ = 4 * ((∫ ω, B s ω ^ 2 ∂P) * ∫ ω, (B t ω - B s ω) ^ 2 ∂P) +
        4 * ((∫ ω, B s ω ∂P) * ∫ ω, (B t ω - B s ω) ^ 3 ∂P) +
        ∫ ω, (B t ω - B s ω) ^ 4 ∂P := by
      rw [integral_add (f := fun ω ↦ 4 * (B s ω ^ 2 * (B t ω - B s ω) ^ 2) +
            4 * (B s ω * (B t ω - B s ω) ^ 3))
          ((h2i.const_mul 4).add (h3i.const_mul 4)) (hB.integrable_pow_sub s t 4),
        integral_add (h2i.const_mul 4) (h3i.const_mul 4), integral_const_mul,
        integral_const_mul, h2.integral_fun_mul_eq_mul_integral (hp s 2).aestronglyMeasurable
          (hB.integrable_pow_sub s t 2).aestronglyMeasurable,
        h3.integral_fun_mul_eq_mul_integral (hB.integrable_eval s).aestronglyMeasurable
          (hB.integrable_pow_sub s t 3).aestronglyMeasurable]
    _ = _ := by
      rw [h2v, hB.integral_sq_sub_of_le hst, hB.integral_eval,
        hB.integral_pow_four_sub_of_le hst]
      ring

/-- The exact time-integrated mean-square error on one left-step cell.
Time is integrated on the real line; `toNNReal` only extends evaluation outside its domain. -/
theorem integral_integral_sq_sq_sub_sq (hB : IsPreBrownianReal B P) {a b : ℝ≥0}
    (hab : a ≤ b) :
    (∫ u in (a : ℝ)..b, ∫ ω, (B u.toNNReal ω ^ 2 - B a ω ^ 2) ^ 2 ∂P) =
      2 * (a : ℝ) * ((b : ℝ) - a) ^ 2 + ((b : ℝ) - a) ^ 3 := by
  have hab' : (a : ℝ) ≤ b := hab
  have hm : (∫ u in (a : ℝ)..b, ∫ ω, (B u.toNNReal ω ^ 2 - B a ω ^ 2) ^ 2 ∂P) =
      ∫ u in (a : ℝ)..b, 4 * (a : ℝ) * (u - a) + 3 * (u - a) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hab'] at hu
    have hau : a ≤ u.toNNReal := by
      exact_mod_cast hu.1.trans_eq (Real.coe_toNNReal u (a.coe_nonneg.trans hu.1)).symm
    dsimp only
    rw [hB.integral_sq_sq_sub_sq hau, Real.coe_toNNReal u (a.coe_nonneg.trans hu.1)]
  have hlin : Continuous (fun u : ℝ ↦ 4 * (a : ℝ) * (u - a)) := by fun_prop
  have hquad : Continuous (fun u : ℝ ↦ 3 * (u - a) ^ 2) := by fun_prop
  rw [hm, intervalIntegral.integral_add
    (hlin.intervalIntegrable _ _) (hquad.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (f := fun x : ℝ ↦ x) (a : ℝ),
    intervalIntegral.integral_comp_sub_right (f := fun x : ℝ ↦ x ^ 2) (a : ℝ)]
  simp only [sub_self, integral_id, integral_pow,
    zero_pow (by decide : 3 ≠ 0), zero_pow two_ne_zero, sub_zero]
  ring

/-- The exact integrated mean-square error of the left-step approximation to `B²`.
The formula permits repeated dates and any nonnegative initial date. -/
theorem sum_integral_integral_sq_sq_sub_sq (hB : IsPreBrownianReal B P)
    {n : ℕ} {τ : Fin (n + 1) → ℝ≥0} (hτ : Monotone τ) :
    (∑ i : Fin n, ∫ u in (τ i.castSucc : ℝ)..τ i.succ,
      ∫ ω, (B u.toNNReal ω ^ 2 - B (τ i.castSucc) ω ^ 2) ^ 2 ∂P) =
      ∑ i : Fin n, (2 * (τ i.castSucc : ℝ) * ((τ i.succ : ℝ) - τ i.castSucc) ^ 2 +
        ((τ i.succ : ℝ) - τ i.castSucc) ^ 3) := by
  exact sum_congr rfl fun i _ ↦ hB.integral_integral_sq_sq_sub_sq (hτ (Fin.castSucc_le_succ i))

/-- A mesh bound for the integrated mean-square error of the left-step approximation to
squared Brownian motion. It is at most `δ (b²-a²)` on a grid spanning `[a,b]`. -/
theorem sum_integral_integral_sq_sq_sub_sq_le (hB : IsPreBrownianReal B P)
    {n : ℕ} {τ : Fin (n + 1) → ℝ≥0} (hτ : Monotone τ) {δ : ℝ}
    (hmesh : ∀ i : Fin n, (τ i.succ : ℝ) - τ i.castSucc ≤ δ) :
    (∑ i : Fin n, ∫ u in (τ i.castSucc : ℝ)..τ i.succ,
      ∫ ω, (B u.toNNReal ω ^ 2 - B (τ i.castSucc) ω ^ 2) ^ 2 ∂P) ≤
      δ * ((τ (Fin.last n) : ℝ) ^ 2 - (τ 0 : ℝ) ^ 2) := by
  rw [hB.sum_integral_integral_sq_sq_sub_sq hτ,
    ← Fin.sum_univ_succ_sub_castSucc (fun i ↦ (τ i : ℝ) ^ 2), mul_sum]
  refine sum_le_sum fun i _ ↦ ?_
  have hab : (τ i.castSucc : ℝ) ≤ τ i.succ := hτ (Fin.castSucc_le_succ i)
  have hs : 0 ≤ (τ i.succ : ℝ) ^ 2 - (τ i.castSucc : ℝ) ^ 2 := by
    nlinarith [(τ i.castSucc).coe_nonneg]
  calc
    _ = ((τ i.succ : ℝ) - τ i.castSucc) *
        ((τ i.succ : ℝ) ^ 2 - (τ i.castSucc : ℝ) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hmesh i) hs

/-- On a constant-step grid the integrated mean-square error is exactly the step length
multiplied by the increment of squared time. In particular it is `T³/n` on the equal `n`-grid
of `[0,T]`, for `n > 0`. -/
theorem sum_integral_integral_sq_sq_sub_sq_of_const_step (hB : IsPreBrownianReal B P)
    {n : ℕ} {τ : Fin (n + 1) → ℝ≥0} (hτ : Monotone τ) {δ : ℝ}
    (hstep : ∀ i : Fin n, (τ i.succ : ℝ) - τ i.castSucc = δ) :
    (∑ i : Fin n, ∫ u in (τ i.castSucc : ℝ)..τ i.succ,
      ∫ ω, (B u.toNNReal ω ^ 2 - B (τ i.castSucc) ω ^ 2) ^ 2 ∂P) =
      δ * ((τ (Fin.last n) : ℝ) ^ 2 - (τ 0 : ℝ) ^ 2) := by
  rw [hB.sum_integral_integral_sq_sq_sub_sq hτ,
    ← Fin.sum_univ_succ_sub_castSucc (fun i ↦ (τ i : ℝ) ^ 2), mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  calc
    _ = ((τ i.succ : ℝ) - τ i.castSucc) *
        ((τ i.succ : ℝ) ^ 2 - (τ i.castSucc : ℝ) ^ 2) := by ring
    _ = _ := by rw [hstep i]

/-- The time-integrated mean-square error on the equal `n`-grid of `[0,T]` is exactly `T³/n`.
The grid is specified by its values, so no separate monotonicity premise is needed. -/
theorem sum_integral_integral_sq_sq_sub_sq_uniform (hB : IsPreBrownianReal B P)
    {n : ℕ} (hn : 0 < n) (T : ℝ≥0) {τ : Fin (n + 1) → ℝ≥0}
    (hgrid : ∀ i, τ i = (i.val : ℝ≥0) * T / n) :
    (∑ i : Fin n, ∫ u in (τ i.castSucc : ℝ)..τ i.succ,
      ∫ ω, (B u.toNNReal ω ^ 2 - B (τ i.castSucc) ω ^ 2) ^ 2 ∂P) =
      (T : ℝ) ^ 3 / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hτ : Monotone τ := by
    intro i j hij
    rw [hgrid i, hgrid j]
    gcongr
    exact_mod_cast hij
  have hstep (i : Fin n) : (τ i.succ : ℝ) - τ i.castSucc = (T : ℝ) / n := by
    simp only [hgrid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
      Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, NNReal.coe_add,
      NNReal.coe_one]
    ring
  rw [hB.sum_integral_integral_sq_sq_sub_sq_of_const_step hτ hstep, hgrid (Fin.last n), hgrid 0]
  simp only [Fin.val_last, Fin.val_zero, Nat.cast_zero, zero_mul, zero_div, NNReal.coe_zero,
    zero_pow two_ne_zero, sub_zero, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
  field_simp [hn']

/-- Every deterministic vanishing-mesh family approximates `B²` in time-integrated
mean square. The grids may vary in length and need not be nested. -/
theorem tendsto_sum_integral_integral_sq_sq_sub_sq (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
    {a b : ℝ≥0} (hτ : ∀ k, Monotone (grid k)) (ha : ∀ k, grid k 0 = a)
    (hb : ∀ k, grid k (Fin.last (N k)) = b) {δ : ι → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), (grid k i.succ : ℝ) - grid k i.castSucc ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i : Fin (N k), ∫ u in (grid k i.castSucc : ℝ)..grid k i.succ,
      ∫ ω, (B u.toNNReal ω ^ 2 - B (grid k i.castSucc) ω ^ 2) ^ 2 ∂P) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hδ.mul_const ((b : ℝ) ^ 2 - (a : ℝ) ^ 2)) ?_ ?_
  · intro k
    apply sum_nonneg
    intro i _
    exact intervalIntegral.integral_nonneg
      (hτ k (Fin.castSucc_le_succ i)) (fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _)
  · intro k
    simpa only [ha k, hb k] using hB.sum_integral_integral_sq_sq_sub_sq_le (hτ k) (hmesh k)

end ProbabilityTheory.IsPreBrownianReal
