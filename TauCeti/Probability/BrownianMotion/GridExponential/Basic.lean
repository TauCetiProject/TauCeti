/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Distributions.Gaussian.Conditional.Exponential
public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.Process.Filtration.Comp
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exponential densities on Brownian grids

For nondecreasing deterministic dates `τ` and bounded heights `θ j` known at `τ j`,
`gridExponential τ θ W n` is the exponential of the first `n` weighted Brownian increments,
minus half their quadratic energy. These likelihoods are positive, have expectation one,
and form a martingale on the sampled filtration. Their second moments are bounded by
`exp (K² (τ n - τ 0))` when every height is bounded by `K`.

The bound is independent of the number and spacing of the dates. In particular it supplies
the uniform second-moment estimate needed when approximating bounded predictable drifts
by grid processes. This file concerns finite sums only, not a completed stochastic integral.
Repeated dates and the empty sum are allowed; the first date need not be zero.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.5 (exponential densities and bounded integrands).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*}

/-- The normalized exponential of finitely many increments with left-endpoint heights.
The normalization is half the sum of squared heights times interval lengths. -/
def gridExponential (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  exp (∑ j ∈ range n, (θ j ω * (W (τ (j + 1)) ω - W (τ j) ω) -
    θ j ω ^ 2 * ((τ (j + 1) : ℝ) - τ j) / 2))

theorem gridExponential_def (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    gridExponential τ θ W n ω =
      exp (∑ j ∈ range n, (θ j ω * (W (τ (j + 1)) ω - W (τ j) ω) -
        θ j ω ^ 2 * ((τ (j + 1) : ℝ) - τ j) / 2)) := (rfl)

@[simp]
theorem gridExponential_zero (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) : gridExponential τ θ W 0 = 1 := by
  funext ω
  simp [gridExponential_def]

/-- Zero heights give the unit density. -/
@[simp]
theorem gridExponential_zero_height (τ : ℕ → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    gridExponential τ 0 W n = 1 := by
  funext ω
  simp [gridExponential_def]

/-- Appending an interval multiplies the density by its normalized exponential increment. -/
theorem gridExponential_succ (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    gridExponential τ θ W (n + 1) ω = gridExponential τ θ W n ω *
      exp (θ n ω * (W (τ (n + 1)) ω - W (τ n) ω) -
        θ n ω ^ 2 * ((τ (n + 1) : ℝ) - τ n) / 2) := by
  rw [gridExponential_def, gridExponential_def, sum_range_succ, exp_add]

/-- Grid exponential densities are strictly positive, without probabilistic assumptions. -/
theorem gridExponential_pos (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 < gridExponential τ θ W n ω :=
  exp_pos _

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} {K : ℝ}

/-- Each grid likelihood is known at the last date used in it. -/
theorem _root_.MeasureTheory.Adapted.measurable_gridExponential (hW : Adapted ℱ W) (hτ : Monotone τ)
    (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j)) (n : ℕ) :
    Measurable[ℱ (τ n)] (gridExponential τ θ W n) := by
  apply Measurable.exp
  apply Finset.measurable_sum
  intro j hj
  have hjn : j + 1 ≤ n := mem_range.mp hj
  have hθj := (hθ j).mono (ℱ.mono (hτ (by omega : j ≤ n))) le_rfl
  have h₁ := (hW (τ (j + 1))).mono (ℱ.mono (hτ hjn)) le_rfl
  have h₀ := (hW (τ j)).mono (ℱ.mono (hτ (by omega : j ≤ n))) le_rfl
  exact (hθj.mul (h₁.sub h₀)).sub ((hθj.pow_const 2).mul_const _ |>.div_const 2)

/-- A normalized Brownian exponential increment with a bounded left-measurable height
preserves integrability and has conditional mean equal to its left-measurable multiplier. -/
private theorem IsFilteredPreBrownianReal.integrable_mul_exp_sub_and_condExp
    (hW : IsFilteredPreBrownianReal ℱ W P) {u v : ℝ≥0} (huv : u ≤ v)
    {a X : Ω → ℝ} (ha : Measurable[ℱ u] a) (hK : ∀ᵐ ω ∂P, |a ω| ≤ K)
    (hX : Measurable[ℱ u] X) (hi : Integrable X P) :
    Integrable (fun ω ↦ X ω *
      exp (a ω * (W v ω - W u ω) - a ω ^ 2 * ((v : ℝ) - u) / 2)) P ∧
      P[(fun ω ↦ X ω *
        exp (a ω * (W v ω - W u ω) - a ω ^ 2 * ((v : ℝ) - u) / 2)) | ℱ u] =ᵐ[P] X := by
  let d : ℝ := (v : ℝ) - u
  have hd : 0 ≤ d := sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv)
  let Y := fun ω ↦ X ω * exp (-(a ω ^ 2 * d / 2))
  have hYm : Measurable[ℱ u] Y :=
    hX.mul ((ha.pow_const 2 |>.mul_const d |>.div_const 2).neg.exp)
  have ham : Measurable a := ha.mono (ℱ.le _) le_rfl
  have hYi : Integrable Y P := hi.mul_bdd (by fun_prop) (c := 1) (by
    filter_upwards [] with ω
    simpa only [norm_eq_abs, abs_exp, exp_le_one_iff] using
      neg_nonpos.mpr (div_nonneg (mul_nonneg (sq_nonneg _) hd) (by positivity)))
  have hZ : Measurable (fun ω ↦ W v ω - W u ω) :=
    hW.adapted.measurable.sub hW.adapted.measurable
  have hind := hW.indep_sub huv
  have hlaw := hW.hasLaw_sub_of_le huv
  have heq : (fun ω ↦ Y ω * exp (a ω * (W v ω - W u ω))) =
      (fun ω ↦ X ω * exp (a ω * (W v ω - W u ω) - a ω ^ 2 * ((v : ℝ) - u) / 2)) := by
    funext ω
    dsimp only [Y, d]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  refine ⟨heq ▸ integrable_mul_exp_of_indep_gaussian (ℱ.le _) hYm ha hZ hind hlaw hYi hK, ?_⟩
  have hc := condExp_mul_exp_of_indep_gaussian (ℱ.le _) hYm ha hZ hind hlaw hYi hK
  simp only [zero_mul, zero_add] at hc
  rw [heq] at hc
  filter_upwards [hc] with ω hω
  rw [hω, NNReal.coe_sub huv]
  dsimp only [Y, d]
  rw [mul_assoc, ← exp_add]
  have hz : -(a ω ^ 2 * ((v : ℝ) - u) / 2) +
      ((v : ℝ) - u) * a ω ^ 2 / 2 = 0 := by ring
  rw [hz, exp_zero, mul_one]

/-- A normalized Brownian exponential increment with a bounded left-measurable height
preserves integrability of a left-measurable multiplier. -/
theorem IsFilteredPreBrownianReal.integrable_mul_exp_sub
    (hW : IsFilteredPreBrownianReal ℱ W P) {u v : ℝ≥0} (huv : u ≤ v)
    {a X : Ω → ℝ} (ha : Measurable[ℱ u] a) (hK : ∀ᵐ ω ∂P, |a ω| ≤ K)
    (hX : Measurable[ℱ u] X) (hi : Integrable X P) :
    Integrable (fun ω ↦ X ω *
      exp (a ω * (W v ω - W u ω) - a ω ^ 2 * ((v : ℝ) - u) / 2)) P :=
  (hW.integrable_mul_exp_sub_and_condExp huv ha hK hX hi).1

/-- A normalized Brownian exponential increment with a bounded left-measurable height
has conditional mean equal to its left-measurable multiplier. -/
theorem IsFilteredPreBrownianReal.condExp_mul_exp_sub
    (hW : IsFilteredPreBrownianReal ℱ W P) {u v : ℝ≥0} (huv : u ≤ v)
    {a X : Ω → ℝ} (ha : Measurable[ℱ u] a) (hK : ∀ᵐ ω ∂P, |a ω| ≤ K)
    (hX : Measurable[ℱ u] X) (hi : Integrable X P) :
    P[(fun ω ↦ X ω *
      exp (a ω * (W v ω - W u ω) - a ω ^ 2 * ((v : ℝ) - u) / 2)) | ℱ u] =ᵐ[P] X :=
  (hW.integrable_mul_exp_sub_and_condExp huv ha hK hX hi).2

private theorem gridExponential_step (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ)
    (hi : Integrable (gridExponential τ θ W n) P) :
    Integrable (gridExponential τ θ W (n + 1)) P ∧
      P[gridExponential τ θ W (n + 1) | ℱ (τ n)] =ᵐ[P] gridExponential τ θ W n := by
  simpa only [← gridExponential_succ] using
    hW.integrable_mul_exp_sub_and_condExp (hτ (Nat.le_succ n)) (hθ n) (hK n)
      (hW.adapted.measurable_gridExponential hτ hθ n) hi

/-- A uniform height bound controls the square by the likelihood with doubled heights,
with a factor depending only on elapsed time rather than the grid length. -/
theorem gridExponential_sq_le (hτ : Monotone τ) (n : ℕ) (ω : Ω)
    (hθK : ∀ j ∈ range n, |θ j ω| ≤ K) :
    gridExponential τ θ W n ω ^ 2 ≤ gridExponential τ (fun j ω ↦ 2 * θ j ω) W n ω *
      exp (K ^ 2 * ((τ n : ℝ) - τ 0)) := by
  have heq : gridExponential τ θ W n ω ^ 2 =
      gridExponential τ (fun j ω ↦ 2 * θ j ω) W n ω *
        exp (∑ j ∈ range n, θ j ω ^ 2 * ((τ (j + 1) : ℝ) - τ j)) := by
    rw [gridExponential_def, gridExponential_def, ← exp_nat_mul, ← exp_add]
    congr 1
    simp only [Nat.cast_ofNat, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (gridExponential_pos _ _ _ _ _))
  apply exp_le_exp.mpr
  calc
    _ ≤ ∑ j ∈ range n, K ^ 2 * ((τ (j + 1) : ℝ) - τ j) := by
      apply sum_le_sum
      intro j hj
      have hs : θ j ω ^ 2 ≤ K ^ 2 :=
        sq_le_sq.mpr ((hθK j hj).trans (le_abs_self K))
      exact mul_le_mul_of_nonneg_right hs
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hτ (Nat.le_succ j))))
    _ = _ := by rw [← mul_sum, sum_range_sub (fun i ↦ (τ i : ℝ))]

namespace IsFilteredPreBrownianReal

/-- Every finite grid likelihood with bounded predictable heights is integrable. -/
theorem integrable_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) :
    Integrable (gridExponential τ θ W n) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  induction n with
  | zero => exact (integrable_const (μ := P) (1 : ℝ)).congr (ae_of_all _ fun ω ↦ by simp)
  | succ n ih => exact (gridExponential_step hW hτ hθ hK n ih).1

/-- **Grid exponential martingale.** Sample the filtration at the nondecreasing dates `τ`.
The coefficient on each interval is known at its left endpoint, not its right endpoint. -/
theorem martingale_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) :
    Martingale (gridExponential τ θ W) (ℱ.comp hτ) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine martingale_nat (fun n ↦ ?_)
    (hW.integrable_gridExponential hτ hθ hK) fun n ↦ ?_
  · simpa only [Filtration.stronglyMeasurable_comp_iff] using
      (hW.adapted.measurable_gridExponential hτ hθ n).stronglyMeasurable
  · simpa only [Filtration.comp_apply] using
      (gridExponential_step hW hτ hθ hK n (hW.integrable_gridExponential hτ hθ hK n)).2.symm

/-- **Normalization.** Bounded predictable grid heights give a likelihood of expectation one. -/
theorem integral_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) :
    ∫ ω, gridExponential τ θ W n ω ∂P = 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have h := (hW.martingale_gridExponential hτ hθ hK).setIntegral_eq (Nat.zero_le n)
    MeasurableSet.univ
  simpa using h.symm

private theorem gridExponential_square_bound (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) :
    Integrable (fun ω ↦ gridExponential τ θ W n ω ^ 2) P ∧
      ∫ ω, gridExponential τ θ W n ω ^ 2 ∂P ≤ exp (K ^ 2 * ((τ n : ℝ) - τ 0)) := by
  have h2θ : ∀ j, Measurable[ℱ (τ j)] (fun ω ↦ 2 * θ j ω) := fun j ↦ (hθ j).const_mul 2
  have h2K : ∀ j, ∀ᵐ ω ∂P, |2 * θ j ω| ≤ 2 * K := by
    intro j
    filter_upwards [hK j] with ω hω
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      mul_le_mul_of_nonneg_left hω (by norm_num : (0 : ℝ) ≤ 2)
  have hi := (hW.integrable_gridExponential hτ h2θ h2K n).mul_const
    (exp (K ^ 2 * ((τ n : ℝ) - τ 0)))
  have hb : ∀ᵐ ω ∂P, gridExponential τ θ W n ω ^ 2 ≤
      gridExponential τ (fun j ω ↦ 2 * θ j ω) W n ω * exp (K ^ 2 * ((τ n : ℝ) - τ 0)) := by
    filter_upwards [ae_all_iff.mpr hK] with ω hω
    exact gridExponential_sq_le hτ n ω fun j _ ↦ hω j
  have hm := (hW.adapted.measurable_gridExponential hτ hθ n).mono (ℱ.le _) le_rfl
  have hs : Integrable (fun ω ↦ gridExponential τ θ W n ω ^ 2) P :=
    hi.mono' (hm.pow_const 2).aestronglyMeasurable (by simpa only [norm_pow,
      Real.norm_eq_abs, sq_abs] using hb)
  refine ⟨hs, (integral_mono_ae hs hi hb).trans_eq ?_⟩
  rw [integral_mul_const, hW.integral_gridExponential hτ h2θ h2K n, one_mul]

/-- **Uniform second-moment bound.** It depends on the height bound and elapsed time,
not on the number or sizes of the trading intervals. -/
theorem integral_sq_gridExponential_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) :
    ∫ ω, gridExponential τ θ W n ω ^ 2 ∂P ≤ exp (K ^ 2 * ((τ n : ℝ) - τ 0)) :=
  (gridExponential_square_bound hW hτ hθ hK n).2

/-- Finite grid exponential densities with bounded predictable heights belong to `L²`. -/
theorem memLp_two_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) :
    MemLp (gridExponential τ θ W n) 2 P := by
  have hm := (hW.adapted.measurable_gridExponential hτ hθ n).mono (ℱ.le _) le_rfl
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    (gridExponential_square_bound hW hτ hθ hK n).1

end IsFilteredPreBrownianReal

end TauCeti.Probability
