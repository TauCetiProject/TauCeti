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

For nondecreasing deterministic dates `τ` and heights `θ j` known at `τ j`,
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

/-- Only the dates and integrator values through `n`, and heights before `n`,
affect a finite grid likelihood. -/
theorem gridExponential_congr {τ σ : ℕ → ℝ≥0} {θ η : ℕ → Ω → ℝ}
    {W V : ℝ≥0 → Ω → ℝ} {n : ℕ} {ω : Ω}
    (hτ : ∀ j ≤ n, τ j = σ j) (hθ : ∀ j < n, θ j ω = η j ω)
    (hW : ∀ j ≤ n, W (τ j) ω = V (σ j) ω) :
    gridExponential τ θ W n ω = gridExponential σ η V n ω := by
  rw [gridExponential_def, gridExponential_def]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hjn := mem_range.mp hj
  rw [hθ j hjn, hW j (by omega), hW (j + 1) (by omega),
    hτ j (by omega), hτ (j + 1) (by omega)]

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} {K : ℝ} {n : ℕ}

/-- Each grid likelihood is known at the last date used in it. -/
theorem _root_.MeasureTheory.Adapted.measurable_gridExponential (hW : Adapted ℱ W)
    (hτ : MonotoneOn τ (Set.Iic n))
    (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) :
    Measurable[ℱ (τ n)] (gridExponential τ θ W n) := by
  apply Measurable.exp
  apply Finset.measurable_sum
  intro j hj
  have hjn : j + 1 ≤ n := mem_range.mp hj
  have hθj := (hθ j (mem_range.mp hj)).mono
    (ℱ.mono (hτ (a := j) (b := n) (by simp; omega) (by simp) (by omega))) le_rfl
  have h₁ := (hW (τ (j + 1))).mono (ℱ.mono (hτ hjn (by simp) hjn)) le_rfl
  have h₀ := (hW (τ j)).mono
    (ℱ.mono (hτ (a := j) (b := n) (by simp; omega) (by simp) (by omega))) le_rfl
  exact (hθj.mul (h₁.sub h₀)).sub ((hθj.pow_const 2).mul_const _ |>.div_const 2)

/-- A normalized Brownian exponential increment with a left-measurable height
preserves integrability of a left-measurable multiplier. No height bound is needed. -/
theorem IsFilteredPreBrownianReal.integrable_mul_exp_sub
    (hW : IsFilteredPreBrownianReal ℱ W P) {u v : ℝ≥0} (huv : u ≤ v)
    {a X : Ω → ℝ} (ha : Measurable[ℱ u] a)
    (hX : Measurable[ℱ u] X) (hi : Integrable X P) :
    Integrable (fun ω ↦ X ω *
      exp (a ω * (W v ω - W u ω) - a ω ^ 2 * ((v : ℝ) - u) / 2)) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let f := fun z : (ℝ × ℝ) × ℝ ↦
    z.1.1 * exp (z.1.2 * z.2 - z.1.2 ^ 2 * ((v : ℝ) - u) / 2)
  have hf : StronglyMeasurable f := by fun_prop
  have hZ : Measurable (fun ω ↦ W v ω - W u ω) :=
    hW.adapted.measurable.sub hW.adapted.measurable
  have hpair := (hX.prodMk ha).mono (ℱ.le u) le_rfl
  have hlaw : P.map (fun ω ↦ W v ω - W u ω) = gaussianReal 0 (v - u) :=
    (hW.hasLaw_sub_of_le huv).map_eq
  have hprod := map_restrict_prodMk_eq_prod_of_indep (ℱ.le u) (hX.prodMk ha) hZ
    (hW.indep_sub huv) MeasurableSet.univ
  simp only [Measure.restrict_univ, hlaw] at hprod
  have hfi : Integrable f ((P.map (fun ω ↦ (X ω, a ω))).prod (gaussianReal 0 (v - u))) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun x ↦
        ((integrable_exp_mul_gaussianReal x.2).div_const
          (exp (x.2 ^ 2 * ((v : ℝ) - u) / 2))).const_mul x.1 |>.congr
          (ae_of_all _ fun y ↦ by simp [f, exp_sub, mul_div_assoc])
    · have heq (x : ℝ × ℝ) : (∫ y, ‖f (x, y)‖ ∂gaussianReal 0 (v - u)) = |x.1| := by
        simp only [f, norm_mul, Real.norm_eq_abs, abs_exp, integral_const_mul]
        rw [← NNReal.coe_sub huv, mul_comm (x.2 ^ 2),
          integral_exp_mul_sub_gaussianReal, mul_one]
      simp_rw [heq]
      exact (integrable_map_measure (by fun_prop) hpair.aemeasurable).mpr hi.abs
  rw [← hprod, integrable_map_measure hf.aestronglyMeasurable
    (hpair.prodMk hZ).aemeasurable] at hfi
  exact hfi

/-- A normalized Brownian exponential increment with a left-measurable height
has conditional mean equal to its left-measurable multiplier. -/
theorem IsFilteredPreBrownianReal.condExp_mul_exp_sub
    (hW : IsFilteredPreBrownianReal ℱ W P) {u v : ℝ≥0} (huv : u ≤ v)
    {a X : Ω → ℝ} (ha : Measurable[ℱ u] a)
    (hX : Measurable[ℱ u] X) (hi : Integrable X P) :
    P[(fun ω ↦ X ω *
      exp (a ω * (W v ω - W u ω) - a ω ^ 2 * ((v : ℝ) - u) / 2)) | ℱ u] =ᵐ[P] X := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hZ : Measurable (fun ω ↦ W v ω - W u ω) :=
    hW.adapted.measurable.sub hW.adapted.measurable
  have h := condExp_comp_prodMk_ae_eq_integral_of_indep (ℱ.le u) (hX.prodMk ha) hZ
    (hW.indep_sub huv)
    (f := fun z : (ℝ × ℝ) × ℝ ↦
      z.1.1 * exp (z.1.2 * z.2 - z.1.2 ^ 2 * ((v : ℝ) - u) / 2))
    (by fun_prop) (hW.integrable_mul_exp_sub huv ha hX hi)
  have hlaw : P.map (fun ω ↦ W v ω - W u ω) = gaussianReal 0 (v - u) :=
    (hW.hasLaw_sub_of_le huv).map_eq
  simpa only [hlaw, integral_const_mul, ← NNReal.coe_sub huv, mul_comm (a _ ^ 2),
    integral_exp_mul_sub_gaussianReal, mul_one] using h

private theorem gridExponential_step (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic (n + 1)))
    (hθ : ∀ j < n + 1, Measurable[ℱ (τ j)] (θ j))
    (hi : Integrable (gridExponential τ θ W n) P) :
    Integrable (gridExponential τ θ W (n + 1)) P ∧
      P[gridExponential τ θ W (n + 1) | ℱ (τ n)] =ᵐ[P] gridExponential τ θ W n := by
  have huv := hτ (Nat.le_succ n) (by simp) (Nat.le_succ n)
  have hm := hW.adapted.measurable_gridExponential
    (hτ.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ n)))
    (fun j hj ↦ hθ j (by omega))
  simpa only [← gridExponential_succ] using
    And.intro (hW.integrable_mul_exp_sub huv (hθ n (by omega)) hm hi)
      (hW.condExp_mul_exp_sub huv (hθ n (by omega)) hm hi)

/-- A uniform height bound controls the square by the likelihood with doubled heights,
with a factor depending only on elapsed time rather than the grid length. -/
theorem gridExponential_sq_le (hτ : MonotoneOn τ (Set.Iic n)) (ω : Ω)
    (hθK : ∀ j < n, |θ j ω| ≤ K) :
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
        sq_le_sq.mpr ((hθK j (mem_range.mp hj)).trans (le_abs_self K))
      exact mul_le_mul_of_nonneg_right hs
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
          (hτ (by have := mem_range.mp hj; simp; omega)
            (mem_range.mp hj) (Nat.le_succ j))))
    _ = _ := by rw [← mul_sum, sum_range_sub (fun i ↦ (τ i : ℝ))]

namespace IsFilteredPreBrownianReal

/-- Every finite grid likelihood with predictable heights is integrable. -/
theorem integrable_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) :
    Integrable (gridExponential τ θ W n) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  induction n with
  | zero => exact (integrable_const (μ := P) (1 : ℝ)).congr (ae_of_all _ fun ω ↦ by simp)
  | succ n ih =>
    exact (gridExponential_step hW hτ hθ
      (ih (hτ.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ n)))
        (fun j hj ↦ hθ j (by omega)))).1

/-- **Grid exponential martingale.** Sample the filtration at the nondecreasing dates `τ`.
The coefficient on each interval is known at its left endpoint, not its right endpoint. -/
theorem martingale_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j)) :
    Martingale (gridExponential τ θ W) (ℱ.comp hτ) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hi (n : ℕ) := hW.integrable_gridExponential (n := n)
    (hτ.monotoneOn _) (fun j _ ↦ hθ j)
  refine martingale_nat (fun n ↦ ?_) hi fun n ↦ ?_
  · simpa only [Filtration.stronglyMeasurable_comp_iff] using
      (hW.adapted.measurable_gridExponential (n := n) (hτ.monotoneOn _)
        (fun j _ ↦ hθ j)).stronglyMeasurable
  · simpa only [Filtration.comp_apply] using
      (gridExponential_step hW (hτ.monotoneOn _) (fun j _ ↦ hθ j) (hi n)).2.symm

/-- **Normalization.** Predictable grid heights give a likelihood of expectation one. -/
theorem integral_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) :
    ∫ ω, gridExponential τ θ W n ω ∂P = 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  induction n with
  | zero => simp
  | succ n ih =>
    have hτn := hτ.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ n))
    have hθn := fun j (hj : j < n) ↦ hθ j (by omega)
    have hs := gridExponential_step hW hτ hθ (hW.integrable_gridExponential hτn hθn)
    rw [← integral_condExp (ℱ.le (τ n)), integral_congr_ae hs.2, ih hτn hθn]

private theorem gridExponential_square_bound (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j < n, ∀ᵐ ω ∂P, |θ j ω| ≤ K) :
    Integrable (fun ω ↦ gridExponential τ θ W n ω ^ 2) P ∧
      ∫ ω, gridExponential τ θ W n ω ^ 2 ∂P ≤ exp (K ^ 2 * ((τ n : ℝ) - τ 0)) := by
  have h2θ : ∀ j < n, Measurable[ℱ (τ j)] (fun ω ↦ 2 * θ j ω) :=
    fun j hj ↦ (hθ j hj).const_mul 2
  have hi := (hW.integrable_gridExponential hτ h2θ).mul_const
    (exp (K ^ 2 * ((τ n : ℝ) - τ 0)))
  have hb : ∀ᵐ ω ∂P, gridExponential τ θ W n ω ^ 2 ≤
      gridExponential τ (fun j ω ↦ 2 * θ j ω) W n ω * exp (K ^ 2 * ((τ n : ℝ) - τ 0)) := by
    filter_upwards [ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (hK j))] with ω hω
    exact gridExponential_sq_le hτ ω hω
  have hm := (hW.adapted.measurable_gridExponential hτ hθ).mono (ℱ.le _) le_rfl
  have hs : Integrable (fun ω ↦ gridExponential τ θ W n ω ^ 2) P :=
    hi.mono' (hm.pow_const 2).aestronglyMeasurable (by simpa only [norm_pow,
      Real.norm_eq_abs, sq_abs] using hb)
  refine ⟨hs, (integral_mono_ae hs hi hb).trans_eq ?_⟩
  rw [integral_mul_const, hW.integral_gridExponential hτ h2θ, one_mul]

/-- **Uniform second-moment bound.** It depends on the height bound and elapsed time,
not on the number or sizes of the trading intervals. -/
theorem integral_sq_gridExponential_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j < n, ∀ᵐ ω ∂P, |θ j ω| ≤ K) :
    ∫ ω, gridExponential τ θ W n ω ^ 2 ∂P ≤ exp (K ^ 2 * ((τ n : ℝ) - τ 0)) :=
  (gridExponential_square_bound hW hτ hθ hK).2

/-- Finite grid exponential densities with bounded predictable heights belong to `L²`. -/
theorem memLp_two_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j < n, ∀ᵐ ω ∂P, |θ j ω| ≤ K) :
    MemLp (gridExponential τ θ W n) 2 P := by
  have hm := (hW.adapted.measurable_gridExponential hτ hθ).mono (ℱ.le _) le_rfl
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    (gridExponential_square_bound hW hτ hθ hK).1

end IsFilteredPreBrownianReal

end TauCeti.Probability
