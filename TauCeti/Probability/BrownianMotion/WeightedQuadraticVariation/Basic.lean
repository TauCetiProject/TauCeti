/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Independence.Integration

/-!
# Centered weighted Brownian quadratic sums

For deterministic dates `tᵢ` and square-integrable heights `Hᵢ` measurable at `tᵢ`,
this file proves the exact identity

`E[(∑ᵢ Hᵢ ((B(tᵢ₊₁) - B(tᵢ))² - (tᵢ₊₁ - tᵢ)))²]
  = 2 ∑ᵢ E[Hᵢ²] (tᵢ₊₁ - tᵢ)²`.

The summands are orthogonal, not generally independent: the later height may depend on
all earlier increments. Specializing to `Hᵢ = B(tᵢ)` gives the centered quadratic error
in the partition proof of the cubic Itô formula. Empty grids and repeated dates are allowed.
Only the filtered
pre-Brownian laws are used; path continuity and usual filtration conditions are unnecessary.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

private theorem indepFun_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) :
    IndepFun Y (fun ω ↦ (B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) P :=
  (hB.indepFun_sub hst hY).comp measurable_id
    ((measurable_id.pow_const 2).sub measurable_const)

/-- A past-measurable height times the centered square of a future Brownian
increment has mean zero. No integrability assumption on the height is required. -/
theorem integral_mul_sq_sub_sub_eq_zero (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) :
    (∫ ω, Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ∂P) = 0 := by
  rw [(indepFun_sq_sub_sub hB hst hY).integral_fun_mul_eq_mul_integral
    (hY.mono (ℱ.le s) le_rfl).aestronglyMeasurable
      hB.toIsPreBrownianReal.memLp_sq_sub_sub.aestronglyMeasurable,
    hB.toIsPreBrownianReal.integral_sq_sub_sub_eq_zero hst,
    mul_zero]

/-- A square-integrable past height times a centered squared Brownian increment is
square integrable. -/
theorem memLp_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) (hYi : MemLp Y 2 P) :
    MemLp (fun ω ↦ Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s))) 2 P := by
  exact (indepFun_sq_sub_sub hB hst hY).memLp_two_mul hYi
    hB.toIsPreBrownianReal.memLp_sq_sub_sub

/-- The second moment of a past-weighted centered squared increment factors exactly,
with no integrability assumption on the height. -/
theorem integral_sq_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hY : Measurable[ℱ s] Y) :
    (∫ ω, (Y ω * ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s))) ^ 2 ∂P) =
      2 * (∫ ω, Y ω ^ 2 ∂P) * ((t : ℝ) - s) ^ 2 := by
  simp_rw [mul_pow]
  have hind : IndepFun (fun ω ↦ Y ω ^ 2)
      (fun ω ↦ ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2) P :=
    (indepFun_sq_sub_sub hB hst hY).comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2)
  rw [hind.integral_fun_mul_eq_mul_integral
    ((hY.mono (ℱ.le s) le_rfl).pow_const 2).aestronglyMeasurable
    hB.toIsPreBrownianReal.memLp_sq_sub_sub.integrable_sq.aestronglyMeasurable,
    hB.toIsPreBrownianReal.integral_sq_sq_sub_sub hst]
  ring

/-- Exact mean-square identity for a finite centered quadratic sum with arbitrary
square-integrable predictable heights. The weighted summands need not be independent. -/
theorem integral_sq_sum_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) {H : ℕ → Ω → ℝ}
    (hH : ∀ i < n, Measurable[ℱ (t i)] (H i)) (hHi : ∀ i < n, MemLp (H i) 2 P) :
    (∫ ω, (∑ i ∈ range n, H i ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
      ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) =
        2 * ∑ i ∈ range n, (∫ ω, H i ω ^ 2 ∂P) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  have := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let Z i ω := H i ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
    ((t (i + 1) : ℝ) - t i))
  have hZi : ∀ i < n, MemLp (Z i) 2 P := fun i hi ↦
    hB.memLp_mul_sq_sub_sub (ht hi.le hi (Nat.le_succ i)) (hH i hi) (hHi i hi)
  have horth : ∀ i < n, ∀ j < n, i < j → (∫ ω, Z i ω * Z j ω ∂P) = 0 := by
    intro i hi j hj hij
    have hmeas : Measurable[ℱ (t j)] (fun ω ↦ Z i ω * H j ω) := by
      have h₀ := (hB.adapted (t i)).mono (ℱ.mono (ht hi.le hj.le hij.le)) le_rfl
      have h₁ := (hB.adapted (t (i + 1))).mono (ℱ.mono (ht hi hj.le hij)) le_rfl
      exact (((hH i hi).mono (ℱ.mono (ht hi.le hj.le hij.le)) le_rfl).mul
        (((h₁.sub h₀).pow_const 2).sub measurable_const)).mul (hH j hj)
    have h := hB.integral_mul_sq_sub_sub_eq_zero (ht hj.le hj (Nat.le_succ j)) hmeas
    convert h using 1
    congr 1
    ext ω
    dsimp [Z]
    ring
  suffices h : (∫ ω, (∑ i ∈ range n, Z i ω) ^ 2 ∂P) =
      ∑ i ∈ range n, ∫ ω, Z i ω ^ 2 ∂P by
    rw [h, mul_sum]
    exact sum_congr rfl fun i hi ↦ by
      rw [hB.integral_sq_mul_sq_sub_sub (ht (mem_range.1 hi).le (mem_range.1 hi)
        (Nat.le_succ i)) (hH i (mem_range.1 hi))]
      ring
  apply integral_sq_sum_of_pairwise_integral_mul_eq_zero (fun i hi ↦ hZi i (mem_range.1 hi))
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact horth i (mem_range.1 hi) j (mem_range.1 hj) hij
  · simpa only [mul_comm] using horth j (mem_range.1 hj) i (mem_range.1 hi) hji

/-- For heights equal to the Brownian left endpoint, the second moment of the centered
quadratic error is `2 ∑ᵢ tᵢ (tᵢ₊₁ - tᵢ)²`. -/
theorem integral_sq_sum_eval_mul_sq_sub_sub (hB : IsFilteredPreBrownianReal ℱ B P)
    {n : ℕ} {t : ℕ → ℝ≥0} (ht : MonotoneOn t (Set.Iic n)) :
    (∫ ω, (∑ i ∈ range n, B (t i) ω * ((B (t (i + 1)) ω - B (t i) ω) ^ 2 -
      ((t (i + 1) : ℝ) - t i))) ^ 2 ∂P) =
        2 * ∑ i ∈ range n, (t i : ℝ) * ((t (i + 1) : ℝ) - t i) ^ 2 := by
  rw [hB.integral_sq_sum_mul_sq_sub_sub ht (fun i _ ↦ hB.adapted (t i))
    (fun i _ ↦ hB.toIsPreBrownianReal.memLp_eval (t i) (by norm_num))]
  congr 1
  apply sum_congr rfl
  intro i _
  have h := (hB.toIsPreBrownianReal.hasLaw_eval (t i)).integral_comp
    (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  have hm : (∫ ω, B (t i) ω ^ 2 ∂P) = t i := by
    simpa [Function.comp_def, integral_sq_gaussianReal] using h
  rw [hm]

end TauCeti.Probability.IsFilteredPreBrownianReal
