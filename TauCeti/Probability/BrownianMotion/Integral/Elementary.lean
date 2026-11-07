/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.Distributions.Gaussian.Moments
import Mathlib.Probability.Independence.Integration

/-!
# The isometry for elementary Brownian integrals

For a Brownian motion relative to a filtration, an elementary integral on a deterministic
nondecreasing grid is the sum `∑ i < n, ξ i * (W (τ (i+1)) - W (τ i))`, where the height
`ξ i` is measurable at the left endpoint `τ i`. This file proves that these sums are square
integrable and that their second moments equal
`∑ i < n, E[(ξ i)²] * (τ (i+1) - τ i)`.

The heights need only be square integrable, not bounded or mutually independent. Distinct
weighted increments are orthogonal because the later Brownian increment is centered and
independent of the information at its left endpoint. Empty sums and repeated grid times
are allowed. Only finite-dimensional Brownian laws and filtration-relative increment
independence are used; neither path continuity nor usual conditions are needed.

These are the elementary isometry and orthogonality identities used to extend the Brownian
integral by completion. No integral for general predictable processes is constructed here.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ξ η : Ω → ℝ}
  {s t u v : ℝ≥0}

/-- A square-integrable height known at the left endpoint times a Brownian increment
is square integrable. -/
theorem memLp_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P) (hst : s ≤ t)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    MemLp (fun ω => ξ ω * (W t ω - W s ω)) 2 P := by
  have hΔ : MemLp (W t - W s) 2 P :=
    (hW.hasLaw_sub_of_le hst).memLp (memLp_id_gaussianReal 2)
  have hind : IndepFun ξ (W t - W s) P :=
    indep_of_indep_of_le_left (hW.indep_sub hst).symm hξ.measurable.comap_le
  have hi := (hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    hξ₂.integrable_sq hΔ.integrable_sq
  apply (memLp_two_iff_integrable_sq (hξ₂.aestronglyMeasurable.mul
    hΔ.aestronglyMeasurable)).2
  simpa only [Pi.mul_def, Function.comp_apply, id_eq, mul_pow, Pi.sub_apply] using hi

/-- An integrable height known at the left endpoint times a Brownian increment has mean zero. -/
theorem integral_mul_sub_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P) (hst : s ≤ t)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₁ : Integrable ξ P) :
    ∫ ω, ξ ω * (W t ω - W s ω) ∂P = 0 := by
  have hind : IndepFun ξ (W t - W s) P :=
    indep_of_indep_of_le_left (hW.indep_sub hst).symm hξ.measurable.comap_le
  have h := hind.integral_fun_mul_eq_mul_integral hξ₁.aestronglyMeasurable
    (hW.adapted.measurable.sub hW.adapted.measurable).aestronglyMeasurable
  have hmean : ∫ ω, W t ω - W s ω ∂P = 0 := by
    simpa only [Pi.sub_apply] using
      (hW.hasLaw_sub_of_le hst).integral_eq.trans integral_id_gaussianReal
  simpa only [Pi.sub_apply, hmean, mul_zero] using h

/-- The one-interval Brownian isometry for a square-integrable left-endpoint height. -/
theorem integral_sq_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P) (hst : s ≤ t)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    ∫ ω, (ξ ω * (W t ω - W s ω)) ^ 2 ∂P =
      (∫ ω, ξ ω ^ 2 ∂P) * ((t : ℝ) - s) := by
  have hind : IndepFun ξ (W t - W s) P :=
    indep_of_indep_of_le_left (hW.indep_sub hst).symm hξ.measurable.comap_le
  have hΔ : ∫ ω, (W t ω - W s ω) ^ 2 ∂P = ((t : ℝ) - s) := by
    have h := (hW.hasLaw_sub_of_le hst).integral_comp
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
    simpa [Function.comp_def, integral_sq_gaussianReal, NNReal.coe_sub hst] using h
  simp_rw [mul_pow]
  have h := (hind.comp (measurable_id.pow_const 2)
    (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
      hξ₂.integrable_sq.aestronglyMeasurable
      ((hW.adapted.measurable.sub hW.adapted.measurable).pow_const 2).aestronglyMeasurable
  simpa only [Function.comp_apply, id_eq, Pi.sub_apply, hΔ] using h

/-- Weighted Brownian increments on ordered disjoint intervals are orthogonal in `L²`.
The heights may depend on all the information available at their respective left endpoints. -/
theorem integral_mul_sub_mul_mul_sub_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (huv : u ≤ v) (hvs : v ≤ s) (hst : s ≤ t)
    (hξ : StronglyMeasurable[ℱ u] ξ) (hξ₂ : MemLp ξ 2 P)
    (hη : StronglyMeasurable[ℱ s] η) (hη₂ : MemLp η 2 P) :
    ∫ ω, (ξ ω * (W v ω - W u ω)) * (η ω * (W t ω - W s ω)) ∂P = 0 := by
  have hknown : StronglyMeasurable[ℱ s] (fun ω => (ξ ω * (W v ω - W u ω)) * η ω) :=
    (((hξ.mono (ℱ.mono (huv.trans hvs))).mul
      ((hW.adapted.stronglyAdapted.stronglyMeasurable_le hvs).sub
        (hW.adapted.stronglyAdapted.stronglyMeasurable_le (huv.trans hvs)))).mul hη)
  have hi := (hW.memLp_mul_sub huv hξ hξ₂).integrable_mul hη₂
  simpa only [mul_assoc] using hW.integral_mul_sub_eq_zero hst hknown hi

variable {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- An elementary Brownian integral with square-integrable predictable heights lies in `L²`.
Grid monotonicity is required only through its last endpoint. -/
theorem memLp_sum_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    MemLp (fun ω => ∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω)) 2 P := by
  exact memLp_finsetSum _ fun i hi =>
    hW.memLp_mul_sub (hτ (mem_range.mp hi).le (mem_range.mp hi) i.le_succ)
      (ha i (mem_range.mp hi)) (ha₂ i (mem_range.mp hi))

/-- **The elementary Brownian isometry.** The second moment of a finite predictable
increment sum is the sum of the expected squared heights times the interval lengths.
No independence between the heights and no strictness of the grid is assumed. -/
theorem integral_sq_sum_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    ∫ ω, (∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω)) ^ 2 ∂P =
      ∑ i ∈ range n, (∫ ω, a i ω ^ 2 ∂P) * ((τ (i + 1) : ℝ) - τ i) := by
  let Z (i : ℕ) (ω : Ω) := a i ω * (W (τ (i + 1)) ω - W (τ i) ω)
  have hZ (i : ℕ) (hi : i < n) : MemLp (Z i) 2 P :=
    hW.memLp_mul_sub (hτ hi.le hi i.le_succ) (ha i hi) (ha₂ i hi)
  have hoff (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i < j) :
      ∫ ω, Z i ω * Z j ω ∂P = 0 :=
    hW.integral_mul_sub_mul_mul_sub_eq_zero (hτ hi.le hi i.le_succ)
      (hτ hi hj.le hij) (hτ hj.le hj j.le_succ) (ha i hi) (ha₂ i hi) (ha j hj) (ha₂ j hj)
  have hpair (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
      ∫ ω, Z i ω * Z j ω ∂P = 0 := by
    rcases hij.lt_or_gt with hij | hij
    · exact hoff i j hi hj hij
    · simpa only [mul_comm] using hoff j i hj hi hij
  have hexpand (ω : Ω) :
      (∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω)) ^ 2 =
        ∑ i ∈ range n, ∑ j ∈ range n, Z i ω * Z j ω := by
    rw [sq, sum_mul]
    exact sum_congr rfl fun i _ => mul_sum _ _ _
  simp_rw [hexpand]
  have hint (i j : ℕ) (hi : i < n) (hj : j < n) :
      Integrable (fun ω => Z i ω * Z j ω) P := by
    simpa only [Pi.mul_def] using (hZ i hi).integrable_mul (hZ j hj)
  rw [integral_finsetSum _ fun i hi =>
    integrable_finsetSum _ fun j hj => hint i j (mem_range.mp hi) (mem_range.mp hj)]
  refine sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun j hj => hint i j (mem_range.mp hi) (mem_range.mp hj),
    sum_eq_single_of_mem i hi]
  · simpa only [Z, ← sq] using
      hW.integral_sq_mul_sub (hτ (mem_range.mp hi).le (mem_range.mp hi) i.le_succ)
        (ha i (mem_range.mp hi)) (ha₂ i (mem_range.mp hi))
  · intro j hj hji
    exact hpair i j (mem_range.mp hi) (mem_range.mp hj) hji.symm

end TauCeti.Probability.IsFilteredPreBrownianReal
