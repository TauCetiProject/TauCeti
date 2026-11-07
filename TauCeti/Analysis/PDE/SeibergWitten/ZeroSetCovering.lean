/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.MeasureTheory.Covering.PackingNumber

/-!
# Covering numbers from monotonicity estimates at large parameter

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
measure `μ` is the defect energy `r |1 - |χ|²| / 4` of a solution, whose total mass is bounded
independently of `r`, and `A` is the zero set of the component `α` of its spinor. Taubes's
monotonicity estimate bounds the defect energy of a ball of radius `ρ` centred at a zero below by
`c ρ ²` for `c₀ r^(-1/2) ≤ ρ ≤ ρ₀`, with constants independent of `r`. By the maximal disjoint
half-ball argument (`TauCeti.coveringNumber_le_of_mul_pow_le_measure_closedBall`), the zero set is
then covered by `N(σ) ≤ C σ⁻²` balls of radius `σ` centred at zeros, as soon as `σ ≤ 2 ρ₀` and
`r ≥ (2 c₀ / σ) ²`.

## Main results

* `TauCeti.coveringNumber_le_of_mul_sq_le_measure_closedBall_of_sq_le`: the quadratic
  large-parameter covering bound, valid for `r ≥ (2 c₀ / σ) ²`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {X : Type*} [PseudoMetricSpace X]

namespace TauCeti

variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {A : Set X}

/-- **Covering bound in the large-parameter form.** Suppose that for some `r` the measure
satisfies `μ (closedBall x ρ) ≥ c ρ ^ 2` for every `x ∈ A` and every radius
`c₀ / √r ≤ ρ ≤ ρ₀`, with `c > 0`. Then for every `σ > 0` with `σ ≤ 2 ρ₀`, as soon as
`r ≥ (2 c₀ / σ) ^ 2`, the set `A` is covered by at most `4 μ (cthickening (σ / 2) A) / (c σ ^ 2)`
closed balls of radius `σ` centred in `A`. The bound does not depend on `r`. -/
theorem coveringNumber_le_of_mul_sq_le_measure_closedBall_of_sq_le {c c₀ ρ₀ r : ℝ} {σ : ℝ≥0}
    (hc : 0 < c)
    (hA : ∀ x ∈ A, ∀ ρ, c₀ / √r ≤ ρ → ρ ≤ ρ₀ → ENNReal.ofReal (c * ρ ^ 2) ≤ μ (closedBall x ρ))
    (hσ : σ ≠ 0) (hσρ₀ : σ ≤ 2 * ρ₀) (hrσ : (2 * c₀ / σ) ^ 2 ≤ r) :
    (coveringNumber σ A : ℝ≥0∞) ≤
      ENNReal.ofReal (4 / (c * σ ^ 2)) * μ (cthickening (σ / 2) A) := by
  have hσ₀ : (0 : ℝ) < σ := by positivity
  -- The threshold `r ≥ (2 c₀ / σ) ^ 2` says that the half-radius `σ / 2` is at least `c₀ / √r`.
  have hsqrt : 2 * c₀ / σ ≤ √r := Real.le_sqrt_of_sq_le hrσ
  have hlow : 2 * (c₀ / √r) ≤ σ := by
    rcases (Real.sqrt_nonneg r).eq_or_lt with hr | hr
    · simp [← hr]
    rw [div_le_iff₀ hσ₀] at hsqrt
    rw [← mul_div_assoc, div_le_iff₀ hr]
    linarith
  convert coveringNumber_le_of_mul_pow_le_measure_closedBall (d := 2) hc hA hσ hlow hσρ₀ using 4
  norm_num

end TauCeti
