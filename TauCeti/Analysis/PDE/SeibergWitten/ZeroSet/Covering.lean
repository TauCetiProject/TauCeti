/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Covering.PackingNumber
import TauCeti.Analysis.Calculus.PowerGrowth

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

The quadratic lower bound itself comes from integrating Taubes's differential inequality
`E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) E'(σ) + K σ⁴` for the radial function
`E(σ) = μ (closedBall x σ)`, starting from a lower bound `E(c₀ r^(-1/2)) ≥ c₁ / r` at the
smallest scale (`TauCeti.mul_sq_le_of_le_mul_deriv_add`). Composing the two gives the covering
bound with constants that depend only on the constants of the differential inequality.

## Main results

* `TauCeti.coveringNumber_le_of_mul_sq_le_measure_closedBall_of_sq_le`: the quadratic
  large-parameter covering bound, valid for `r ≥ (2 c₀ / σ) ²`.
* `TauCeti.exists_forall_coveringNumber_le_of_ae_le`: the same bound with the quadratic lower
  bound supplied by Taubes's differential inequality and the smallest-scale lower bound at each
  point of `A`.

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

/-- **Covering the zero set from the monotonicity inequality.** Fix `C, C₁, K ≥ 0` and
`c₀, c₁, σ₀ > 0`. There are constants `c > 0` and `ρ₀ > 0` with the following property. Let
`r ≥ 1`, let `μ` be a measure and `A` a set, and suppose that for every `x ∈ A` the ball
`closedBall x σ₀` has finite measure, the function `E(σ) = μ (closedBall x σ)` satisfies Taubes's
differential inequality `E(σ) ≤ (σ / 2) (1 + C σ) (1 + C₁ r^(-1/2)) E'(σ) + K σ⁴` at almost every
`σ ∈ (c₀ r^(-1/2), σ₀)`, and `E(c₀ r^(-1/2)) ≥ c₁ / r`. Then for every `σ > 0` with `σ ≤ 2 ρ₀`,
as soon as `r ≥ (2 c₀ / σ) ^ 2`, the set `A` is covered by at most
`4 μ (cthickening (σ / 2) A) / (c σ ^ 2)` closed balls of radius `σ` centred in `A`. The
constants `c` and `ρ₀` depend neither on `r` nor on `μ` and `A`. -/
theorem exists_forall_coveringNumber_le_of_ae_le {C C₁ K c₀ c₁ σ₀ : ℝ} (hC : 0 ≤ C)
    (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hσ₀ : 0 < σ₀) :
    ∃ c > 0, ∃ ρ₀ > 0, ∀ r, 1 ≤ r → ∀ (μ : Measure X) (A : Set X),
      (∀ x ∈ A, μ (closedBall x σ₀) ≠ ∞ ∧
        (∀ᵐ σ, σ ∈ Ioo (c₀ / √r) σ₀ →
          (μ (closedBall x σ)).toReal ≤ σ / 2 * (1 + C * σ) * (1 + C₁ / √r) *
            deriv (fun σ ↦ (μ (closedBall x σ)).toReal) σ + K * σ ^ 4) ∧
        c₁ / r ≤ (μ (closedBall x (c₀ / √r))).toReal) →
      ∀ σ : ℝ≥0, σ ≠ 0 → (σ : ℝ) ≤ 2 * ρ₀ → (2 * c₀ / σ) ^ 2 ≤ r →
        (coveringNumber σ A : ℝ≥0∞) ≤
          ENNReal.ofReal (4 / (c * σ ^ 2)) * μ (cthickening (σ / 2) A) := by
  set m := c₁ / (c₀ ^ 2 * (1 + C) ^ 2 * Real.exp (2 * C₁ * (1 + |Real.log c₀|)))
  have hm : 0 < m := by positivity
  -- Below the radius `ρ₀` the error term `K ρ ^ 4` is absorbed into `m ρ ^ 2 / 2`.
  set ρ₀ := min σ₀ (min 1 √(m / (2 * (K + 1))))
  have hρ₀ : 0 < ρ₀ := lt_min hσ₀ (lt_min one_pos (by positivity))
  refine ⟨m / 2, by positivity, ρ₀, hρ₀, fun r hr μ A hA σ hσ hσρ₀ hrσ ↦ ?_⟩
  refine coveringNumber_le_of_mul_sq_le_measure_closedBall_of_sq_le (by positivity)
    (fun x hx ρ hρ hρρ₀ ↦ ?_) hσ hσρ₀ hrσ
  obtain ⟨hfin, hle, hbase⟩ := hA x hx
  -- Apply the real-variable lower bound with `h = r^(-1/2)`.
  have hs : 0 < √r := Real.sqrt_pos.2 (by linarith)
  set h := (√r)⁻¹
  have hch : c₀ / √r = c₀ * h := div_eq_mul_inv _ _
  have hρσ₀ : ρ ≤ σ₀ := hρρ₀.trans (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := hρρ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hKρ : 2 * K * ρ ^ 2 ≤ m := by
    have hsq : ρ ^ 2 ≤ m / (2 * (K + 1)) := by
      calc ρ ^ 2 ≤ √(m / (2 * (K + 1))) ^ 2 := by
            gcongr
            · exact (by positivity : 0 ≤ c₀ / √r).trans hρ
            · exact hρρ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
        _ = m / (2 * (K + 1)) := Real.sq_sqrt (by positivity)
    rw [le_div_iff₀ (by positivity)] at hsq
    nlinarith [sq_nonneg ρ]
  have hmono : MonotoneOn (fun σ ↦ (μ (closedBall x σ)).toReal) (Icc (c₀ * h) ρ) :=
    fun s _ t ht hst ↦ ENNReal.toReal_mono
      (ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall (ht.2.trans hρσ₀))))
      (measure_mono (closedBall_subset_closedBall hst))
  have hfm : c₁ * h ^ 2 ≤ (μ (closedBall x (c₀ * h))).toReal := by
    rwa [← hch, inv_pow, Real.sq_sqrt (by linarith), ← div_eq_mul_inv]
  have hf' : ∀ᵐ τ, τ ∈ Ioo (c₀ * h) ρ →
      (μ (closedBall x τ)).toReal ≤ τ / 2 * (1 + C * τ) * (1 + C₁ / √r) *
        deriv (fun σ ↦ (μ (closedBall x σ)).toReal) τ + K * τ ^ 4 := by
    filter_upwards [hle] with τ hτ hτI
    exact hτ ⟨hch ▸ hτI.1, hτI.2.trans_le hρσ₀⟩
  exact ENNReal.ofReal_le_of_le_toReal <| mul_sq_le_of_le_mul_deriv_add hC (by positivity) hK
    hc₀ (inv_pos.2 hs) (inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hr)) (div_eq_mul_inv _ _).le
    (hch ▸ hρ) hρ1 hmono hc₁.le hfm hf' hKρ

end TauCeti
