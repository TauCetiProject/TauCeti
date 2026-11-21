/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import TauCeti.MeasureTheory.Function.PolynomialMemLp
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# The Laguerre measure

The generalized Laguerre polynomials `Lₙ^{(α)}` are orthogonal for the weight `x ^ α * exp (-x)` on
the half-line `(0, ∞)`. This file defines the corresponding measure `Polynomial.laguerreMeasure α`,
Lebesgue measure on `Set.Ioi 0` weighted by that density, and records the facts about it that the
Laguerre orthogonality relation and the Laguerre `L²` bases consume.

The weight is the Gamma density up to normalization, so every moment is a value of `Real.Gamma`:
`∫ x ^ s ∂(laguerreMeasure α) = Γ(s + α + 1)` whenever `-1 < s + α` (`Real.Gamma_eq_integral`).
At `s = 0` this is the total mass `Γ(α + 1)`, and the measure is finite exactly when `-1 < α`:
for `α ≤ -1` the density is not integrable at the origin. For `-1 < α` the Laguerre measure is
the Gamma law `ProbabilityTheory.gammaMeasure (α + 1) 1` scaled by its normalizing constant
`Γ(α + 1)`. The moment formulas hold for every `α`, including `α ≤ -1`, where the measure is
infinite but `x ^ s` is still integrable when `-1 < s + α`.

The measure has a finite exponential moment `∫ exp (a * |x|) < ∞` for every `a < 1`. This is the
hypothesis of the moment-determinacy argument behind
`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`, the density of polynomials in
`L²(laguerreMeasure α)`. Every polynomial is integrable against the measure as well.

## Main definitions

* `Polynomial.laguerreMeasure α`: the measure `x ^ α * exp (-x) dx` on `(0, ∞)`.

## Main statements

* `Polynomial.laguerreMeasure_eq_smul_gammaMeasure`: the comparison with the Gamma law.
* `Polynomial.integral_laguerreMeasure`: integration against the Laguerre measure as a weighted
  integral over `Set.Ioi 0`.
* `Polynomial.integral_rpow_laguerreMeasure`: the moments `∫ x ^ s = Γ(s + α + 1)`.
* `Polynomial.laguerreMeasure_univ`: the total mass is `Γ(α + 1)`.
* `Polynomial.isFiniteMeasure_laguerreMeasure_iff`: the measure is finite iff `-1 < α`.
* `Polynomial.integrable_exp_mul_abs_laguerreMeasure`: the finite exponential moments.
* `Polynomial.integrable_eval_laguerreMeasure`: polynomials are integrable.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, Table 18.3.1 (the Laguerre weight) and
  5.2.1 (Euler's integral for `Γ`).
* G. Szegő, *Orthogonal Polynomials*, Ch. V.
-/

public section

open MeasureTheory Real Set

namespace Polynomial

/-- The **Laguerre measure** with parameter `α`: Lebesgue measure on `(0, ∞)` weighted by
`x ^ α * exp (-x)`, the orthogonality measure of the generalized Laguerre polynomials. It is finite
exactly when `-1 < α` (`Polynomial.isFiniteMeasure_laguerreMeasure_iff`). -/
noncomputable def laguerreMeasure (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal (x ^ α * exp (-x))

/-- Unfolds `Polynomial.laguerreMeasure` to the weighted restricted Lebesgue measure, the shape in
which `TauCeti.hilbertBasisOfWeightedMeasure` takes its measure. -/
theorem laguerreMeasure_def (α : ℝ) :
    laguerreMeasure α =
      (volume.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal (x ^ α * exp (-x)) :=
  (rfl)

/-- The Laguerre weight `x ^ α * exp (-x)` is a.e. measurable for Lebesgue measure on `(0, ∞)`. -/
theorem aemeasurable_laguerreWeight (α : ℝ) :
    AEMeasurable (fun x : ℝ => x ^ α * exp (-x)) (volume.restrict (Ioi 0)) := by
  fun_prop

/-- The Laguerre weight `x ^ α * exp (-x)` is positive almost everywhere on `(0, ∞)`. -/
theorem ae_pos_laguerreWeight (α : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), 0 < x ^ α * exp (-x) :=
  ae_restrict_of_forall_mem measurableSet_Ioi fun _ hx => mul_pos (rpow_pos_of_pos hx α) (exp_pos _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ}

/-- Integration against the Laguerre measure is integration over `(0, ∞)` against the weight
`x ^ α * exp (-x)`. No integrability is needed: when the integrand is not integrable both sides
are `0`. -/
theorem integral_laguerreMeasure (f : ℝ → E) :
    ∫ x, f x ∂laguerreMeasure α = ∫ x in Ioi 0, (x ^ α * exp (-x)) • f x :=
  TauCeti.MeasureTheory.integral_withDensity_ofReal (aemeasurable_laguerreWeight α)
    ((ae_pos_laguerreWeight α).mono fun _ hx => hx.le) f

/-- A function is integrable against the Laguerre measure iff its product with the weight
`x ^ α * exp (-x)` is integrable on `(0, ∞)`. -/
theorem integrable_laguerreMeasure_iff {f : ℝ → E} :
    Integrable f (laguerreMeasure α) ↔
      IntegrableOn (fun x => (x ^ α * exp (-x)) • f x) (Ioi 0) :=
  TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff (aemeasurable_laguerreWeight α)
    ((ae_pos_laguerreWeight α).mono fun _ hx => hx.le)

/-! ### Moments -/

/-- The real power `x ^ s` is integrable against the Laguerre measure when `-1 < s + α`. -/
theorem integrable_rpow_laguerreMeasure {s : ℝ} (h : -1 < s + α) :
    Integrable (fun x : ℝ => x ^ s) (laguerreMeasure α) := by
  rw [integrable_laguerreMeasure_iff]
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow h one_pos one_pos).congr_fun
    (fun x hx => ?_) measurableSet_Ioi
  dsimp only
  rw [rpow_add (mem_Ioi.1 hx), rpow_one, neg_one_mul, smul_eq_mul]
  ring

/-- **The moments of the Laguerre measure** are values of the Gamma function: for `-1 < s + α`,
`∫ x ^ s ∂(laguerreMeasure α) = Γ(s + α + 1)`. -/
theorem integral_rpow_laguerreMeasure {s : ℝ} (h : -1 < s + α) :
    ∫ x, x ^ s ∂laguerreMeasure α = Gamma (s + α + 1) := by
  rw [integral_laguerreMeasure, Gamma_eq_integral (by linarith)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [smul_eq_mul, add_sub_cancel_right, rpow_add (mem_Ioi.1 hx)]
  ring

/-- The monomial `x ^ k` is integrable against the Laguerre measure when `-1 < k + α`. -/
theorem integrable_pow_laguerreMeasure {k : ℕ} (h : -1 < k + α) :
    Integrable (fun x : ℝ => x ^ k) (laguerreMeasure α) := by
  simpa only [rpow_natCast] using integrable_rpow_laguerreMeasure (s := k) h

/-- The integer moments of the Laguerre measure: `∫ x ^ k ∂(laguerreMeasure α) = Γ(k + α + 1)`
when `-1 < k + α`. -/
theorem integral_pow_laguerreMeasure {k : ℕ} (h : -1 < k + α) :
    ∫ x, x ^ k ∂laguerreMeasure α = Gamma (k + α + 1) := by
  simpa only [rpow_natCast] using integral_rpow_laguerreMeasure (s := k) h

/-- Every real polynomial is integrable against the Laguerre measure when `-1 < α`. -/
theorem integrable_eval_laguerreMeasure (hα : -1 < α) (q : ℝ[X]) :
    Integrable (fun x : ℝ => q.eval x) (laguerreMeasure α) :=
  TauCeti.integrable_eval_of_forall_integrable_pow
    (fun k => integrable_pow_laguerreMeasure (by linarith [k.cast_nonneg (α := ℝ)])) q

/-! ### Total mass and finiteness -/

/-- The total mass of the Laguerre measure, as a real number, is `Γ(α + 1)` when `-1 < α`. -/
theorem laguerreMeasure_real_univ (hα : -1 < α) :
    (laguerreMeasure α).real univ = Gamma (α + 1) := by
  simpa using integral_rpow_laguerreMeasure (s := 0) (by linarith)

/-- **The Laguerre measure is finite exactly when `-1 < α`.** For `α ≤ -1` the density
`x ^ α * exp (-x)` is not integrable at the origin. -/
theorem isFiniteMeasure_laguerreMeasure_iff : IsFiniteMeasure (laguerreMeasure α) ↔ -1 < α := by
  refine ⟨fun h => ?_, fun hα => ?_⟩
  · -- The weight is integrable on `(0, 1)`, where `exp x ≤ exp 1` bounds `x ^ α` by it.
    have hw : IntegrableOn (fun x : ℝ => x ^ α * exp (-x)) (Ioo 0 1) := by
      have h1 := integrable_laguerreMeasure_iff.1 <|
        integrable_const (μ := laguerreMeasure α) (1 : ℝ)
      simpa only [smul_eq_mul, mul_one] using h1.mono_set Ioo_subset_Ioi_self
    refine (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).1 <| (hw.const_mul (exp 1)).mono'
      (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_)
    rw [norm_of_nonneg (rpow_nonneg hx.1.le α)]
    calc x ^ α = exp x * (x ^ α * exp (-x)) := by
          rw [mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
      _ ≤ exp 1 * (x ^ α * exp (-x)) := by
          gcongr
          · exact mul_nonneg (rpow_nonneg hx.1.le α) (exp_pos _).le
          · exact hx.2.le
  · have h1 := integrable_rpow_laguerreMeasure (α := α) (s := 0) (by linarith)
    simp only [rpow_zero] at h1
    exact (integrable_const_iff.1 h1).resolve_left one_ne_zero

/-- The Laguerre measure is finite when `-1 < α`. -/
theorem isFiniteMeasure_laguerreMeasure (hα : -1 < α) : IsFiniteMeasure (laguerreMeasure α) :=
  isFiniteMeasure_laguerreMeasure_iff.2 hα

/-- **The total mass of the Laguerre measure** is `Γ(α + 1)` when `-1 < α`. -/
theorem laguerreMeasure_univ (hα : -1 < α) :
    laguerreMeasure α univ = ENNReal.ofReal (Gamma (α + 1)) := by
  have := isFiniteMeasure_laguerreMeasure hα
  rw [← laguerreMeasure_real_univ hα, ofReal_measureReal (measure_ne_top _ _)]

/-- For `-1 < α` the Laguerre measure is the Gamma law of shape `α + 1` and rate `1`, scaled by
its total mass `Γ(α + 1)`. -/
theorem laguerreMeasure_eq_smul_gammaMeasure (hα : -1 < α) :
    laguerreMeasure α =
      ENNReal.ofReal (Gamma (α + 1)) • ProbabilityTheory.gammaMeasure (α + 1) 1 := by
  have hΓ : 0 < Gamma (α + 1) := Gamma_pos_of_pos (by linarith)
  rw [TauCeti.Probability.gammaMeasure_eq_withDensity_restrict_Ioi, ← withDensity_smul' _ _
    ENNReal.ofReal_ne_top, laguerreMeasure_def]
  refine withDensity_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  rw [Pi.smul_apply, smul_eq_mul, ProbabilityTheory.gammaPDF, ← ENNReal.ofReal_mul hΓ.le,
    TauCeti.Probability.gammaPDFReal_of_nonneg (le_of_lt hx), one_rpow, one_mul,
    add_sub_cancel_right]
  field_simp

/-! ### Exponential moments -/

/-- **The finite exponential moments of the Laguerre measure.** For `-1 < α` and `a < 1`, the
function `exp (a * |x|)` is integrable against `laguerreMeasure α`: on `(0, ∞)` the weighted
integrand is `x ^ α * exp (-(1 - a) * x)`. Any `0 < a < 1` supplies the exponential-moment
hypothesis of `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`. -/
theorem integrable_exp_mul_abs_laguerreMeasure {a : ℝ} (hα : -1 < α) (ha : a < 1) :
    Integrable (fun x : ℝ => exp (a * |x|)) (laguerreMeasure α) := by
  rw [integrable_laguerreMeasure_iff]
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow hα one_pos (sub_pos.2 ha)).congr_fun
    (fun x hx => ?_) measurableSet_Ioi
  dsimp only
  rw [rpow_one, smul_eq_mul, abs_of_pos (mem_Ioi.1 hx), mul_assoc, ← exp_add]
  ring_nf

end Polynomial
