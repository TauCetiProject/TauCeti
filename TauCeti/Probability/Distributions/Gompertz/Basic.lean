/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The Gompertz distribution

For positive parameters `η` and `b`, the Gompertz law is the law of
`log (1 + E / η) / b`, where `E` is a rate-one exponential variable. Its survival function
is `exp (-η * (exp (b * x) - 1))` for `x ≥ 0`. Nonpositive parameters give zero measure.

This file constructs the law, proves probability and joint parameter measurability, and gives
the exponential-variable construction and positive-scaling identity.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {η b c : ℝ}

/-- The Gompertz law with positive shape `η` and rate `b`, constructed from a rate-one
exponential variable. Invalid parameters give zero measure. -/
def gompertzMeasure (η b : ℝ) : Measure ℝ :=
  if 0 < η ∧ 0 < b then (expMeasure 1).map (fun e => Real.log (1 + e / η) / b) else 0

/-- At positive parameters the Gompertz law is its defining exponential pushforward. -/
theorem gompertzMeasure_of_pos (hη : 0 < η) (hb : 0 < b) :
    gompertzMeasure η b = (expMeasure 1).map (fun e => Real.log (1 + e / η) / b) := by
  rw [gompertzMeasure, ite_eq_left ⟨hη, hb⟩]

/-- Invalid Gompertz parameters give zero measure. -/
@[simp]
theorem gompertzMeasure_of_not_pos (h : ¬ (0 < η ∧ 0 < b)) : gompertzMeasure η b = 0 := by
  rw [gompertzMeasure, ite_eq_right h]

/-- A Gompertz law with positive parameters is a probability measure. -/
theorem isProbabilityMeasure_gompertzMeasure (hη : 0 < η) (hb : 0 < b) :
    IsProbabilityMeasure (gompertzMeasure η b) := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  rw [gompertzMeasure_of_pos hη hb]
  infer_instance

/-- The Gompertz law is a probability measure exactly at positive parameters. -/
@[simp]
theorem isProbabilityMeasure_gompertzMeasure_iff :
    IsProbabilityMeasure (gompertzMeasure η b) ↔ 0 < η ∧ 0 < b := by
  refine ⟨fun h => ?_, fun h => isProbabilityMeasure_gompertzMeasure h.1 h.2⟩
  by_contra hab
  rw [gompertzMeasure_of_not_pos hab] at h
  exact not_isProbabilityMeasure_zero h

/-- Transforming a rate-one exponential variable gives the Gompertz law. -/
theorem hasLaw_gompertzMeasure_of_hasLaw_expMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {E : Ω → ℝ} (hη : 0 < η) (hb : 0 < b)
    (hE : HasLaw E (expMeasure 1) P) :
    HasLaw (fun ω => Real.log (1 + E ω / η) / b) (gompertzMeasure η b) P := by
  rw [gompertzMeasure_of_pos hη hb]
  exact (hasLaw_map (by fun_prop : Measurable (fun e : ℝ =>
    Real.log (1 + e / η) / b)).aemeasurable).comp hE

/-- The defining Gompertz transform sends positive inputs to positive outputs. -/
theorem log_one_add_div_div_pos (hη : 0 < η) (hb : 0 < b) {e : ℝ} (he : 0 < e) :
    0 < Real.log (1 + e / η) / b :=
  div_pos (Real.log_pos (by linarith [div_pos he hη])) hb

/-- Gompertz variables are almost surely positive, including on the invalid zero branch. -/
theorem ae_pos_gompertzMeasure (η b : ℝ) : ∀ᵐ x ∂gompertzMeasure η b, 0 < x := by
  by_cases h : 0 < η ∧ 0 < b
  · rw [gompertzMeasure_of_pos h.1 h.2]
    apply (ae_map_iff (by fun_prop) measurableSet_Ioi).2
    filter_upwards [ae_pos_expMeasure 1] with e he
    exact log_one_add_div_div_pos h.1 h.2 he
  · simp [gompertzMeasure_of_not_pos h]

/-- The Gompertz law gives no mass to the nonpositive half-line, at all parameters. -/
@[simp]
theorem gompertzMeasure_Iic_zero (η b : ℝ) : gompertzMeasure η b (Iic 0) = 0 :=
  measure_mono_null (fun _ hy => not_lt.mpr (mem_Iic.mp hy))
    (ae_iff.mp (ae_pos_gompertzMeasure η b))

/-- The totalized Gompertz family is jointly measurable in both parameters. -/
@[fun_prop]
theorem measurable_gompertzMeasure :
    Measurable fun p : ℝ × ℝ => gompertzMeasure p.1 p.2 := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  unfold gompertzMeasure
  apply Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd))
  · exact TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry
      (ν := expMeasure 1) (by fun_prop)
  · exact measurable_const

/-- Multiplication by a positive constant divides the Gompertz rate by that constant.
The identity includes invalid parameters. -/
theorem map_mul_gompertzMeasure (hc : 0 < c) (η b : ℝ) :
    (gompertzMeasure η b).map (c * ·) = gompertzMeasure η (b / c) := by
  by_cases h : 0 < η ∧ 0 < b
  · rw [gompertzMeasure_of_pos h.1 h.2,
      gompertzMeasure_of_pos h.1 (div_pos h.2 hc),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext e
    simp only [Function.comp_apply]
    field_simp
  · rw [gompertzMeasure_of_not_pos h,
      gompertzMeasure_of_not_pos (by simpa [div_pos_iff_of_pos_right hc] using h),
      Measure.map_zero]

/-- The random-variable form of positive scaling of the Gompertz rate. -/
theorem hasLaw_mul_gompertzMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hc : 0 < c) (hX : HasLaw X (gompertzMeasure η b) P) :
    HasLaw (fun ω => c * X ω) (gompertzMeasure η (b / c)) P := by
  rw [← map_mul_gompertzMeasure hc]
  exact (hasLaw_map (by fun_prop : Measurable (c * · : ℝ → ℝ)).aemeasurable).comp hX

end TauCeti.Probability
