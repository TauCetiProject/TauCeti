/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# Generalized gamma laws

The generalized gamma law with shape `a`, nonzero power parameter `c`, and scale `s` is
obtained from a unit-rate Gamma variable `G` by `s * G ^ c⁻¹`. Negative power parameters
are allowed; in particular, they give laws with only finitely many natural moments.
Invalid parameters give the zero measure.

This file supplies the construction, probability and positivity results, positive scaling,
and recovery of the Gamma variable by taking a power.
Real-power moments are developed in `GeneralizedGamma.Moments`.

The construction reuses Mathlib's `ProbabilityTheory.gammaMeasure` and its moment theory
in `TauCeti.Probability.Distributions.Gamma.Basic`.

## References

* E. W. Stacy, *A Generalization of the Gamma Distribution*, Annals of Mathematical
  Statistics 33 (1962), 1187–1192. We also allow negative power parameters.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {a c s b : ℝ}

/-- The law of `s * G ^ c⁻¹` for a unit-rate Gamma variable of shape `a`.
It is zero unless `a > 0`, `c ≠ 0`, and `s > 0`. -/
def generalizedGammaMeasure (a c s : ℝ) : Measure ℝ :=
  if 0 < a ∧ c ≠ 0 ∧ 0 < s then
    (gammaMeasure a 1).map (fun x ↦ s * x ^ c⁻¹)
  else 0

/-- The defining power pushforward at valid parameters. -/
theorem generalizedGammaMeasure_of_valid (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    generalizedGammaMeasure a c s = (gammaMeasure a 1).map (fun x ↦ s * x ^ c⁻¹) := by
  simp [generalizedGammaMeasure, ha, hc, hs]

/-- Invalid parameters give the zero measure. -/
@[simp]
theorem generalizedGammaMeasure_of_not_valid (h : ¬ (0 < a ∧ c ≠ 0 ∧ 0 < s)) :
    generalizedGammaMeasure a c s = 0 := by
  simp [generalizedGammaMeasure, h]

/-- Positive shape and scale and a nonzero power parameter give a probability law. -/
theorem isProbabilityMeasure_generalizedGammaMeasure
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    IsProbabilityMeasure (generalizedGammaMeasure a c s) := by
  rw [generalizedGammaMeasure_of_valid ha hc hs]
  let _ := isProbabilityMeasure_gammaMeasure ha zero_lt_one
  infer_instance

/-- Every totalized generalized gamma law is finite. -/
instance (a c s : ℝ) : IsFiniteMeasure (generalizedGammaMeasure a c s) := by
  by_cases h : 0 < a ∧ c ≠ 0 ∧ 0 < s
  · let _ := isProbabilityMeasure_generalizedGammaMeasure h.1 h.2.1 h.2.2
    infer_instance
  · rw [generalizedGammaMeasure_of_not_valid h]
    infer_instance

/-- The valid parameter range is exactly the probability range. -/
@[simp]
theorem isProbabilityMeasure_generalizedGammaMeasure_iff :
    IsProbabilityMeasure (generalizedGammaMeasure a c s) ↔ 0 < a ∧ c ≠ 0 ∧ 0 < s := by
  refine ⟨fun h ↦ ?_, fun h ↦ isProbabilityMeasure_generalizedGammaMeasure h.1 h.2.1 h.2.2⟩
  by_contra hn
  have := h.ne_zero
  exact this (generalizedGammaMeasure_of_not_valid hn)

/-- Generalized gamma laws are almost surely positive, including invalid zero laws. -/
theorem ae_pos_generalizedGammaMeasure (a c s : ℝ) :
    ∀ᵐ x ∂generalizedGammaMeasure a c s, 0 < x := by
  by_cases h : 0 < a ∧ c ≠ 0 ∧ 0 < s
  swap
  · simp [generalizedGammaMeasure_of_not_valid h]
  rw [generalizedGammaMeasure_of_valid h.1 h.2.1 h.2.2]
  apply (ae_map_iff (by fun_prop) measurableSet_Ioi).2
  filter_upwards [ae_pos_gammaMeasure a 1] with x hx
  exact mul_pos h.2.2 (rpow_pos_of_pos hx _)

/-- Taking the standardized `c`th power recovers the unit-rate Gamma law. -/
@[simp]
theorem generalizedGammaMeasure_map_rpow
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    (generalizedGammaMeasure a c s).map (fun x ↦ (x / s) ^ c) = gammaMeasure a 1 := by
  rw [generalizedGammaMeasure_of_valid ha hc hs,
    Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    _ = (gammaMeasure a 1).map id := by
      apply Measure.map_congr
      filter_upwards [ae_pos_gammaMeasure a 1] with x hx
      simp [mul_div_cancel_left₀ _ hs.ne', rpow_inv_rpow hx.le hc]
    _ = _ := Measure.map_id

/-- Positive scaling multiplies the scale, including at invalid parameters. -/
@[simp]
theorem generalizedGammaMeasure_map_const_mul (hb : 0 < b) :
    (generalizedGammaMeasure a c s).map (fun x ↦ b * x) =
      generalizedGammaMeasure a c (b * s) := by
  by_cases h : 0 < a ∧ c ≠ 0 ∧ 0 < s
  · rw [generalizedGammaMeasure_of_valid h.1 h.2.1 h.2.2,
      generalizedGammaMeasure_of_valid h.1 h.2.1 (mul_pos hb h.2.2),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    exact (mul_assoc _ _ _).symm
  · have h' : ¬ (0 < a ∧ c ≠ 0 ∧ 0 < b * s) := by
      simpa only [mul_pos_iff_of_pos_left hb] using h
    simp [generalizedGammaMeasure_of_not_valid h, generalizedGammaMeasure_of_not_valid h']

/-- Power parameter one recovers the Gamma law with reciprocal-scale rate. -/
@[simp]
theorem generalizedGammaMeasure_one (ha : 0 < a) (hs : 0 < s) :
    generalizedGammaMeasure a 1 s = gammaMeasure a s⁻¹ := by
  rw [generalizedGammaMeasure_of_valid ha one_ne_zero hs]
  simpa using gammaMeasure_map_const_mul ha zero_lt_one hs

/-- A power transform of a unit-rate Gamma variable has the generalized gamma law. -/
theorem hasLaw_generalizedGammaMeasure_of_hasLaw_gammaMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (hX : HasLaw X (gammaMeasure a 1) P) :
    HasLaw (fun ω ↦ s * X ω ^ c⁻¹) (generalizedGammaMeasure a c s) P := by
  rw [generalizedGammaMeasure_of_valid ha hc hs]
  exact (hasLaw_map (X := fun x : ℝ ↦ s * x ^ c⁻¹) (by fun_prop)).fun_comp hX

end TauCeti.Probability
