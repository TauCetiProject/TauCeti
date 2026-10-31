/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Approximation
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.MeasureTheory.Measure.LevyConvergence
import TauCeti.Probability.Distributions.Affine

/-!
# Scalar stable probability measures

`stableMeasure α β s m` is the scalar stable law in Nolan's `S₀` convention, with shape `α`,
skewness `β`, nonnegative scale `s`, and location `m`. Valid shapes satisfy `0 < α ≤ 2` and
`|β| ≤ 1`. Invalid shapes give the zero measure, including at scale zero; valid shapes at
scale zero give the Dirac mass at the location.

For shapes below two, existence follows from the compensated compound-Poisson approximations
and `TauCeti.exists_probabilityMeasure_of_tendsto_charFun`. At shape two the law is Gaussian
with variance `2 * s ^ 2`. The characteristic function characterizes the resulting measures
without reference to the choice of weak limit. The dyadic approximations converge weakly to
the standardized law.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace TauCeti.Probability

private theorem exists_standardStableLaw {α β : ℝ} (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      charFun μ = fun t ↦ Complex.exp (stableCharacteristicExponent α β t) := by
  let μ (n : ℕ) : ProbabilityMeasure ℝ :=
    ⟨stableCompensatedPoissonMeasure α β ((2 : ℝ)⁻¹ ^ n),
      isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ (by positivity)⟩
  obtain ⟨ν, hν, -⟩ := exists_probabilityMeasure_of_tendsto_charFun (μ := μ)
    (Complex.continuous_exp.continuousAt.comp
      (continuousAt_stableCharacteristicExponent_zero hα.1 β))
    (tendsto_charFun_stableCompensatedPoissonMeasure_invTwoPow hα hβ)
  exact ⟨ν, hν.1⟩

private def standardStableLaw (α β : ℝ) (hα0 : 0 < α) (hα2 : α < 2) (hβ : |β| ≤ 1) :
    ProbabilityMeasure ℝ :=
  (exists_standardStableLaw ⟨hα0, hα2⟩ hβ).choose

private theorem charFun_standardStableLaw (α β : ℝ) (hα0 : 0 < α) (hα2 : α < 2)
    (hβ : |β| ≤ 1) (t : ℝ) :
    charFun (standardStableLaw α β hα0 hα2 hβ) t =
      Complex.exp (stableCharacteristicExponent α β t) :=
  congrFun (exists_standardStableLaw ⟨hα0, hα2⟩ hβ).choose_spec t

/-- The scalar stable law in Nolan's `S₀` parameterization.

It is zero unless `0 < α ≤ 2` and `|β| ≤ 1`. On that domain it is the affine image of the
standardized stable law for `α < 2`, and Gaussian with variance `2 * s ^ 2` for `α = 2`.
In particular, zero scale gives a Dirac law only for valid shapes. -/
def stableMeasure (α β : ℝ) (s : ℝ≥0) (m : ℝ) : Measure ℝ :=
  if h : α ∈ Ioc 0 2 ∧ |β| ≤ 1 then
    if htwo : α = 2 then gaussianReal m (2 * s ^ 2)
    else (standardStableLaw α β h.1.1 (lt_of_le_of_ne h.1.2 htwo) h.2 : Measure ℝ).map
      (fun x ↦ m + s * x)
  else 0

/-- Invalid shape or skewness parameters give the zero measure at every scale and location. -/
@[simp]
theorem stableMeasure_of_invalid {α β : ℝ} (h : α ≤ 0 ∨ 2 < α ∨ 1 < |β|)
    (s : ℝ≥0) (m : ℝ) : stableMeasure α β s m = 0 := by
  rw [stableMeasure, dite_eq_right (by
    rintro ⟨hα, hβ⟩
    rcases h with h | h | h <;> linarith [hα.1, hα.2])]

/-- Every stable law with valid shape and skewness is a probability measure, including at
zero scale and at both full-skewness boundaries. -/
theorem isProbabilityMeasure_stableMeasure {α β : ℝ} (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m : ℝ) : IsProbabilityMeasure (stableMeasure α β s m) := by
  rw [stableMeasure, dite_eq_left ⟨hα, hβ⟩]
  split_ifs <;> infer_instance

instance (α β : ℝ) (s : ℝ≥0) (m : ℝ) : IsFiniteMeasure (stableMeasure α β s m) := by
  by_cases h : α ∈ Ioc 0 2 ∧ |β| ≤ 1
  · let _ := isProbabilityMeasure_stableMeasure h.1 h.2 s m
    infer_instance
  · rw [stableMeasure_of_invalid (by
      simpa only [mem_Ioc, not_and_or, not_lt, not_le, or_assoc] using h)]
    infer_instance

/-- The stable law has the prescribed `S₀` characteristic function throughout the valid
parameter range, including shape one, shape two, and scale zero. -/
theorem charFun_stableMeasure {α β : ℝ} (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m t : ℝ) :
    charFun (stableMeasure α β s m) t =
      Complex.exp ((m * t : ℝ) * Complex.I + stableCharacteristicExponent α β (s * t)) := by
  rw [stableMeasure, dite_eq_left ⟨hα, hβ⟩]
  split_ifs with htwo
  · subst α
    rw [charFun_gaussianReal, stableCharacteristicExponent_two]
    congr 1
    push_cast
    ring
  · rw [charFun_map_affine, charFun_standardStableLaw, ← Complex.exp_add,
      Complex.ofReal_mul]

/-- At valid shapes, scale zero is the Dirac law at the location. -/
@[simp]
theorem stableMeasure_zero_scale {α β : ℝ} (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (m : ℝ) :
    stableMeasure α β 0 m = Measure.dirac m := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stableMeasure hα hβ, charFun_dirac]
  simp [mul_comm]

/-- Shape two is Gaussian with variance twice the squared stable scale. -/
@[simp]
theorem stableMeasure_two {β : ℝ} (hβ : |β| ≤ 1) (s : ℝ≥0) (m : ℝ) :
    stableMeasure 2 β s m = gaussianReal m (2 * s ^ 2) := by
  simp [stableMeasure, hβ]

/-- The dyadic compensated compound-Poisson approximations converge weakly to the
standardized stable law. -/
theorem tendsto_stableCompensatedPoissonMeasure_invTwoPow {α β : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ ↦
      (⟨stableCompensatedPoissonMeasure α β ((2 : ℝ)⁻¹ ^ n),
        isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ (by positivity)⟩ :
        ProbabilityMeasure ℝ)) atTop
      (𝓝 (⟨stableMeasure α β 1 0,
        isProbabilityMeasure_stableMeasure ⟨hα.1, hα.2.le⟩ hβ 1 0⟩ : ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simpa only [ProbabilityMeasure.coe_mk, charFun_stableMeasure ⟨hα.1, hα.2.le⟩ hβ,
    NNReal.coe_one, one_mul, zero_mul, Complex.ofReal_zero, zero_add] using
    tendsto_charFun_stableCompensatedPoissonMeasure_invTwoPow hα hβ t

end TauCeti.Probability
