/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
import TauCeti.Probability.Distributions.Affine

/-!
# Affine transport of scalar stable laws

Scalar stable laws are closed under every real affine map. In Nolan's `S₀` convention,
`x ↦ a + b * x` changes the skewness by the sign of `b`, multiplies the scale by `|b|`, and
changes the location to `a + b * m`. The zero-slope case is included and gives a Dirac mass.

The proof uses characteristic-function uniqueness. Its key input is the equivariance of the
stable characteristic exponent under simultaneous reflection of its skewness and argument.
Invalid shape parameters remain the zero measure under every affine pushforward.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- Scaling the argument of the stable characteristic exponent by `b` is equivalent to
scaling its magnitude by `|b|` and multiplying the skewness by the sign of `b`. -/
theorem stableCharacteristicExponent_sign_mul_abs (α β b u : ℝ) :
    stableCharacteristicExponent α (Real.sign b * β) (|b| * u) =
      stableCharacteristicExponent α β (b * u) := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [Real.sign_of_neg hb, abs_of_neg hb, neg_one_mul,
      stableCharacteristicExponent_neg_skew]
    congr 2
    ring
  · simp
  · simp [Real.sign_of_pos hb, abs_of_pos hb]

/-- **Affine transport of scalar stable laws.** For valid shape parameters, the image under
`x ↦ a + b * x` has skewness `sign b * β`, scale `|b| * s`, and location `a + b * m`.
This includes `b = 0`, when both sides are the Dirac mass at `a`. -/
@[simp]
theorem stableMeasure_map_affine {α β : ℝ} (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m a b : ℝ) :
    (stableMeasure α β s m).map (fun x ↦ a + b * x) =
      stableMeasure α (Real.sign b * β) (‖b‖₊ * s) (a + b * m) := by
  have hβ' : |Real.sign b * β| ≤ 1 := by
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · simpa [Real.sign_of_neg hb] using hβ
    · simp
    · simpa [Real.sign_of_pos hb] using hβ
  let _ := isProbabilityMeasure_stableMeasure hα hβ s m
  let _ := isProbabilityMeasure_stableMeasure hα hβ' (‖b‖₊ * s) (a + b * m)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_affine, charFun_stableMeasure hα hβ,
    charFun_stableMeasure hα hβ', ← Complex.exp_add]
  have hexponent :
      stableCharacteristicExponent α (Real.sign b * β) ((↑(‖b‖₊ * s) : ℝ) * t) =
        stableCharacteristicExponent α β ((s : ℝ) * (b * t)) := by
    rw [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
    rw [show |b| * (s : ℝ) * t = |b| * ((s : ℝ) * t) by ring,
      stableCharacteristicExponent_sign_mul_abs]
    apply congrArg (stableCharacteristicExponent α β)
    ring
  rw [hexponent]
  congr 1
  push_cast
  ring

/-- A constant affine image of a valid stable law is the Dirac mass at the constant. -/
@[simp]
theorem stableMeasure_map_const {α β : ℝ} (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m a : ℝ) :
    (stableMeasure α β s m).map (fun _ ↦ a) = Measure.dirac a := by
  rw [show (fun _ : ℝ ↦ a) = fun x ↦ a + 0 * x by funext x; ring,
    stableMeasure_map_affine hα hβ]
  simpa using stableMeasure_zero_scale hα (β := 0) (by simp) a

/-- Reflecting a stable law negates its skewness and location while preserving its scale. -/
@[simp]
theorem stableMeasure_map_neg {α β : ℝ} (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (s : ℝ≥0) (m : ℝ) :
    (stableMeasure α β s m).map (-·) = stableMeasure α (-β) s (-m) := by
  rw [show (-·) = fun x : ℝ ↦ 0 + (-1) * x by funext x; ring,
    stableMeasure_map_affine hα hβ]
  norm_num [Real.sign_of_neg]

/-- An affine pushforward of an invalid stable family is still the zero measure. -/
theorem stableMeasure_map_affine_of_invalid {α β : ℝ}
    (h : α ≤ 0 ∨ 2 < α ∨ 1 < |β|) (s : ℝ≥0) (m a b : ℝ) :
    (stableMeasure α β s m).map (fun x ↦ a + b * x) = 0 := by
  rw [stableMeasure_of_invalid h, Measure.map_zero]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- Affine transport of a random variable with a valid scalar stable law. -/
theorem HasLaw.affine_stableMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {α β : ℝ} {s : ℝ≥0} {m a b : ℝ}
    (hX : HasLaw X (stableMeasure α β s m) P) (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) :
    HasLaw (fun ω ↦ a + b * X ω)
      (stableMeasure α (Real.sign b * β) (‖b‖₊ * s) (a + b * m)) P :=
  (HasLaw.mk (by fun_prop) (stableMeasure_map_affine hα hβ s m a b)).fun_comp hX

/-- Reflection of a random variable with a valid scalar stable law. -/
theorem HasLaw.neg_stableMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {α β : ℝ} {s : ℝ≥0} {m : ℝ}
    (hX : HasLaw X (stableMeasure α β s m) P) (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) :
    HasLaw (fun ω ↦ -X ω) (stableMeasure α (-β) s (-m)) P :=
  (HasLaw.mk (by fun_prop) (stableMeasure_map_neg hα hβ s m)).fun_comp hX

end ProbabilityTheory
