/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Cauchy.Basic
import TauCeti.Probability.Distributions.Affine

/-!
# Affine transport of Cauchy laws

The affine image `a + b * X` of a Cauchy variable of location `m` and nonnegative scale
`γ` is Cauchy with location `a + b * m` and scale `‖b‖₊ * γ`. This identity includes
negative slopes, constant maps, and the zero-scale Dirac laws. In particular, every member
of the family is an affine image of the standard Cauchy law, including its Dirac boundary.

The measure identity uses `TauCeti.Probability.charFun_cauchyMeasure` and uniqueness of
characteristic functions, so no moment assumptions are needed. A `HasLaw` corollary makes
the same parameter transformation available on arbitrary measurable source spaces.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

/-- An affine image of a Cauchy law has location `a + b * m` and scale `‖b‖₊ * γ`.
This holds at every slope, including zero, and at zero input scale. -/
@[simp]
theorem cauchyMeasure_map_affine (m : ℝ) (γ : ℝ≥0) (a b : ℝ) :
    (cauchyMeasure m γ).map (fun x ↦ a + b * x) =
      cauchyMeasure (a + b * m) (‖b‖₊ * γ) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_affine, charFun_cauchyMeasure, charFun_cauchyMeasure,
    ← Complex.exp_add]
  congr 1
  simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_mul]
  push_cast
  ring

/-- Affine transport of a Cauchy random variable, including constant maps and Dirac laws. -/
theorem hasLaw_affine_cauchyMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m a b : ℝ} {γ : ℝ≥0} (hX : HasLaw X (cauchyMeasure m γ) P) :
    HasLaw (fun ω ↦ a + b * X ω) (cauchyMeasure (a + b * m) (‖b‖₊ * γ)) P :=
  (HasLaw.mk (by fun_prop) (cauchyMeasure_map_affine m γ a b)).fun_comp hX

end TauCeti.Probability
