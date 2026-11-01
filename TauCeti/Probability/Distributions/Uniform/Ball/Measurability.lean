/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Ball.Basic
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Parameter measurability of uniform ball laws

The uniform ball law is jointly Giry measurable in its center and real radius, including the
Dirac law at radius zero and the zero measure at negative radii. Thus measurable centers and
nonnegative radii can parameterize probability kernels through the existing kernel constructors.

For nonnegative radii, `uniformBallMeasure_eq_map_unitBall` represents the family by the affine
maps `x ↦ c + r • x` of one fixed unit-ball law. Joint measurability then follows from
`TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry`.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Uniform ball laws are jointly measurable in the center and radius, including the
zero-radius Dirac law and the negative-radius zero law. -/
@[fun_prop]
theorem measurable_uniformBallMeasure :
    Measurable (fun p : E × ℝ ↦ uniformBallMeasure p.1 p.2) := by
  classical
  have hpiece : Measurable (fun p : E × ℝ ↦ if 0 ≤ p.2 then
      (uniformBallMeasure (0 : E) 1).map (fun x ↦ p.1 + p.2 • x) else 0) :=
    Measurable.ite (measurableSet_le measurable_const measurable_snd)
      (TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry (by fun_prop))
      measurable_const
  convert hpiece using 1
  funext p
  split_ifs with hr
  · exact uniformBallMeasure_eq_map_unitBall p.1 hr
  · exact uniformBallMeasure_of_neg (lt_of_not_ge hr)

end TauCeti.Probability

namespace Measurable

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Measurable centers and radii give a measurable family of uniform ball laws, with no
restriction on the sign of the radius. -/
@[fun_prop]
theorem uniformBallMeasure {c : T → E} {r : T → ℝ} (hc : Measurable c) (hr : Measurable r) :
    Measurable (fun t ↦ TauCeti.Probability.uniformBallMeasure (c t) (r t)) :=
  TauCeti.Probability.measurable_uniformBallMeasure.comp (hc.prodMk hr)

end Measurable
