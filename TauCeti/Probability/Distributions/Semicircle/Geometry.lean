/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.Basic
public import TauCeti.Probability.Distributions.Uniform.Ball.Coordinate

/-!
# The semicircle law from uniform disk coordinates

Each coordinate of a point uniformly distributed in the planar unit disk has the
unit-radius semicircle law. This identifies the geometric marginal with the affine
Beta realization, so the elementary semicircle density and cdf apply directly to
disk coordinates.

This is the two-dimensional case of the ball-coordinate law `map_eval_uniformBallMeasure`.

## References

* K.-T. Fang, S. Kotz, K. W. Ng, *Symmetric Multivariate and Related Distributions*,
  Chapman and Hall, 1990, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- A coordinate of a uniform point in the planar unit disk has the semicircle law. -/
@[simp] theorem map_eval_uniformBallMeasure_eq_semicircleMeasure
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 2) (i : ι) :
    (uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map (fun x ↦ x i) =
      semicircleMeasure := by
  rw [map_eval_uniformBallMeasure, semicircleMeasure_eq_map_betaMeasure]
  norm_num [hι]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- Every coordinate of a uniformly distributed planar unit-disk point is semicircular. -/
theorem HasLaw.eval_uniformBallMeasure_semicircle
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 2) (i : ι)
    {X : Ω → EuclideanSpace ℝ ι}
    (hX : HasLaw X (uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1) P) :
    HasLaw (fun ω ↦ X ω i) semicircleMeasure P :=
  (HasLaw.mk (by fun_prop)
    (map_eval_uniformBallMeasure_eq_semicircleMeasure hι i)).fun_comp hX

end ProbabilityTheory
