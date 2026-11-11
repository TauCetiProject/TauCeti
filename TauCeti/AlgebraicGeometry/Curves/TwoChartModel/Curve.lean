/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Curves.Smooth
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Proper

/-!
# The two-chart model is a curve

The two-chart model of an algebraic function field is an example of a proper integral curve.
Over a perfect field it is moreover smooth of relative dimension one
(`TauCeti.AlgebraicGeometry.twoChartModel.smoothOfRelativeDimension_one_of_perfectField`), being a
regular curve.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.twoChartModel

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
  {hF : TauCeti.IsFunctionField k F} {x : F} {hx : x ≠ 0}

/-- The two-chart model of a function field is a proper integral curve with that function field. -/
theorem isCurveOver (hxt : Transcendental k x) :
    (twoChartModel hF hx).IsCurveOver k := by
  exact @AlgebraicGeometry.Scheme.IsCurveOver.mk (twoChartModel hF hx) k _ _ inferInstance
    (isProper hxt) (topologicalKrullDim_eq_one hxt)

/-- **Over a perfect field the two-chart model is smooth** of relative dimension one, for `x`
transcendental over `k`: it is a regular curve. -/
theorem smoothOfRelativeDimension_one_of_perfectField [PerfectField k]
    (hxt : Transcendental k x) :
    SmoothOfRelativeDimension 1 (twoChartModel hF hx ↘ Spec (.of k)) := by
  have := isCurveOver (hF := hF) (hx := hx) hxt
  have := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  exact AlgebraicGeometry.Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField k _

end TauCeti.AlgebraicGeometry.twoChartModel
