/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Proper

/-!
# The two-chart model is a curve

The two-chart model of an algebraic function field is an example of a proper integral curve.
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

end TauCeti.AlgebraicGeometry.twoChartModel
