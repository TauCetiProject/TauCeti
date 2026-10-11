/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Proper
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField

/-!
# Proper integral curves over a field

A curve over a field is an integral scheme that is proper and one-dimensional over that field.
Its function field is therefore an algebraic function field of one variable. The two-chart model
of any algebraic function field provides a regular proper curve with that function field.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A curve over a field is an integral, proper scheme of dimension one over that field. -/
class IsCurveOver (k : Type u) [Field k] [X.Over (Spec (.of k))] : Prop
    extends IsIntegral X, IsProper (X ↘ Spec (.of k)) where
  /-- The curve has dimension one. -/
  topologicalKrullDim_eq_one : topologicalKrullDim X = 1

/-- The defining properties of a curve over a field. -/
@[simp]
theorem isCurveOver_iff : X.IsCurveOver k ↔
    IsIntegral X ∧ IsProper (X ↘ Spec (.of k)) ∧ topologicalKrullDim X = 1 := by
  constructor
  · intro hX
    exact ⟨hX.toIsIntegral, hX.toIsProper, hX.topologicalKrullDim_eq_one⟩
  · rintro ⟨hI, hP, hdim⟩
    exact @IsCurveOver.mk X k _ _ hI hP hdim

/-- The function field of a curve over `k` is an algebraic function field of one variable. -/
theorem IsCurveOver.isFunctionField [X.IsCurveOver k] :
    TauCeti.IsFunctionField k X.functionField := by
  exact (TauCeti.AlgebraicGeometry.isFunctionField_functionField_iff k).2
    (IsCurveOver.topologicalKrullDim_eq_one k)

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry.twoChartModel

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
  {hF : TauCeti.IsFunctionField k F} {x : F} {hx : x ≠ 0}

/-- The two-chart model of a function field is a proper integral curve with that function field. -/
theorem isCurveOver (hxt : Transcendental k x) :
    (twoChartModel hF hx).IsCurveOver k := by
  exact @AlgebraicGeometry.Scheme.IsCurveOver.mk (twoChartModel hF hx) k _ _ inferInstance
    (isProper hxt) (topologicalKrullDim_eq_one hxt)

end TauCeti.AlgebraicGeometry.twoChartModel
