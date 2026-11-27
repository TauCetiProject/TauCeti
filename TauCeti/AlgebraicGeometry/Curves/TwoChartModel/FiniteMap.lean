/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Finite
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Curve
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Map

/-!
# Finite morphisms between two-chart models

An extension of algebraic function fields induces a morphism of their two-chart models. Both
models are curves over the constant field and the induced morphism is dominant, so it is finite,
as is every nonconstant morphism of curves
(`AlgebraicGeometry.Scheme.Hom.isFinite_of_isDominant_of_isCurveOver`).

This is the global finiteness assertion for the normalization morphism. It applies to inseparable
extensions as well.

See Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.2 and
Appendix B.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

/-- The morphism of two-chart models induced by a finite function-field extension is finite.
This includes inseparable extensions. -/
theorem isFinite_map (hF : IsFunctionField k F) (hF' : IsFunctionField k F')
    {x : F} (hx : x ≠ 0) {x' : F'} (hx' : x' ≠ 0)
    (h : algebraMap F F' x = x') (hxt : Transcendental k x) :
    IsFinite (map hF hF' hx hx' h) := by
  -- Both models are curves over `k`, and `map` is a dominant morphism over `k`.
  have := isCurveOver (hF := hF) (hx := hx) hxt
  have := isCurveOver (hF := hF') (hx := hx')
    (h ▸ (transcendental_algebraMap_iff (algebraMap F F').injective).2 hxt)
  exact (map hF hF' hx hx' h).isFinite_of_isDominant_of_isCurveOver k

end TauCeti.AlgebraicGeometry.twoChartModel
