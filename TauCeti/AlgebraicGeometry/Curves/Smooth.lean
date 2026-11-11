/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Curves.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Smooth curves

A scheme `X` smooth of relative dimension one over a field `k` has dimension one
(`TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension`). So if it is
moreover integral and proper over `k`, it is a curve over `k`. Its local rings at codimension-one
points are discrete valuation rings by
`TauCeti.AlgebraicGeometry.isDiscreteValuationRing_stalk_of_smooth`.

Conversely, over a perfect field `k` a curve whose local rings at codimension-one points are
discrete valuation rings is smooth of relative dimension one over `k`: all its local rings are
then regular (`AlgebraicGeometry.Scheme.Hom.smooth_of_isRegularLocalRing_stalk`). So over a
perfect field the regular proper curves are exactly the smooth ones. Over an imperfect field a
regular curve need not be smooth.

## Main results

* `AlgebraicGeometry.Scheme.IsCurveOver.of_smooth`: an integral proper scheme smooth of relative
  dimension one over `k` is a curve over `k`.
* `AlgebraicGeometry.Scheme.IsCurveOver.smoothOfRelativeDimension_one_of_perfectField`: a regular
  curve over a perfect field is smooth of relative dimension one.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (k X) in
/-- An integral proper scheme smooth of relative dimension one over `k` is a curve over `k`. -/
theorem IsCurveOver.of_smooth [IsIntegral X] [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] : X.IsCurveOver k :=
  ⟨topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))⟩

variable (k X) in
/-- **A regular curve over a perfect field is smooth**: if the local rings of a curve `X` over a
perfect field `k` at its codimension-one points are discrete valuation rings, then `X` is smooth
of relative dimension one over `k`. -/
theorem IsCurveOver.smoothOfRelativeDimension_one_of_perfectField [PerfectField k]
    [X.IsCurveOver k]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))] :
    SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
    have := IsCurveOver.valuationRing_stalk k X x
    infer_instance
  have := (X ↘ Spec (.of k)).smooth_of_isRegularLocalRing_stalk
  exact smoothOfRelativeDimension_of_topologicalKrullDim_eq _
    (IsCurveOver.topologicalKrullDim_eq_one k)

end AlgebraicGeometry.Scheme
