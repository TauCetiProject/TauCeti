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

A scheme `X` smooth of relative dimension one over a field `k` has regular local rings
(`TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth`) and dimension one
(`TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension`). So its local
rings at codimension-one points are discrete valuation rings, and if it is moreover integral and
proper over `k`, it is a curve over `k`.

## Main results

* `AlgebraicGeometry.Scheme.IsCurveOver.of_smooth`: an integral proper scheme smooth of relative
  dimension one over `k` is a curve over `k`.
* `AlgebraicGeometry.Scheme.isDiscreteValuationRing_stalk_of_smooth`: the local rings of an
  integral scheme smooth over `k` at its codimension-one points are discrete valuation rings.
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

variable (k) in
/-- The local ring of an integral scheme smooth over `k` at a codimension-one point is a discrete
valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_smooth [IsIntegral X] [Smooth (X ↘ Spec (.of k))]
    (y : CodimensionOnePoint X) : IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := by
  have := isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) (y : X)
  infer_instance

end AlgebraicGeometry.Scheme
