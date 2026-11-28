/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.IntegralClosure.FixedField
import TauCeti.RingTheory.DiscreteValuationRing.Invariant

/-!
# Discrete valuation ring instances for integral closures in Galois fixed fields

For a Galois subgroup `H ≤ Gal(L/K)` and a base ring `A` acting on `L` through `K`, if
`integralClosure A L` is a discrete valuation ring then so is
`integralClosure A (IntermediateField.fixedField H)`.

## Main results

* `TauCeti.instIsDiscreteValuationRingIntegralClosureFixedField`: transfers
  `IsDiscreteValuationRing` from `integralClosure A L` to `integralClosure A (fixedField H)`.
-/

public section

namespace TauCeti

/-- If `integralClosure A L` is a DVR and `H ≤ Gal(L/K)`, then
`integralClosure A (fixedField H)` is a DVR. -/
instance instIsDiscreteValuationRingIntegralClosureFixedField {A K L : Type*} [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [_root_.IsDiscreteValuationRing (integralClosure A L)] {H : Subgroup (L ≃ₐ[K] L)} :
    _root_.IsDiscreteValuationRing (integralClosure A (IntermediateField.fixedField H)) :=
  have : Algebra.IsIntegral (FixedPoints.subalgebra A (integralClosure A L) H)
      (integralClosure A L) := Algebra.IsIntegral.tower_top A
  have := isDiscreteValuationRing_fixedPoints_subalgebra_of_isIntegral
    (A := A) (B := integralClosure A L) (G := H)
  _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsSubalgebraIntegralClosureEquiv A H)

end TauCeti
