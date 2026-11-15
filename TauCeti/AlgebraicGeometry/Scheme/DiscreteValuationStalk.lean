/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Regularity and valuation rings at codimension-one points

At a codimension-one point of a scheme, the local ring has Krull dimension one. If it is
regular, it is a discrete valuation ring. This turns the regularity hypothesis on a curve
into the valuation-ring hypothesis used to define orders of vanishing and to compare Weil
and Cartier divisors. On an integral scheme of dimension at most one whose codimension-one local
rings are discrete valuation rings, every local ring is a valuation ring: the function field at
the generic point, and a discrete valuation ring elsewhere. This is the hypothesis under which
morphisms from the generic point into proper schemes extend to the whole scheme.

The first result combines
`TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one` with Mathlib's
`ringKrullDim_stalk_eq_coheight`.
-/

public section

open AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace CodimensionOnePoint

/-- The stalk at a regular codimension-one point is a discrete valuation ring. -/
instance (priority := low) isDiscreteValuationRing_stalk {X : Scheme.{u}}
    (x : CodimensionOnePoint X)
    [IsRegularLocalRing (X.presheaf.stalk (x : X))] :
    IsDiscreteValuationRing (X.presheaf.stalk (x : X)) := by
  apply IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
  rw [ringKrullDim_stalk_eq_coheight]
  simp [x.property]

end CodimensionOnePoint

namespace Scheme

/-- **The local rings of an integral scheme of dimension at most one are valuation rings** when
its codimension-one local rings are discrete valuation rings (for instance when it is regular): at
the generic point the local ring is the function field, and every other point has codimension
one. -/
theorem valuationRing_stalk_of_topologicalKrullDim_le_one
    {X : Scheme.{u}} [IsIntegral X] (hX : topologicalKrullDim X ≤ 1)
    [hDVR : ∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  by_cases hx : x = genericPoint X
  · subst hx
    exact inferInstanceAs (ValuationRing X.functionField)
  · have := hDVR ⟨x, (coheight_eq_one_iff_ne_genericPoint hX).mpr hx⟩
    infer_instance

end Scheme

end AlgebraicGeometry

end TauCeti
