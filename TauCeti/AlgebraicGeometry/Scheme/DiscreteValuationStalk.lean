/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
-- Proof-only: the local rings of the integral scheme `Spec R` are domains.
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Regularity and valuation rings at codimension-one points

At a codimension-one point of a scheme, the local ring has Krull dimension one. If it is
regular, it is a discrete valuation ring. This turns the regularity hypothesis on a curve
into the valuation-ring hypothesis used to define orders of vanishing and to compare Weil
and Cartier divisors.

The result combines `TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`
with Mathlib's `ringKrullDim_stalk_eq_coheight`.

The same conclusion holds on an open subscheme `Spec R` with `R` a Dedekind domain: the local
ring at a codimension-one point there is the localization of `R` at a nonzero prime, a discrete
valuation ring. This is how a scheme glued from spectra of Dedekind domains, such as the
normalization of a curve, is seen to have discrete valuation rings as its local rings at
codimension-one points.

## Main results

* `TauCeti.AlgebraicGeometry.CodimensionOnePoint.isDiscreteValuationRing_stalk`: the stalk at a
  regular codimension-one point is a discrete valuation ring.
* `TauCeti.AlgebraicGeometry.isDiscreteValuationRing_stalk_of_isDedekindDomain`: at a point of
  codimension one in the image of an open immersion from the spectrum of a Dedekind domain, the
  stalk is a discrete valuation ring.
-/

public section

open AlgebraicGeometry CategoryTheory Order

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

/-- **Codimension-one points of a Dedekind chart have discrete valuation ring stalks**: if
`f : Spec R ⟶ X` is an open immersion and `R` is a Dedekind domain, then
the stalk of `X` at a codimension-one point `f q` is a discrete valuation ring. It is the
localization of `R` at the nonzero prime `q`. The domain instance on the stalk, needed to state the
conclusion, holds automatically when `X` is integral; `X` itself need not be. -/
theorem isDiscreteValuationRing_stalk_of_isDedekindDomain {X : Scheme.{u}}
    {R : CommRingCat.{u}} [IsDedekindDomain R] (f : Spec R ⟶ X) [IsOpenImmersion f] (q : Spec R)
    [IsDomain (X.presheaf.stalk (f q))] (hq : coheight (f q) = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk (f q)) := by
  rw [coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight] at hq
  have hq0 : q.asIdeal ≠ ⊥ := by
    rintro h
    rw [h, Ideal.height_bot] at hq
    exact zero_ne_one hq
  have := q.isPrime
  let : Algebra R ((Spec R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hq0
    ((Spec R).presheaf.stalk q)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry

end TauCeti
