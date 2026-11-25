/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Completion
public import TauCeti.RingTheory.FittingIdeal.Basic
import TauCeti.RingTheory.DedekindDomain.Different.Kaehler

/-!
# The Kähler different of a place with separable residue field

Let `F' / F` be a finite separable extension of function fields and `P'` a place of `F'` over
`P = P'.restrict k F`. The Kähler different of the completed extension `𝒪̂_{P'} / 𝒪̂_P` is the
zeroth Fitting ideal of `Ω[𝒪̂_{P'}⁄𝒪̂_P]`, the completed local form of the ramification ideal
sheaf `TauCeti.AlgebraicGeometry.ramificationIdealSheaf` of a finite map of curves.

When the residue extension at `P'` is separable, the completed extension is monogenic, and the
Kähler different is `𝔪̂_{P'} ^ d(P' ∣ P)`, with `d(P' ∣ P)` the exponent of the trace-dual
different. Only the residue extension at `P'` is assumed separable: the constant fields are
arbitrary, and other places of `F'` may be wildly ramified or have inseparable residue
extensions.

## Main results

* `TauCeti.Place.fittingIdeal_kaehlerDifferential_completionIntegers_eq_maximalIdeal_pow`:
  `Fitt₀(Ω[𝒪̂_{P'}⁄𝒪̂_P]) = 𝔪̂_{P'} ^ d(P' ∣ P)` when the residue extension is separable.

## References

* [Stacks Project, Tag 0BVH](https://stacks.math.columbia.edu/tag/0BVH): the Kähler different.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Corollary 2 of Proposition 11 and Proposition 12.
-/

public section

open IsLocalRing

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- **The Kähler different at a place with separable residue field.** If the residue extension at
`P'` over `P = P'.restrict k F` is separable, the zeroth Fitting ideal of the differentials of the
completed valuation ring `𝒪̂_{P'}` over `𝒪̂_P` is `𝔪̂_{P'} ^ d(P' ∣ P)`, the trace-dual different
of `P'`. -/
theorem fittingIdeal_kaehlerDifferential_completionIntegers_eq_maximalIdeal_pow (P' : Place k' F')
    [Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField] :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    haveI := (P'.restrict k F).moduleFinite_completionIntegers P' rfl
    fittingIdeal P'.completionPlace.integers
        Ω[P'.completionPlace.integers⁄(P'.restrict k F).completionPlace.integers] 0 =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).moduleFinite_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  have := (P'.isSeparable_residueField_completion_iff (k := k) (F := F)).mpr ‹_›
  rw [IsDiscreteValuationRing.fittingIdeal_kaehlerDifferential_eq_differentIdeal
      (P'.restrict k F).Completion P'.Completion,
    (P'.restrict k F).differentIdeal_completionIntegers_eq_maximalIdeal_pow P' rfl]

end TauCeti.Place
