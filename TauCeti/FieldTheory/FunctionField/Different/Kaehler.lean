/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Completion
public import TauCeti.RingTheory.FittingIdeal.Basic
import TauCeti.RingTheory.DedekindDomain.Different.Kaehler
import TauCeti.RingTheory.FittingIdeal.BaseChange

/-!
# The Kähler different of a place with separable residue field

Let `F' / F` be a finite separable extension of function fields and `P'` a place of `F'` over
`P = P'.restrict k F`. The Kähler different of the valuation-ring extension `𝒪_{P'} / 𝒪_P` (and of
the completed extension `𝒪̂_{P'} / 𝒪̂_P`) is the zeroth Fitting ideal of `Ω[𝒪_{P'}⁄𝒪_P]` (or
`Ω[𝒪̂_{P'}⁄𝒪̂_P]`), the local form of the ramification ideal sheaf
`TauCeti.AlgebraicGeometry.ramificationIdealSheaf` of a finite map of curves.

When the residue extension at `P'` is separable, `𝒪_{P'}` is the localization at the centre of `P'`
of the local model `𝒪'_P`, which is locally monogenic there, and the Kähler different is
`𝔪_{P'} ^ d(P' ∣ P)`, with `d(P' ∣ P)` the exponent of the trace-dual different (and likewise on
completions `𝔪̂_{P'} ^ d(P' ∣ P)`). Only the residue extension at `P'` is assumed separable: the
constant fields are arbitrary, and other places of `F'` may be wildly ramified or have inseparable
residue extensions.

## Main results

* `TauCeti.Place.moduleFinite_kaehlerDifferential_integers`: `Ω[𝒪_{P'}⁄𝒪_P]` is finite over
  `𝒪_{P'}`.
* `TauCeti.Place.fittingIdeal_kaehlerDifferential_integers_eq_maximalIdeal_pow`:
  `Fitt₀(Ω[𝒪_{P'}⁄𝒪_P]) = 𝔪_{P'} ^ d(P' ∣ P)` when the residue extension is separable.
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

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

private theorem isBaseChange_kaehlerDifferential_integers (P' : Place k' F') :
    letI := algebraIntegralClosureIntegers k F P'
    haveI : IsScalarTower (P'.restrict k F).integers
        (integralClosure (P'.restrict k F).integers F') P'.integers :=
      isScalarTower_integers_integralClosure_integers k F P'
    _root_.IsBaseChange P'.integers
      (KaehlerDifferential.map (P'.restrict k F).integers (P'.restrict k F).integers
        (integralClosure (P'.restrict k F).integers F') P'.integers) :=
  letI := algebraIntegralClosureIntegers k F P'
  haveI : IsScalarTower (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F') P'.integers :=
    isScalarTower_integers_integralClosure_integers k F P'
  haveI : IsLocalization (centerIntegralClosure k F P').asIdeal.primeCompl P'.integers :=
    isLocalization_centerIntegralClosure_integers k F P'
  haveI : Algebra.FormallyEtale (integralClosure (P'.restrict k F).integers F') P'.integers :=
    .of_isLocalization (centerIntegralClosure k F P').asIdeal.primeCompl
  KaehlerDifferential.isBaseChange_of_formallyEtale _ _ _

/-- **Finiteness of relative differentials of valuation rings**: for a finite separable extension
`F' / F` of function fields and a place `P'` over `P = P'.restrict k F`, `Ω[𝒪_{P'}⁄𝒪_P]` is a
finitely generated `𝒪_{P'}`-module, because `𝒪_{P'}` is a localization of the module-finite local
model `𝒪'_P`. -/
theorem moduleFinite_kaehlerDifferential_integers (P' : Place k' F') :
    Module.Finite P'.integers Ω[P'.integers⁄(P'.restrict k F).integers] :=
  letI := algebraIntegralClosureIntegers k F P'
  haveI : IsScalarTower (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F') P'.integers :=
    isScalarTower_integers_integralClosure_integers k F P'
  haveI : Module.Finite (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F') :=
    IsIntegralClosure.finite _ F F' _
  Module.Finite.equiv (isBaseChange_kaehlerDifferential_integers (k := k) (F := F) P').equiv

/-- **The Kähler different at a place with separable residue field**: if `F' / F` is finite and
separable and the residue extension `F'_{P'} / F_P` at `P'` over `P = P'.restrict k F` is
separable, then `Fitt₀(Ω[𝒪_{P'}⁄𝒪_P]) = 𝔪_{P'} ^ d(P' ∣ P)`, the trace-dual different at `P'`. -/
theorem fittingIdeal_kaehlerDifferential_integers_eq_maximalIdeal_pow (P' : Place k' F')
    [Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField] :
    haveI := moduleFinite_kaehlerDifferential_integers (k := k) (F := F) P'
    fittingIdeal P'.integers Ω[P'.integers⁄(P'.restrict k F).integers] 0 =
      maximalIdeal P'.integers ^ differentExponent k F P' := by
  let O := (P'.restrict k F).integers
  let B := integralClosure O F'
  let q := centerIntegralClosure k F P'
  let _ := algebraIntegralClosureIntegers k F P'
  have : IsScalarTower O B P'.integers :=
    isScalarTower_integers_integralClosure_integers k F P'
  have : IsLocalization q.asIdeal.primeCompl P'.integers :=
    isLocalization_centerIntegralClosure_integers k F P'
  have : IsLocalization.AtPrime P'.integers q.asIdeal := ‹_›
  have : Module.Finite O B := IsIntegralClosure.finite O F F' B
  have hbc : (haveI := moduleFinite_kaehlerDifferential_integers (k := k) (F := F) P'
      fittingIdeal P'.integers Ω[P'.integers⁄O] 0) =
      (fittingIdeal B Ω[B⁄O] 0).map (algebraMap B P'.integers) :=
    (isBaseChange_kaehlerDifferential_integers (k := k) (F := F) P').fittingIdeal_eq_map 0
  have : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  let _ : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  let _ : Field (B ⧸ q.asIdeal) := Ideal.Quotient.field _
  have : Algebra.IsSeparable (O ⧸ maximalIdeal O) (B ⧸ q.asIdeal) :=
    (isSeparable_quotient_centerIntegralClosure_iff k F P').mpr ‹_›
  rw [hbc, TauCeti.fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map
      F F' (p := maximalIdeal O) q.asIdeal P'.integers,
    differentIdeal_map_integers_eq_maximalIdeal_pow k F P']

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
