/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Isogeny invariance of the L-function

Isogenous elliptic curves over a number field have the same local Euler factors at every finite
place, and therefore the same formal Dirichlet series. The local comparison includes additive
and both kinds of multiplicative reduction. Here it is applied to the completions in Mathlib's
`WeierstrassCurve.LFunction`, using the identification of their two rings of integers.

## Main results

* `TauCeti.Isogeny.localEulerFactor_eq_of_localField`: equality over any local field.
* `TauCeti.Isogeny.localEulerFactor_eq_adicCompletion`: equality of the factors over a completion.
* `TauCeti.Isogeny.LFunction_eq`: isogenous elliptic curves have the same L-function.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix C, §16.
-/

public section

open ValuativeRel WeierstrassCurve IsDedekindDomain

namespace TauCeti.Isogeny

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- Isogenous elliptic curves over a nonarchimedean local field have the same local Euler factor
as a formal Dirichlet series. -/
theorem localEulerFactor_eq_of_localField (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.localEulerFactor 𝒪[K] = W₂.localEulerFactor 𝒪[K] := by
  rw [localEulerFactor, localEulerFactor, localPowerSeries, localPowerSeries,
    φ.localPolynomial_eq_of_localField]

end LocalField

/-- Isogenous elliptic curves over an adic completion have the same local Euler factor,
using the completion's canonical integer ring. -/
theorem localEulerFactor_eq_adicCompletion
    {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {p : HeightOneSpectrum R} [Finite (R ⧸ p.asIdeal)]
    {W₁ W₂ : WeierstrassCurve (p.adicCompletion K)} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.localEulerFactor (p.adicCompletionIntegers K) =
      W₂.localEulerFactor (p.adicCompletionIntegers K) := by
  have he := φ.localEulerFactor_eq_of_localField
  -- The canonical valuation ring and the adic-completion integer ring are the same subring.
  -- Abstract the subring before substituting its equality, so its DVR instances transport too.
  have transport (S : Subring (p.adicCompletion K))
      [IsDiscreteValuationRing S] [IsFractionRing S (p.adicCompletion K)]
      (hS : S = 𝒪[p.adicCompletion K]) :
      W₁.localEulerFactor S = W₂.localEulerFactor S := by
    subst S
    exact he
  -- Passing to `toSubring` changes only the bundle, so these instance carriers coincide.
  have : IsDiscreteValuationRing (p.adicCompletionIntegers K).toSubring :=
    inferInstanceAs (IsDiscreteValuationRing (p.adicCompletionIntegers K))
  have : IsFractionRing (p.adicCompletionIntegers K).toSubring (p.adicCompletion K) :=
    inferInstanceAs (IsFractionRing (p.adicCompletionIntegers K) (p.adicCompletion K))
  exact transport (p.adicCompletionIntegers K).toSubring
    (p.integer_eq_adicCompletionIntegers (K := K)).symm

/-- Isogenous elliptic curves over a number field have the same L-function as a formal Dirichlet
series, including the Euler factors at all bad places. -/
theorem LFunction_eq {K : Type*} [Field K] [NumberField K]
    {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) : W₁.LFunction = W₂.LFunction := by
  rw [WeierstrassCurve.LFunction, WeierstrassCurve.LFunction]
  apply congrArg ArithmeticFunction.eulerProduct
  funext p
  exact (φ.map (algebraMap K (p.adicCompletion K))).localEulerFactor_eq_adicCompletion

end TauCeti.Isogeny
