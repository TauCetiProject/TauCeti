/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
public import TauCeti.NumberTheory.LocalField.MaximalPrime
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Integral models along an extension of valued fields

For a compatible extension `L/K` of valued fields (`ValuativeExtension K L`), the valuation ring
of `K` maps into that of `L` compatibly with `K → L`. So `WeierstrassCurve.IsIntegral.baseChange`
applies: an equation integral over the valuation ring of `K` has a base change to `L` integral over
the valuation ring of `L`. This is what gives the points over `L` of such a base change a
reduction, and a subgroup `E₀(L)` of points with nonsingular reduction.

## Main results

* `WeierstrassCurve.isIntegral_valuationSubring_baseChange`: along a compatible extension `L/K` of
  valued fields, an equation integral over the valuation ring of `K` stays integral over that of
  `L`.
* `WeierstrassCurve.integralModel_valuationSubring_maximalPrime`: for a nonarchimedean local field
  `L`, the same holds over the valuation ring of the adic valuation of the maximal ideal
  `TauCeti.maximalPrime L` of `𝒪[L]`, where the integral model of the base change is the image of
  the integral model over the valuation ring of `K`.
-/

public section

namespace WeierstrassCurve

open ValuativeRel

/-- **Integrality along an extension of valued fields.** If `L/K` is a compatible extension of
valued fields, the base change to `L` of an equation with coefficients in the valuation ring of `K`
has coefficients in the valuation ring of `L`, so its points over `L` have a reduction and a
subgroup `E₀(L)` of points with nonsingular reduction. -/
instance isIntegral_valuationSubring_baseChange {K L : Type*} [Field K] [ValuativeRel K] [Field L]
    [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] (W : WeierstrassCurve K)
    [IsIntegral (valuation K).integer W] :
    IsIntegral (valuation L).valuationSubring (W.baseChange L) :=
  IsIntegral.baseChange (R := (valuation K).integer) (S := (valuation L).integer)
    (RingHom.ext fun x ↦ TauCeti.coe_algebraMap_integerRing x) W

section MaximalPrime

/-! The statements over the fraction field of a Dedekind domain apply over a local field `L` at the
maximal ideal `TauCeti.maximalPrime L` of `𝒪[L]`. The valuation ring of its adic valuation is
`𝒪[L]` again, and the declarations below supply the integral model of `W` over it. -/

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] (W : WeierstrassCurve K)
  [IsIntegral 𝒪[K] W]

/-- The base change of an equation integral over `𝒪[K]` is integral over the valuation ring of the
adic valuation of the maximal ideal of `𝒪[L]`. -/
instance isIntegral_valuationSubring_maximalPrime :
    IsIntegral ((maximalPrime L).valuation L).valuationSubring (W⁄L) :=
  IsIntegral.baseChange (R := 𝒪[K]) (S := ((maximalPrime L).valuation L).valuationSubring)
    (RingHom.ext coe_algebraMap_valuationSubringMaximalPrime) W

/-- The integral model of the base change of `W` over the valuation ring of the adic valuation of
the maximal ideal of `𝒪[L]` is the image of the integral model of `W` over `𝒪[K]`. -/
theorem integralModel_valuationSubring_maximalPrime :
    integralModel ((maximalPrime L).valuation L).valuationSubring (W⁄L) =
      (integralModel 𝒪[K] W).map
        (algebraMap 𝒪[K] ((maximalPrime L).valuation L).valuationSubring) :=
  integralModel_baseChange (R := 𝒪[K]) (S := ((maximalPrime L).valuation L).valuationSubring)
    (RingHom.ext coe_algebraMap_valuationSubringMaximalPrime) W

end MaximalPrime

end WeierstrassCurve

end
