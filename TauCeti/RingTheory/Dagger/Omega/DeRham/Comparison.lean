/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.DeRham
public import TauCeti.RingTheory.Dagger.Omega.Kaehler
public import TauCeti.RingTheory.Kaehler.DeRham.ExteriorPower

/-!
# Comparison of overconvergent and algebraic Kähler exterior derivatives

Shows that when `A` is Noetherian and `Omega R A` is finite over `A`, the canonical map
`ofKaehler R A : Ω[A⁄R] →ₗ[A] Omega R A` intertwines the algebraic Kähler exterior derivative
`TauCeti.KaehlerDeRham.exteriorPowerDeriv` with `Omega.extDerivPow`, and that
`(ofKaehlerEquiv R A).exteriorPower` is an isomorphism of exterior derivatives whenever `Ω[A⁄R]` is
also finite over `A`.
-/

public section

namespace TauCeti.Dagger.Omega

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A]
  [Module.Finite A (Omega R A)]

/-- **Comparison with algebraic Kähler forms**: `ofKaehler` intertwines
`TauCeti.KaehlerDeRham.exteriorPowerDeriv` with `Omega.extDerivPow` in every degree when `A` is
Noetherian and `Omega R A` is finite over `A`. -/
theorem map_ofKaehler_extDerivPow (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.map (q + 1) (ofKaehler R A)
        (TauCeti.KaehlerDeRham.exteriorPowerDeriv R A q ω) =
      extDerivPow R A q (exteriorPower.map q (ofKaehler R A) ω) :=
  Subtype.ext <| by
    simpa only [exteriorPower.coe_map, coe_extDerivPow_apply,
      TauCeti.KaehlerDeRham.coe_exteriorPowerDeriv_apply] using map_ofKaehler_extDeriv ω.val

/-- When `A` is Noetherian, `Omega R A` is finite over `A`, and algebraic Kähler differentials
`Ω[A⁄R]` are finite over `A`, `(ofKaehlerEquiv R A).exteriorPower` identifies the algebraic and
universally finite exterior derivatives. -/
theorem ofKaehlerEquiv_extDerivPow [Module.Finite A Ω[A⁄R]] (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (ofKaehlerEquiv R A).exteriorPower (q + 1)
        (TauCeti.KaehlerDeRham.exteriorPowerDeriv R A q ω) =
      extDerivPow R A q ((ofKaehlerEquiv R A).exteriorPower q ω) := by
  rw [← LinearEquiv.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap,
    LinearEquiv.exteriorPower_toLinearMap, LinearEquiv.exteriorPower_toLinearMap,
    show (ofKaehlerEquiv R A).toLinearMap = ofKaehler R A from
      LinearMap.ext (ofKaehlerEquiv_apply R A)]
  exact map_ofKaehler_extDerivPow q ω

end TauCeti.Dagger.Omega
