/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.DeRham.Derivative
public import TauCeti.RingTheory.Dagger.Omega.Kaehler
public import TauCeti.RingTheory.Kaehler.DeRham.ExteriorPower

/-!
# Comparison of overconvergent and algebraic Kähler exterior derivatives

Shows that when `Omega R A` is Noetherian over `A`, the canonical map
`ofKaehler R A : Ω[A⁄R] →ₗ[A] Omega R A` intertwines the algebraic Kähler exterior derivative
`TauCeti.KaehlerDeRham.exteriorPowerDeriv` with `Omega.exteriorPowerDeriv`, and that
`(ofKaehlerEquiv R A).exteriorPower` is an isomorphism of exterior derivatives whenever `Ω[A⁄R]` is
also finite over `A`.
-/

public section

namespace TauCeti.Dagger.Omega

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherian A (Omega R A)]

/-- **Comparison with algebraic Kähler forms**: `ofKaehler` intertwines
`TauCeti.KaehlerDeRham.exteriorPowerDeriv` with `Omega.exteriorPowerDeriv` in every degree when
`Omega R A` is Noetherian over `A`. -/
theorem map_ofKaehler_exteriorPowerDeriv (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.map (q + 1) (ofKaehler R A)
        (TauCeti.KaehlerDeRham.exteriorPowerDeriv R A q ω) =
      exteriorPowerDeriv R A q (exteriorPower.map q (ofKaehler R A) ω) := by
  rw [← exteriorPower.mapSemilinear_eq_map (q + 1), ← exteriorPower.mapSemilinear_eq_map q]
  exact Derivation.mapSemilinear_exteriorPowerDeriv _ _ _ _ _ _ _ _ (AlgHom.id R A)
    (ofKaehler R A) (ofKaehler_D R A) q ω

/-- When `Omega R A` is Noetherian over `A` and algebraic Kähler differentials `Ω[A⁄R]` are
finite over `A`, `(ofKaehlerEquiv R A).exteriorPower` identifies the algebraic and universally
finite exterior derivatives. -/
theorem ofKaehlerEquiv_exteriorPowerDeriv [Module.Finite A Ω[A⁄R]] (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (ofKaehlerEquiv R A).exteriorPower (q + 1)
        (TauCeti.KaehlerDeRham.exteriorPowerDeriv R A q ω) =
      exteriorPowerDeriv R A q ((ofKaehlerEquiv R A).exteriorPower q ω) := by
  rw [← LinearEquiv.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap,
    LinearEquiv.exteriorPower_toLinearMap, LinearEquiv.exteriorPower_toLinearMap,
    show (ofKaehlerEquiv R A).toLinearMap = ofKaehler R A from
      LinearMap.ext (ofKaehlerEquiv_apply R A)]
  exact map_ofKaehler_exteriorPowerDeriv q ω

end TauCeti.Dagger.Omega
