/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.RingTheory.Dagger.Omega.DeRham
public import TauCeti.RingTheory.Dagger.Omega.Kaehler
public import TauCeti.RingTheory.DeRham.Differential

/-!
# Comparison of overconvergent and algebraic de Rham differentials

Shows that when `A` is Noetherian and `Omega R A` is finite over `A`, the canonical map
`ofKaehler R A : Ω[A⁄R] →ₗ[A] Omega R A` intertwines the ordinary algebraic de Rham differential
`TauCeti.DeRham.d` with `Omega.extDerivPow`, and that `(ofKaehlerEquiv R A).exteriorPower` is an
isomorphism of exterior derivatives whenever `Ω[A⁄R]` is also finite over `A`.
-/

public section

namespace TauCeti.Dagger.Omega

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A]
  [Module.Finite A (Omega R A)]

/-- **Comparison with algebraic de Rham forms**: `ofKaehler` intertwines `TauCeti.DeRham.d`
with `Omega.extDerivPow` in every degree when `A` is Noetherian and `Omega R A` is finite over
`A`. -/
theorem map_ofKaehler_extDerivPow (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.map (q + 1) (ofKaehler R A) (TauCeti.DeRham.d R A q ω) =
      extDerivPow R A q (exteriorPower.map q (ofKaehler R A) ω) :=
  LinearMap.congr_fun
    (TauCeti.DeRham.forms_hom_ext
      (f := (exteriorPower.map (q + 1) (ofKaehler R A)).restrictScalars R ∘ₗ
        TauCeti.DeRham.d R A q)
      (g := extDerivPow R A q ∘ₗ (exteriorPower.map q (ofKaehler R A)).restrictScalars R)
      fun c v ↦ by
        simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
        rw [TauCeti.DeRham.d_elementary, TauCeti.DeRham.elementary_def, map_smul,
          exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, Fin.comp_cons]
        simp [Function.comp_def, extDerivPow_smul_ιMulti]) ω

/-- When `A` is Noetherian, `Omega R A` is finite over `A`, and algebraic Kähler differentials
`Ω[A⁄R]` are finite over `A`, `(ofKaehlerEquiv R A).exteriorPower` identifies the algebraic and
universally finite exterior derivatives. -/
theorem ofKaehlerEquiv_extDerivPow [Module.Finite A Ω[A⁄R]] (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (ofKaehlerEquiv R A).exteriorPower (q + 1) (TauCeti.DeRham.d R A q ω) =
      extDerivPow R A q ((ofKaehlerEquiv R A).exteriorPower q ω) := by
  rw [← LinearEquiv.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap,
    LinearEquiv.exteriorPower_toLinearMap, LinearEquiv.exteriorPower_toLinearMap,
    ofKaehlerEquiv_toLinearMap]
  exact map_ofKaehler_extDerivPow q ω

end TauCeti.Dagger.Omega
