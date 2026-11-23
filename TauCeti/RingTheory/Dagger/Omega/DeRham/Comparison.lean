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
`TauCeti.KaehlerDeRham.exteriorDeriv` with `Omega.exteriorDeriv`, and that
`(ofKaehlerEquiv R A).exteriorPower` is an isomorphism of exterior derivatives whenever `Ω[A⁄R]` is
also finite over `A`.
-/

public section

namespace TauCeti.Dagger.Omega

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherian A (Omega R A)]

/-- **Comparison with algebraic Kähler forms**: `ofKaehler` intertwines
`TauCeti.KaehlerDeRham.exteriorDeriv` with `Omega.exteriorDeriv` in every degree when
`Omega R A` is Noetherian over `A`. -/
theorem map_ofKaehler_exteriorDeriv (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.map (q + 1) (ofKaehler R A) (TauCeti.KaehlerDeRham.exteriorDeriv R A q ω) =
      exteriorDeriv R A q (exteriorPower.map q (ofKaehler R A) ω) := by
  apply Subtype.ext
  rw [← exteriorPower.mapSemilinear_eq_map (q + 1), ← exteriorPower.mapSemilinear_eq_map q]
  simp only [exteriorPower.coe_mapSemilinear_apply, coe_exteriorDeriv_apply,
    TauCeti.KaehlerDeRham.coe_exteriorDeriv_apply]
  suffices h : ∀ x : ExteriorAlgebra A Ω[A⁄R],
      ExteriorAlgebra.mapSemilinear (ofKaehler R A) (TauCeti.KaehlerDeRham.extDeriv R A x) =
        exteriorAlgebraDeriv R A (ExteriorAlgebra.mapSemilinear (ofKaehler R A) x) from h ω.val
  intro x
  induction x using TauCeti.KaehlerDeRham.inductionOn with
  | algebraMap a =>
    rw [TauCeti.KaehlerDeRham.extDeriv_algebraMap, ExteriorAlgebra.mapSemilinear_ι, ofKaehler_D,
      ExteriorAlgebra.mapSemilinear_algebraMap, RingHom.id_apply, exteriorAlgebraDeriv_algebraMap]
  | ι_D a =>
    rw [TauCeti.KaehlerDeRham.extDeriv_ι_D, map_zero, ExteriorAlgebra.mapSemilinear_ι, ofKaehler_D,
      exteriorAlgebraDeriv_ι_apply]
  | mul x y hx hy =>
    simp only [map_mul, TauCeti.KaehlerDeRham.extDeriv_mul, map_add,
      ExteriorAlgebra.mapSemilinear_involute, hx, hy]
    exact (exteriorAlgebraDeriv_mul _ _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- When `Omega R A` is Noetherian over `A` and algebraic Kähler differentials `Ω[A⁄R]` are
finite over `A`, `(ofKaehlerEquiv R A).exteriorPower` identifies the algebraic and universally
finite exterior derivatives. -/
theorem ofKaehlerEquiv_exteriorDeriv [Module.Finite A Ω[A⁄R]] (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (ofKaehlerEquiv R A).exteriorPower (q + 1) (TauCeti.KaehlerDeRham.exteriorDeriv R A q ω) =
      exteriorDeriv R A q ((ofKaehlerEquiv R A).exteriorPower q ω) := by
  rw [← LinearEquiv.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap,
    LinearEquiv.exteriorPower_toLinearMap, LinearEquiv.exteriorPower_toLinearMap,
    show (ofKaehlerEquiv R A).toLinearMap = ofKaehler R A from
      LinearMap.ext (ofKaehlerEquiv_apply R A)]
  exact map_ofKaehler_exteriorDeriv q ω

end TauCeti.Dagger.Omega
