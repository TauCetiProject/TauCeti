/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Partial differentiation of substitution subalgebras

The chain rule over a coefficient algebra characterizes when the image of
`MvPowerSeries.substAlgHom` is stable under a partial derivative. It suffices to
test the derivatives of the substituted series
(`MvPowerSeries.mapsTo_pderiv_range_substAlgHom_iff`).

In particular, if `Y' = G(Y)` with `G` over the base ring, then the series in the
parameters `Y(L_j)` with coefficients in that ring are stable under partial
differentiation whenever the linear forms `L_j` have coefficients in the base
ring (`MvPowerSeries.mapsTo_pderiv_range_substAlgHom_of_derivative_eq_subst`).
This uses `MvPowerSeries.pderiv_substAlgHom` and `PowerSeries.pderiv_subst`.

The application to integral series in the formal parameter of a CM elliptic curve
follows `New.CMLattice.pderiv_mem_multiSeriesRing` in
`grh/src/New/Derivatives/FormalGroup/Resolution.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace MvPowerSeries

variable {σ τ : Type*}

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {a : σ → MvPowerSeries τ S}

/-- The substitution image is stable under a partial derivative exactly when it
contains the derivatives of the substituted series. -/
theorem mapsTo_pderiv_range_substAlgHom_iff [Finite σ] {ha : HasSubst a} {i : τ} :
    Set.MapsTo (pderiv i : MvPowerSeries τ S → MvPowerSeries τ S)
      (substAlgHom ha : MvPowerSeries σ R →ₐ[R] _).range
      (substAlgHom ha : MvPowerSeries σ R →ₐ[R] _).range ↔
    ∀ j, pderiv i (a j) ∈ (substAlgHom (R := R) ha).range := by
  constructor
  · intro h j
    have hj : a j ∈ (substAlgHom (R := R) ha).range := ⟨X j, substAlgHom_X ha j⟩
    exact h hj
  · intro h F hF
    obtain ⟨f, rfl⟩ := (AlgHom.mem_range (substAlgHom ha)).mp hF
    let := Fintype.ofFinite σ
    rw [pderiv_substAlgHom ha]
    exact Subalgebra.sum_mem _ fun j _ ↦
      Subalgebra.mul_mem _ ((substAlgHom ha).mem_range_self (pderiv j f)) (h j)

variable {b : σ → MvPowerSeries τ S} {y : PowerSeries S}
variable (hy : PowerSeries.HasSubst y) (hb : ∀ j, PowerSeries.HasSubst (b j))

/-- Series over `R` in the parameters `y(b j)` are stable under differentiation in
`X i` if `y' = g(y)` with `g` over `R` and each `∂ᵢ b_j` is a scalar from `R`.
In particular, one can take the `b_j` to be integral linear forms. -/
theorem mapsTo_pderiv_range_substAlgHom_of_derivative_eq_subst [Finite σ]
    {i : τ} {g : PowerSeries R} (hyg : PowerSeries.derivative y = PowerSeries.subst y g)
    {c : σ → R}
    (hc : ∀ j, pderiv i (b j) = algebraMap R (MvPowerSeries τ S) (c j)) :
    Set.MapsTo (pderiv (R := S) i)
      (substAlgHom (R := R) (hasSubst_of_constantCoeff_nilpotent
        fun j ↦ hy.comp (hb j))).range
      (substAlgHom (R := R) (hasSubst_of_constantCoeff_nilpotent
        fun j ↦ hy.comp (hb j))).range := by
  let a : σ → MvPowerSeries τ S := fun k ↦ PowerSeries.substAlgHom (hb k) y
  have ha : HasSubst a := hasSubst_of_constantCoeff_nilpotent fun k ↦ hy.comp (hb k)
  refine (mapsTo_pderiv_range_substAlgHom_iff (ha := ha)).mpr fun j ↦ ?_
  have hderiv : pderiv i (a j) = PowerSeries.subst (a j) g *
      algebraMap R (MvPowerSeries τ S) (c j) := by
    have hj : a j = PowerSeries.subst (b j) y := by
      simp only [a, PowerSeries.coe_substAlgHom]
    rw [hj, PowerSeries.pderiv_subst (hb j), hyg,
      PowerSeries.subst_comp_subst_apply hy (hb j), hc j]
  rw [hderiv, ← subst_X (R := R) ha j,
    ← subst_powerSeriesSubst ha (PowerSeries.HasSubst.X (S := R) j) g,
    ← substAlgHom_apply (R := R) ha]
  exact Subalgebra.mul_mem _ ((substAlgHom ha).mem_range_self _)
    ((substAlgHom ha).range.algebraMap_mem (c j))

end

end MvPowerSeries
