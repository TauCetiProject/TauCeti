/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Multivariate power-series substitution into formal Laurent series

Let `K` be a field, `q ∈ MvPowerSeries σ K` a nonzero multivariate power series with zero constant
coefficient, and `L` a field containing `MvPowerSeries σ K` (for instance
`FractionRing (MvPowerSeries σ K)` or `K⸨X⸩` when `σ = Unit`). Since `PowerSeries.subst q` has
trivial kernel (`PowerSeries.subst_eq_zero_iff`), its composition with `algebraMap` into `L` is
injective and therefore extends uniquely to a `K`-algebra homomorphism
`TauCeti.LaurentSeries.mvSubstAlgHom : K⸨X⸩ →ₐ[K] L`, compatible with univariate Laurent
substitution `TauCeti.LaurentSeries.substAlgHom`.

This evaluates rational functions expanded as Laurent series at independent formal parameters
`(X_i)_{i ∈ σ}`, for example when comparing formal-group laws with geometric addition on curves.

## Main definitions

* `TauCeti.LaurentSeries.mvSubstAlgHom`: substitution `f ↦ f(q)` of a nonzero multivariate power
  series `q` of zero constant coefficient into `K⸨X⸩`, landing in any field `L` faithful over
  `MvPowerSeries σ K`.

## Main results

* `TauCeti.LaurentSeries.mvSubstAlgHom_coe`: on `K⟦X⟧`, `mvSubstAlgHom` agrees with
  `PowerSeries.subst q` composed with `algebraMap`.
* `TauCeti.LaurentSeries.mvSubstAlgHom_single`: on Laurent monomials `a X ^ n` (`n : ℤ`),
  `mvSubstAlgHom` evaluates to `a q ^ n`.
* `TauCeti.LaurentSeries.mvSubstAlgHom_single_mul_coe`: `(X ^ N * f₊)(q) = q ^ N * f₊(q)`.
* `TauCeti.LaurentSeries.mvSubstAlgHom_comp_substAlgHom`: precomposing `mvSubstAlgHom` with
  `TauCeti.LaurentSeries.substAlgHom` substitutes the composite series `g(q)`.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries

namespace TauCeti.LaurentSeries

variable {K σ : Type*} [Field K]

section Def

variable (L : Type*) [Field L] [Algebra K L] [Algebra (MvPowerSeries σ K) L]
  [IsScalarTower K (MvPowerSeries σ K) L] [FaithfulSMul (MvPowerSeries σ K) L]
  {q : MvPowerSeries σ K} (hq : MvPowerSeries.constantCoeff q = 0) (hq₀ : q ≠ 0)

include hq hq₀ in
private theorem injective_mvSubstAlgHom_coe :
    Function.Injective
      ((IsScalarTower.toAlgHom K (MvPowerSeries σ K) L).comp
        (PowerSeries.substAlgHom (R := K) (.of_constantCoeff_zero hq))) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (MvPowerSeries σ K) L),
    PowerSeries.coe_substAlgHom] at hf
  exact (PowerSeries.subst_eq_zero_iff hq hq₀).mp hf

/-- Substitution `f ↦ f(q)` of a nonzero multivariate power series `q ∈ MvPowerSeries σ K` with
zero constant coefficient into formal Laurent series `K⸨X⸩`, valued in any field `L` containing
`MvPowerSeries σ K` (for instance `FractionRing (MvPowerSeries σ K)`). -/
noncomputable def mvSubstAlgHom : K⸨X⸩ →ₐ[K] L :=
  IsFractionRing.liftAlgHom (injective_mvSubstAlgHom_coe L hq hq₀)

end Def

variable {L : Type*} [Field L] [Algebra K L] [Algebra (MvPowerSeries σ K) L]
  [IsScalarTower K (MvPowerSeries σ K) L] [FaithfulSMul (MvPowerSeries σ K) L]
  {q : MvPowerSeries σ K} (hq : MvPowerSeries.constantCoeff q = 0) (hq₀ : q ≠ 0)

/-- On formal power series, `mvSubstAlgHom` agrees with `PowerSeries.subst q` followed by the
algebra map into `L`. -/
@[simp]
theorem mvSubstAlgHom_coe (f : K⟦X⟧) :
    mvSubstAlgHom L hq hq₀ (f : K⸨X⸩) =
      algebraMap (MvPowerSeries σ K) L (PowerSeries.subst q f) := by
  rw [mvSubstAlgHom, IsFractionRing.coe_liftAlgHom, ← _root_.LaurentSeries.coe_algebraMap,
    IsFractionRing.lift_algebraMap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', PowerSeries.coe_substAlgHom]

/-- Multivariate Laurent substitution sends the variable `X = single 1 1` to the image of `q`. -/
theorem mvSubstAlgHom_single_one :
    mvSubstAlgHom L hq hq₀ (single 1 1) = algebraMap (MvPowerSeries σ K) L q := by
  rw [← PowerSeries.coe_X, mvSubstAlgHom_coe, PowerSeries.subst_X (.of_constantCoeff_zero hq)]

/-- Multivariate Laurent substitution sends the monomial `a X ^ n`, for every integer `n`, to
`a q ^ n` in `L`. -/
@[simp]
theorem mvSubstAlgHom_single (n : ℤ) (a : K) :
    mvSubstAlgHom L hq hq₀ (single n a) =
      algebraMap K L a * algebraMap (MvPowerSeries σ K) L q ^ n := by
  rw [← mul_one a, ← zero_add n, ← single_mul_single, mul_one, zero_add, map_mul,
    RatFunc.single_zpow, map_zpow₀, mvSubstAlgHom_single_one, ← HahnSeries.C_apply,
    ← _root_.LaurentSeries.algebraMap_apply, AlgHom.commutes]

/-- Writing a Laurent series as `X ^ N * f₊` with `f₊` a power series, its multivariate
substitution is `q ^ N * f₊(q)` in `L`. -/
theorem mvSubstAlgHom_single_mul_coe (N : ℤ) (f : K⟦X⟧) :
    mvSubstAlgHom L hq hq₀ (single N 1 * (f : K⸨X⸩)) =
      algebraMap (MvPowerSeries σ K) L q ^ N *
        algebraMap (MvPowerSeries σ K) L (PowerSeries.subst q f) := by
  rw [map_mul, mvSubstAlgHom_single, mvSubstAlgHom_coe, map_one, one_mul]

/-- Precomposing `mvSubstAlgHom` at `q` with univariate Laurent substitution `substAlgHom` by `g`
equals `mvSubstAlgHom` at the substituted multivariate series `g(q)`. -/
theorem mvSubstAlgHom_comp_substAlgHom {g : K⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    (hg₀ : g ≠ 0) :
    (mvSubstAlgHom L hq hq₀).comp (substAlgHom hg hg₀) =
      mvSubstAlgHom L (PowerSeries.constantCoeff_subst_eq_zero hq g hg)
        (PowerSeries.subst_ne_zero hq hq₀ hg₀) := by
  apply AlgHom.toRingHom_injective
  refine IsFractionRing.ringHom_ext (A := K⟦X⟧) fun f ↦ ?_
  simp only [RingHom.coe_coe, AlgHom.comp_apply]
  rw [_root_.LaurentSeries.coe_algebraMap, substAlgHom_coe, mvSubstAlgHom_coe, mvSubstAlgHom_coe,
    PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero' hg) (.of_constantCoeff_zero hq)]

/-- Pointwise form of `mvSubstAlgHom_comp_substAlgHom`. -/
theorem mvSubstAlgHom_comp_substAlgHom_apply {g : K⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    (hg₀ : g ≠ 0) (f : K⸨X⸩) :
    mvSubstAlgHom L hq hq₀ (substAlgHom hg hg₀ f) =
      mvSubstAlgHom L (PowerSeries.constantCoeff_subst_eq_zero hq g hg)
        (PowerSeries.subst_ne_zero hq hq₀ hg₀) f :=
  congr($(mvSubstAlgHom_comp_substAlgHom hq hq₀ hg hg₀) f)

end TauCeti.LaurentSeries

end
