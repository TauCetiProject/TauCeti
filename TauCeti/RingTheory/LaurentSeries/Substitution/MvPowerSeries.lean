/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic
public import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors

/-!
# Multivariate power-series substitution into formal Laurent series

Let `R` be a commutative ring without zero divisors and `q ∈ MvPowerSeries σ R` a nonzero
multivariate power series with zero constant coefficient. Substituting `q` into a univariate power
series `f ∈ R⟦X⟧` sends only `0` to `0` (`PowerSeries.subst_mvPowerSeries_eq_zero_iff`),
generalising `PowerSeries.subst_eq_zero_iff` from one variable to an arbitrary variable set `σ`.

Over a field `K`, this injectivity extends `PowerSeries.subst q` to a `K`-algebra homomorphism
`TauCeti.LaurentSeries.mvSubstAlgHom : K⸨X⸩ →ₐ[K] FractionRing (MvPowerSeries σ K)`, compatible
with univariate Laurent substitution `TauCeti.LaurentSeries.substAlgHom`. This evaluates rational
functions expanded as Laurent series at independent formal parameters `(X_i)_{i ∈ σ}`, for example
when comparing formal-group laws with geometric addition on curves.

## Main definitions

* `TauCeti.LaurentSeries.mvSubstAlgHom`: substitution `f ↦ f(q)` of a nonzero multivariate power
  series `q` of zero constant coefficient into `K⸨X⸩`, landing in
  `FractionRing (MvPowerSeries σ K)`.

## Main results

* `PowerSeries.subst_mvPowerSeries_eq_zero_iff` and `PowerSeries.subst_mvPowerSeries_ne_zero`:
  substituting `q` into `R⟦X⟧` has trivial kernel.
* `TauCeti.LaurentSeries.mvSubstAlgHom_coe`: on `K⟦X⟧`, `mvSubstAlgHom` agrees with
  `PowerSeries.subst q` composed with `algebraMap`.
* `TauCeti.LaurentSeries.mvSubstAlgHom_comp_substAlgHom`: precomposing `mvSubstAlgHom` with
  `TauCeti.LaurentSeries.substAlgHom` substitutes the composite series `g(q)`.
-/

public section

open scoped LaurentSeries PowerSeries

namespace PowerSeries

variable {R σ : Type*} [CommRing R] [NoZeroDivisors R] {q : MvPowerSeries σ R}

/-- **Substituting a nonzero multivariate power series `q` of zero constant coefficient into `R⟦X⟧`
sends only `0` to `0`.** -/
theorem subst_mvPowerSeries_eq_zero_iff (hq : MvPowerSeries.constantCoeff q = 0) (hq₀ : q ≠ 0)
    {f : R⟦X⟧} :
    PowerSeries.subst q f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ by_contra fun hf ↦ ?_, fun h ↦ by simp [h]⟩
  have hs : HasSubst q := .of_constantCoeff_zero hq
  rw [← X_pow_order_mul_divXPowOrder (f := f), subst_mul hs, subst_pow hs, subst_X hs] at h
  rcases mul_eq_zero.mp h with hpow | hdiv
  · exact pow_ne_zero _ hq₀ hpow
  · have hc := congrArg MvPowerSeries.constantCoeff hdiv
    rw [map_zero, constantCoeff_subst_of_constantCoeff_zero hq,
      Algebra.algebraMap_self_apply] at hc
    exact constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf hc

/-- Substituting a nonzero multivariate power series `q` of zero constant coefficient into a nonzero
univariate power series yields a nonzero series. -/
theorem subst_mvPowerSeries_ne_zero (hq : MvPowerSeries.constantCoeff q = 0) (hq₀ : q ≠ 0)
    {f : R⟦X⟧} (hf : f ≠ 0) :
    PowerSeries.subst q f ≠ 0 :=
  (subst_mvPowerSeries_eq_zero_iff hq hq₀).not.mpr hf

end PowerSeries

namespace TauCeti.LaurentSeries

variable {K σ : Type*} [Field K] {q : MvPowerSeries σ K}
  (hq : MvPowerSeries.constantCoeff q = 0) (hq₀ : q ≠ 0)

include hq hq₀ in
private theorem injective_mvSubstAlgHom_coe :
    Function.Injective
      ((IsScalarTower.toAlgHom K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))).comp
        (PowerSeries.substAlgHom (R := K) (.of_constantCoeff_zero hq))) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    map_eq_zero_iff _ (IsFractionRing.injective (MvPowerSeries σ K) _),
    PowerSeries.coe_substAlgHom] at hf
  exact (PowerSeries.subst_mvPowerSeries_eq_zero_iff hq hq₀).mp hf

/-- Substitution `f ↦ f(q)` of a nonzero multivariate power series `q ∈ MvPowerSeries σ K` with
zero constant coefficient into formal Laurent series `K⸨X⸩`, valued in
`FractionRing (MvPowerSeries σ K)`. -/
noncomputable def mvSubstAlgHom : K⸨X⸩ →ₐ[K] FractionRing (MvPowerSeries σ K) :=
  IsFractionRing.liftAlgHom (injective_mvSubstAlgHom_coe hq hq₀)

/-- On formal power series, `mvSubstAlgHom` agrees with `PowerSeries.subst q` followed by the
canonical map into `FractionRing (MvPowerSeries σ K)`. -/
@[simp]
theorem mvSubstAlgHom_coe (f : K⟦X⟧) :
    mvSubstAlgHom hq hq₀ (f : K⸨X⸩) =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
        (PowerSeries.subst q f) := by
  rw [mvSubstAlgHom, IsFractionRing.coe_liftAlgHom, ← _root_.LaurentSeries.coe_algebraMap,
    IsFractionRing.lift_algebraMap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', PowerSeries.coe_substAlgHom]

/-- Precomposing `mvSubstAlgHom` at `q` with univariate Laurent substitution `substAlgHom` by `g`
equals `mvSubstAlgHom` at the substituted multivariate series `g(q)`. -/
theorem mvSubstAlgHom_comp_substAlgHom {g : K⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    (hg₀ : g ≠ 0) :
    (mvSubstAlgHom hq hq₀).comp (substAlgHom hg hg₀) =
      mvSubstAlgHom (PowerSeries.constantCoeff_subst_eq_zero hq g hg)
        (PowerSeries.subst_mvPowerSeries_ne_zero hq hq₀ hg₀) := by
  apply AlgHom.toRingHom_injective
  refine IsFractionRing.ringHom_ext (A := K⟦X⟧) fun f ↦ ?_
  simp only [RingHom.coe_coe, AlgHom.comp_apply]
  rw [_root_.LaurentSeries.coe_algebraMap, substAlgHom_coe, mvSubstAlgHom_coe, mvSubstAlgHom_coe,
    PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero' hg) (.of_constantCoeff_zero hq)]

/-- Pointwise form of `mvSubstAlgHom_comp_substAlgHom`. -/
theorem mvSubstAlgHom_comp_substAlgHom_apply {g : K⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    (hg₀ : g ≠ 0) (f : K⸨X⸩) :
    mvSubstAlgHom hq hq₀ (substAlgHom hg hg₀ f) =
      mvSubstAlgHom (PowerSeries.constantCoeff_subst_eq_zero hq g hg)
        (PowerSeries.subst_mvPowerSeries_ne_zero hq hq₀ hg₀) f :=
  congr($(mvSubstAlgHom_comp_substAlgHom hq hq₀ hg hg₀) f)

end TauCeti.LaurentSeries

end
