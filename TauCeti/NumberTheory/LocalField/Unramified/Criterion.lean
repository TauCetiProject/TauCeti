/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Etale
public import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
public import TauCeti.NumberTheory.LocalField.Different.Basic
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic

/-!
# Unramified extensions of local fields via generators

An extension `L/K` of nonarchimedean local fields is unramified when `L = K(b)` for an integral
element `b` which is a root of a polynomial `p` over `𝒪[K]` whose derivative `p'(b)` is a unit.
Conversely every unramified extension is of this form: `𝒪[L]` is generated over `𝒪[K]` by one
element at which its minimal polynomial has unit derivative. This is the criterion through which
unramifiedness is transported along base change and composita.

The basic instance is a radical extension: if `L = K(β)` with `β^n = a ∈ Kˣ`, where `n` is prime
to the residue characteristic and divides `v_K(a)`, then `L/K` is unramified. Dividing `β` by a
power of a uniformizer of `K` turns it into a unit `y` with `y^n` a unit of `𝒪[K]`, and `X^n − y^n`
has unit derivative `n y^{n−1}` at `y`.

## Main results

* `TauCeti.isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative`: `L = K(b)` is unramified
  over `K` when `b` is a root of a polynomial over `𝒪[K]` whose derivative at `b` is a unit.
* `TauCeti.isUnramified_iff_exists_adjoin_eq_top_and_isUnit_aeval_derivative_minpoly`: `L/K` is
  unramified exactly when `𝒪[L]` is generated over `𝒪[K]` by an element at which its minimal
  polynomial has unit derivative.
* `TauCeti.isUnramified_of_adjoin_eq_top_of_pow_eq`: `K(a^{1/n})/K` is unramified when `n` is
  prime to the residue characteristic and divides `v_K(a)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

open ValuativeRel IsLocalRing Polynomial

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **A simple root of an integral polynomial generates an unramified extension.** If `L = K(b)`
for an element `b` of `𝒪[L]` which is a root of a polynomial `p` over `𝒪[K]` whose derivative
`p'(b)` is a unit of `𝒪[L]`, then `L/K` is unramified. -/
theorem isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative {b : 𝒪[L]}
    (hb : IntermediateField.adjoin K {algebraMap 𝒪[L] L b} = ⊤) {p : 𝒪[K][X]}
    (hp : aeval b p = 0) (hu : IsUnit (aeval b (derivative p))) : IsUnramified K L := by
  have := finite_of_valuativeExtension K L
  have hbint : IsIntegral 𝒪[K] b := .of_finite 𝒪[K] b
  -- The derivative of the minimal polynomial of `b` over `𝒪[K]` divides `p'(b)` at `b`.
  have hu' : IsUnit (aeval b (derivative (minpoly 𝒪[K] b))) := by
    obtain ⟨q, rfl⟩ := minpoly.isIntegrallyClosed_dvd hbint hp
    have h : aeval b (derivative (minpoly 𝒪[K] b * q)) =
        aeval b (derivative (minpoly 𝒪[K] b)) * aeval b q := by
      simp [derivative_mul]
    exact isUnit_of_mul_isUnit_left (h ▸ hu)
  -- So `b` is separable over `K`, and hence so is `L = K(b)`.
  have : Algebra.IsSeparable K L := by
    have hsep : IsSeparable K (algebraMap 𝒪[L] L b) := by
      rw [IsSeparable, separable_iff_derivative_ne_zero
        (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))]
      intro h0
      have h1 : aeval (algebraMap 𝒪[L] L b) (derivative (minpoly K (algebraMap 𝒪[L] L b))) = 0 :=
        by rw [h0, map_zero]
      rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hbint, derivative_map,
        aeval_map_algebraMap, aeval_algebraMap_apply] at h1
      exact hu'.ne_zero (FaithfulSMul.algebraMap_injective 𝒪[L] L (by rw [h1, map_zero]))
    rw [← separableClosure.eq_top_iff, eq_top_iff, ← hb, IntermediateField.adjoin_simple_le_iff]
    exact mem_separableClosure_iff.2 hsep
  -- The unit `f'(b)` lies in the different ideal, which is therefore trivial.
  have hK : Algebra.adjoin K {algebraMap 𝒪[L] L b} = ⊤ := by
    rwa [← IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun y _ ↦ IsAlgebraic.of_finite K y)]
  have hd := conductor_mul_differentIdeal 𝒪[K] K L b hK
  rw [Ideal.span_singleton_eq_top.2 hu'] at hd
  exact (differentIdeal_eq_top_iff K L).1 (eq_top_iff.2 (hd ▸ Ideal.mul_le_right))

/-- **Radical extensions by roots of units are unramified.** Let `L = K(β)` with `β^n = a` for
some `a ∈ Kˣ`, where the residue characteristic `p` of `K` does not divide `n`. If `n` divides
the normalized valuation `v_K(a)`, then `L/K` is unramified. -/
theorem isUnramified_of_adjoin_eq_top_of_pow_eq {n : ℕ} (hn : ¬ ringChar 𝓀[K] ∣ n) {β : L}
    (hβ : IntermediateField.adjoin K {β} = ⊤) {a : Kˣ} (ha : β ^ n = algebraMap K L a)
    (hdvd : (n : ℤ) ∣ (normalizedValuation K a).toAdd) : IsUnramified K L := by
  have := finite_of_valuativeExtension K L
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  -- Write `a = u π^{nk}` with `π` a uniformizer and `u` a unit of `𝒪[K]`.
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨u, m, hu1, rfl⟩ := exists_eq_mul_zpow_of_irreducible hϖ a
  set π : Kˣ := Units.mk0 (ϖ : K) (fun h => hϖ.ne_zero (Subtype.ext h))
  have hm : m = n * k := by
    rwa [map_mul, map_zpow, (normalizedValuation_eq_one_iff u).2 hu1,
      normalizedValuation_irreducible hϖ, one_mul, ← ofAdd_zsmul, toAdd_ofAdd, smul_eq_mul,
      mul_one] at hk
  subst hm
  -- `y = β / π^k` is an `n`-th root of `u`.
  set y : L := β * algebraMap K L ((π ^ k)⁻¹ : Kˣ) with hy_def
  have hyn : y ^ n = algebraMap K L u := by
    rw [hy_def, mul_pow, ha, ← map_pow, ← map_mul]
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, ← zpow_natCast, ← zpow_mul,
      mul_comm (n : ℤ) k]
    simp [zpow_mul]
  set c : 𝒪[K] := ⟨u, (Valuation.mem_integer_iff _ _).2 hu1.le⟩
  have hc : IsUnit c := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).2 hu1
  -- `y` is integral over `𝒪[K]`, hence lies in `𝒪[L]`, where it is a unit.
  have hyO : y ∈ 𝒪[L] := by
    rw [integerRing_eq_integralClosure K L]
    refine ⟨X ^ n - C c, monic_X_pow_sub_C c hn0, ?_⟩
    rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hyn,
      IsScalarTower.algebraMap_apply 𝒪[K] K L, sub_eq_zero]
    rfl
  set b : 𝒪[L] := ⟨y, hyO⟩
  have hbn : b ^ n = algebraMap 𝒪[K] 𝒪[L] c := Subtype.ext (by simp [b, c, hyn])
  have hb : IsUnit b := (isUnit_pow_iff hn0).1 (hbn ▸ hc.map _)
  have hnL : IsUnit (n : 𝒪[L]) := by
    simpa using ((IsLocalRing.isUnit_natCast_iff_not_dvd (R := 𝒪[K])).2 hn).map
      (algebraMap 𝒪[K] 𝒪[L])
  -- So `b` is a simple root of `X^n − c`.
  refine isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative (b := b)
    (p := X ^ n - C c) ?_ ?_ ?_
  · -- `K(y) = K(β)`, since `y` and `β` differ by a factor in `K`.
    refine top_le_iff.1 (hβ ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)
    have : β = y * algebraMap K L (π ^ k : Kˣ) := by
      rw [hy_def, mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
        mul_one]
    rw [this]
    exact mul_mem (IntermediateField.mem_adjoin_simple_self K _)
      (IntermediateField.algebraMap_mem _ _)
  · rw [map_sub, map_pow, aeval_X, aeval_C, hbn, sub_self]
  · rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, map_pow, aeval_X,
      aeval_C]
    simpa using hnL.mul (hb.pow _)

/-- **Unramified extensions are generated by simple roots of integral polynomials.** An extension
`L/K` of nonarchimedean local fields is unramified exactly when `𝒪[L]` is generated as an
`𝒪[K]`-algebra by an element `b` at which the derivative of its minimal polynomial over `𝒪[K]` is
a unit. -/
theorem isUnramified_iff_exists_adjoin_eq_top_and_isUnit_aeval_derivative_minpoly :
    IsUnramified K L ↔ ∃ b : 𝒪[L], Algebra.adjoin 𝒪[K] {b} = ⊤ ∧
      IsUnit (aeval b (derivative (minpoly 𝒪[K] b))) := by
  refine ⟨fun h ↦ ?_, fun ⟨b, hb, hu⟩ ↦
    isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative
    (TauCeti.IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top hb) (minpoly.aeval _ _) hu⟩
  have := (isUnramified_iff_etale K L).1 h
  obtain ⟨b, hb⟩ := IsLocalRing.exists_adjoin_eq_top (R := 𝒪[K]) (S := 𝒪[L])
  exact ⟨b, hb, IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top hb⟩

end TauCeti
