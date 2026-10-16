/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Differentiation of Laurent series

This file bundles the coefficientwise formal derivative `D` of Laurent series as a derivation over
any commutative ring, using the Leibniz rule from `LaurentSeries.Basic`. The bundle allows the
universal property of Kähler differentials to compare it with differentiation of algebraic
functions in a local parameter.

It then records how `D` interacts with the order `ord = HahnSeries.orderTop` and with the
valuation topology of `K⸨X⸩`. The coefficient of `Xⁿ⁻¹` in `D f` is `n` times the coefficient of
`Xⁿ` in `f`, so `D` lowers the order by at most one. The order drops by exactly one when the
leading exponent `r` times the leading coefficient is nonzero, for instance over a field in which
`r` is nonzero. In general the order of `D f` is one less than the first exponent `n` with
`n • f.coeff n ≠ 0`, and `D f = 0` when there is no such exponent. Without additive torsion, as
in characteristic zero, the kernel of `D` is the constants. Over a field, `D` satisfies the
inverse and quotient rules, and it maps the neighbourhood `{f | v f ≤ exp (-m)}` of zero into
`{f | v f ≤ exp (-(m - 1))}`, so it is continuous for the valuation topology.

The underlying linear map is Mathlib's `LaurentSeries.derivative`; no new differentiation
operation is introduced.

## Main results

* `TauCeti.laurentSeriesDerivation`: `D` as a derivation.
* `LaurentSeries.coeff_derivative_order_sub_one`: the coefficient of `X ^ (r - 1)` in `D f` is
  `r` times the leading coefficient of `f`, where `r = f.order`.
* `LaurentSeries.orderTop_le_orderTop_derivative_add_one`: `ord f ≤ ord (D f) + 1`.
* `LaurentSeries.orderTop_derivative_eq_sub_one`: the order of `D f` is one less than the first
  exponent whose coefficient survives differentiation.
* `LaurentSeries.orderTop_derivative_eq_order_sub_one_of_cast_ne_zero`: if the order `r` of
  `f ≠ 0` is nonzero in a ring without zero divisors, then `ord (D f) = r - 1`.
* `LaurentSeries.derivative_eq_zero_iff_exists_C`: without additive torsion the kernel of `D`
  consists of the constants.
* `LaurentSeries.derivative_inv` and `LaurentSeries.derivative_div`: the inverse and quotient
  rules over a field.
* `LaurentSeries.continuous_derivative`: `D` is continuous for the valuation topology.
-/

public section

open HahnSeries Filter Topology
open scoped LaurentSeries

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- Formal Laurent differentiation as a derivation. Its linear map is the existing
coefficientwise derivative. -/
noncomputable def laurentSeriesDerivation :
    Derivation R (LaurentSeries R) (LaurentSeries R) where
  toFun f := _root_.LaurentSeries.derivative R f
  map_add' f g := (_root_.LaurentSeries.derivative R).map_add f g
  map_smul' c f := by
    -- The source uses the algebra action; Mathlib's derivative uses the coefficientwise action.
    rw [Algebra.smul_def, laurentSeries_algebraMap_mul_eq_smul]
    exact map_smul (_root_.LaurentSeries.derivative R) c f
  map_one_eq_zero' := by
    ext n
    suffices n + 1 = 0 → (n : R) + 1 = 0 by
      simpa [_root_.LaurentSeries.derivative_apply, coeff_one]
    intro h
    simpa using congrArg (fun i : ℤ ↦ (i : R)) h
  leibniz' f g := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    rw [_root_.LaurentSeries.derivative_mul]
    ring

/-- The bundled Laurent derivation evaluates as the coefficientwise derivative. -/
@[simp]
theorem laurentSeriesDerivation_apply (f : LaurentSeries R) :
    laurentSeriesDerivation R f = _root_.LaurentSeries.derivative R f := (rfl)

end TauCeti

namespace LaurentSeries

section Module

variable {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]

/-- The coefficient of `Xⁿ` in `f'` is `n + 1` times the coefficient of `Xⁿ⁺¹` in `f`. -/
theorem coeff_derivative (f : LaurentSeries V) (n : ℤ) :
    (derivative R f).coeff n = (n + 1) • f.coeff (n + 1) := by
  simp

/-- The coefficient of `Xⁿ⁻¹` in `f'` is `n` times the coefficient of `Xⁿ` in `f`. -/
theorem coeff_derivative_sub_one (f : LaurentSeries V) (n : ℤ) :
    (derivative R f).coeff (n - 1) = n • f.coeff n := by
  simp

/-- The coefficient of `X ^ (r - 1)` in `f'`, where `r` is the order of `f`, is `r` times the
leading coefficient of `f`. -/
theorem coeff_derivative_order_sub_one (f : LaurentSeries V) :
    (derivative R f).coeff (f.order - 1) = f.order • f.leadingCoeff := by
  rw [coeff_derivative_sub_one, leadingCoeff_eq]

/-- **Differentiation lowers the order by at most one**: `ord f ≤ ord f' + 1`. -/
theorem orderTop_le_orderTop_derivative_add_one (f : LaurentSeries V) :
    f.orderTop ≤ (derivative R f).orderTop + 1 := by
  obtain h | h := eq_or_ne (derivative R f) 0
  · simp [h]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr h)
  have hc := coeff_orderTop_ne hk.symm
  rw [coeff_derivative] at hc
  rw [← hk, ← WithTop.coe_one, ← WithTop.coe_add]
  exact orderTop_le_of_coeff_ne_zero (right_ne_zero_of_smul hc)

/-- If `n` is the first exponent with `n • f.coeff n ≠ 0`, then `f'` has order `n - 1`. -/
theorem orderTop_derivative_eq_sub_one {f : LaurentSeries V} {n : ℤ} (hn : n • f.coeff n ≠ 0)
    (hlt : ∀ m < n, m • f.coeff m = 0) :
    (derivative R f).orderTop = (n - 1 : ℤ) := by
  refine orderTop_eq_of_le (by rwa [mem_support, coeff_derivative_sub_one]) fun m hm ↦ ?_
  by_contra! h
  rw [mem_support, ← add_sub_cancel_right m 1, coeff_derivative_sub_one] at hm
  exact hm (hlt _ (by omega))

/-- If the order `r` of `f` times its leading coefficient is nonzero, then `f'` has order
`r - 1`. -/
theorem orderTop_derivative_eq_order_sub_one {f : LaurentSeries V}
    (h : f.order • f.leadingCoeff ≠ 0) :
    (derivative R f).orderTop = (f.order - 1 : ℤ) := by
  rw [leadingCoeff_eq] at h
  exact orderTop_derivative_eq_sub_one h fun m hm ↦ by rw [coeff_eq_zero_of_lt_order hm, smul_zero]

/-- A Laurent series has derivative zero exactly when `n • f.coeff n = 0` for every exponent
`n`. -/
theorem derivative_eq_zero_iff {f : LaurentSeries V} :
    derivative R f = 0 ↔ ∀ n : ℤ, n • f.coeff n = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · rw [← coeff_derivative_sub_one (R := R), h, coeff_zero]
  · ext n
    rw [coeff_derivative, h, coeff_zero]

/-- Without additive torsion, a Laurent series has derivative zero exactly when it is
constant. -/
theorem derivative_eq_zero_iff_eq_single [IsAddTorsionFree V] {f : LaurentSeries V} :
    derivative R f = 0 ↔ f = single 0 (f.coeff 0) := by
  rw [derivative_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h n ↦ ?_⟩
  · ext n
    by_cases hn : n = 0
    · simp [hn]
    · simpa [coeff_single_of_ne hn, hn] using h n
  · rw [h]
    by_cases hn : n = 0 <;> simp [hn]

end Module

/-- If `f ≠ 0` has order `r` and `r` is nonzero in a ring `R` without zero divisors, for instance
a field in which `r` is nonzero, then `f'` has order `r - 1`. -/
theorem orderTop_derivative_eq_order_sub_one_of_cast_ne_zero {R : Type*} [Ring R]
    [NoZeroDivisors R] {f : R⸨X⸩} (hf : f ≠ 0) (h : (f.order : R) ≠ 0) :
    (derivative R f).orderTop = (f.order - 1 : ℤ) :=
  orderTop_derivative_eq_order_sub_one <| by
    rw [zsmul_eq_mul]
    exact mul_ne_zero h (leadingCoeff_ne_zero.mpr hf)

/-- **The kernel of the derivative.** Over a ring without additive torsion, for instance a field
of characteristic zero, the Laurent series with derivative zero are exactly the constants. -/
theorem derivative_eq_zero_iff_exists_C {R : Type*} [Ring R] [IsAddTorsionFree R] {f : R⸨X⸩} :
    derivative R f = 0 ↔ ∃ c : R, C c = f := by
  rw [derivative_eq_zero_iff_eq_single]
  refine ⟨fun h ↦ ⟨_, by simpa only [C_apply] using h.symm⟩, ?_⟩
  rintro ⟨c, rfl⟩
  simp

section Field

variable {K : Type*} [Field K]

/-- **The inverse rule**: `(f⁻¹)' = -(f⁻¹ ^ 2 * f')`. -/
theorem derivative_inv (f : K⸨X⸩) :
    derivative K f⁻¹ = -(f⁻¹ ^ 2 * derivative K f) := by
  simpa using (TauCeti.laurentSeriesDerivation K).leibniz_inv f

/-- **The quotient rule**: `(f / g)' = (f' * g - f * g') / g ^ 2`. -/
theorem derivative_div (f g : K⸨X⸩) :
    derivative K (f / g) = (derivative K f * g - f * derivative K g) / g ^ 2 := by
  have h := (TauCeti.laurentSeriesDerivation K).leibniz_div f g
  simp only [TauCeti.laurentSeriesDerivation_apply, smul_eq_mul] at h
  rw [h]
  ring

/-- If `f` vanishes to order at least `m`, then `f'` vanishes to order at least `m - 1`. -/
theorem valuation_derivative_le {m : ℤ} {f : K⸨X⸩} (hf : Valued.v f ≤ WithZero.exp (-m)) :
    Valued.v (derivative K f) ≤ WithZero.exp (-(m - 1)) := by
  rw [valuation_le_iff_coeff_lt_eq_zero] at hf ⊢
  intro n hn
  rw [coeff_derivative, hf _ (by omega), smul_zero]

/-- The derivative of Laurent series is continuous for the valuation topology. -/
theorem continuous_derivative : Continuous (derivative K : K⸨X⸩ → K⸨X⸩) := by
  refine continuous_of_continuousAt_zero (derivative K) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)).symm⟩
  -- Series of valuation below `exp (k - 2)` have derivatives of valuation below `exp k`.
  have hU : {x : K⸨X⸩ | Valued.v x < Valued.v (single (2 - k) (1 : K))} ∈ 𝓝 0 :=
    Valued.mem_nhds_zero.mpr ⟨Units.mk0 (Valued.v.restrict (single (2 - k) (1 : K))) (by simp),
      fun _ hx ↦ Valued.v.restrict_lt_iff.mp hx⟩
  refine Filter.mem_map.mpr ?_
  filter_upwards [hU] with x hx
  rw [valuation_single_zpow] at hx
  apply hγ
  rw [Set.mem_ofPred_eq, Valued.v.restrict_lt_iff_lt_embedding]
  refine (valuation_derivative_le hx.le).trans_lt ?_
  rw [hk, WithZero.exp_lt_exp]
  omega

end Field

end LaurentSeries
