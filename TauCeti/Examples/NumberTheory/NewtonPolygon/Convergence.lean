/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Convergence
public import TauCeti.NumberTheory.Padics.Complex.Valuation
public import TauCeti.NumberTheory.Padics.LogGauge
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Explicit radii and pointwise convergence of `p`-adic power series

Concrete instances comparing the intrinsic coefficient radius `PowerSeries.radius` with the
pointwise convergence radius `PowerSeries.convergenceRadius` over `ℚ_[p]` and `ℂ_[p]`, with respect
to `TauCeti.padicRealValuation p` (normalised by `v(p) = 1`):

* **Strict inequality in a discretely normed base field.** The power series
  `halfSlopeSeries p = ∑_{n ≥ 0} p ^ ⌈n / 2⌉ X ^ n ∈ ℚ_[p]⟦X⟧` has coefficient valuations
  `⌈n / 2⌉`, whose lower linear growth `liminf_{n → ∞} ⌈n / 2⌉ / n` equals `1 / 2`. Its intrinsic
  radius is therefore `√p`, and over the densely normed completion `ℂ_[p]` its pointwise
  convergence radius also equals `√p` (converging on `{x : ℂ_[p] | ‖x‖ < √p}`, including points of
  norm strictly between `1` and `√p`, and diverging on the boundary sphere `‖x‖ = √p`). Over
  `ℚ_[p]`, however, every nonzero norm is an integer power of `p`, so the pointwise convergence
  radius rounds down to `p ^ ⌊1 / 2⌋ = 1 < √p`: the series converges at `x ∈ ℚ_[p]` if and only if
  `‖x‖ ≤ 1`.
* **Polynomials with finite root norms still have infinite radius.** The quadratic polynomial
  `1 - p X ^ 2 ∈ ℚ_[p][X]` has roots in `ℂ_[p]`, every one of which has finite positive norm `√p`;
  nevertheless, viewed in `ℚ_[p]⟦X⟧`, its intrinsic radius and its pointwise convergence radii in
  both `ℚ_[p]` and `ℂ_[p]` are `⊤`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open Filter LinearGrowth _root_.PowerSeries TauCeti
open scoped NNReal ENNReal

namespace TauCeti.NewtonPolygonConvergenceExample

section HalfSlopeSeries

private theorem ceil_two_mul_div_two (k : ℕ) : ⌈((2 * k : ℕ) : ℚ) / 2⌉₊ = k := by
  have h : (((2 * k : ℕ) : ℚ) / 2) = (k : ℚ) := by
    push_cast
    exact mul_div_cancel_left₀ (k : ℚ) two_ne_zero
  rw [h, Nat.ceil_natCast]

variable (p : ℕ) [Fact p.Prime]

/-- The power series `∑_{n ≥ 0} p ^ ⌈n / 2⌉ X ^ n` over `ℚ_[p]`. -/
noncomputable def halfSlopeSeries : ℚ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦ (p : ℚ_[p]) ^ ⌈(n : ℚ) / 2⌉₊

/-- The `n`-th coefficient of `halfSlopeSeries p` is `p ^ ⌈n / 2⌉`. -/
@[simp]
theorem coeff_halfSlopeSeries (n : ℕ) :
    PowerSeries.coeff n (halfSlopeSeries p) = (p : ℚ_[p]) ^ ⌈(n : ℚ) / 2⌉₊ :=
  PowerSeries.coeff_mk n _

variable {p}

/-- Under `padicRealValuation p`, the `n`-th coefficient of `halfSlopeSeries p` has valuation
`⌈n / 2⌉`. -/
theorem padicRealValuation_coeff_halfSlopeSeries (n : ℕ) :
    padicRealValuation p (PowerSeries.coeff n (halfSlopeSeries p)) =
      ((⌈(n : ℚ) / 2⌉₊ : ℝ) : WithTop ℝ) := by
  rw [coeff_halfSlopeSeries, (padicRealValuation p).map_pow, padicRealValuation_p, nsmul_one]
  exact (WithTop.coe_natCast _).symm

/-- The lower linear growth `liminf_{n → ∞} v(aₙ) / n` of `halfSlopeSeries p` equals `1 / 2`. -/
theorem linearGrowthInf_halfSlopeSeries :
    (linearGrowthInf fun n ↦
      (padicRealValuation p (PowerSeries.coeff n (halfSlopeSeries p))).toEReal) =
      ((1 / 2 : ℝ) : EReal) := by
  refine le_antisymm ?_ ?_
  · refine Frequently.linearGrowthInf_le (frequently_atTop.mpr fun N ↦ ⟨2 * N, by omega, ?_⟩)
    rw [padicRealValuation_coeff_halfSlopeSeries, ceil_two_mul_div_two, WithTop.toEReal_coe,
      ← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    push_cast
    linarith
  · refine le_linearGrowthInf_of_affine_le (c := 0) (σ := 1 / 2) fun n ↦ ?_
    rw [padicRealValuation_coeff_halfSlopeSeries, WithTop.coe_le_coe, zero_add]
    have hq : (((n : ℚ) / 2 : ℚ) : ℝ) ≤ (⌈(n : ℚ) / 2⌉₊ : ℝ) := by
      exact_mod_cast Nat.le_ceil ((n : ℚ) / 2)
    push_cast at hq
    linarith

/-- The intrinsic coefficient radius of `∑_{n ≥ 0} p ^ ⌈n / 2⌉ X ^ n` is `√p`. -/
theorem radius_halfSlopeSeries :
    (halfSlopeSeries p).radius = ENNReal.ofReal (Real.sqrt p) := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  rw [(halfSlopeSeries p).radius_eq_ofReal_rpow (padicRealValuation p) hp1
    (fun _ hx ↦ norm_eq_rpow_neg_padicRealValuation hx) linearGrowthInf_halfSlopeSeries,
    Real.sqrt_eq_rpow]

/-- Over `ℚ_[p]`, the pointwise convergence radius of `∑_{n ≥ 0} p ^ ⌈n / 2⌉ X ^ n` is `1`. -/
theorem convergenceRadius_padic_halfSlopeSeries :
    (halfSlopeSeries p).convergenceRadius ℚ_[p] = 1 := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hdisc : ∀ y : ℚ_[p], ‖y‖ ≠ 0 → ∃ m : ℤ, ‖y‖ = (p : ℝ) ^ m := fun y hy ↦
    ⟨-y.valuation, Padic.norm_eq_zpow_neg_valuation (norm_ne_zero_iff.mp hy)⟩
  have hfl0 : ⌊(1 / 2 : ℝ)⌋ = 0 := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  have hfloor : (⌊(1 / 2 : ℝ)⌋ : ℝ) < 1 / 2 := by
    rw [hfl0]
    norm_num
  have hatt : ∃ x : ℚ_[p], ‖x‖ = (p : ℝ) ^ ⌊(1 / 2 : ℝ)⌋ := ⟨1, by rw [hfl0, zpow_zero, norm_one]⟩
  have heq := (halfSlopeSeries p).convergenceRadius_eq_ofReal_zpow_floor
    (padicRealValuation p) hp1 (fun _ hx ↦ norm_eq_rpow_neg_padicRealValuation hx) ℚ_[p]
    hdisc linearGrowthInf_halfSlopeSeries hfloor hatt
  rwa [hfl0, zpow_zero, ENNReal.ofReal_one] at heq

/-- Over `ℚ_[p]`, the pointwise convergence radius of `∑_{n ≥ 0} p ^ ⌈n / 2⌉ X ^ n` is strictly
smaller than its intrinsic radius `√p`. -/
theorem convergenceRadius_padic_lt_radius_halfSlopeSeries :
    (halfSlopeSeries p).convergenceRadius ℚ_[p] < (halfSlopeSeries p).radius := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hsqrt : (1 : ℝ) < Real.sqrt p := by rwa [Real.lt_sqrt zero_le_one, one_pow]
  rw [convergenceRadius_padic_halfSlopeSeries, radius_halfSlopeSeries, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hsqrt) |>.mpr hsqrt

/-- Over `ℚ_[p]`, `∑_{n ≥ 0} p ^ ⌈n / 2⌉ x ^ n` converges if and only if `‖x‖ ≤ 1`. -/
theorem summable_halfSlopeSeries_padic_iff {x : ℚ_[p]} :
    (Summable fun n ↦ PowerSeries.coeff n (halfSlopeSeries p) • x ^ n) ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro hs
    have hle : ‖x‖ₑ ≤ 1 :=
      (le_convergenceRadius_of_summable hs).trans_eq convergenceRadius_padic_halfSlopeSeries
    simpa [← ofReal_norm] using hle
  · intro hx
    have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
    have hsqrt : (1 : ℝ) < Real.sqrt p := by
      rwa [Real.lt_sqrt zero_le_one, one_pow]
    have hres : (halfSlopeSeries p).IsRestricted (1 : ℝ) := by
      refine isRestricted_of_lt_radius ?_
      rw [radius_halfSlopeSeries, Real.eNorm_eq_ofReal zero_le_one]
      exact ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hsqrt) |>.mpr hsqrt
    exact hres.summable_smul_pow (by simpa using hx)

/-- Over `ℂ_[p]`, the pointwise convergence radius of `∑_{n ≥ 0} p ^ ⌈n / 2⌉ X ^ n` equals its
intrinsic radius `√p`. -/
theorem convergenceRadius_padicComplex_halfSlopeSeries :
    (halfSlopeSeries p).convergenceRadius ℂ_[p] = ENNReal.ofReal (Real.sqrt p) := by
  rw [(halfSlopeSeries p).convergenceRadius_eq_radius ℂ_[p], radius_halfSlopeSeries]

/-- At the boundary radius `√p`, `halfSlopeSeries p` is not restricted, because its even-degree
terms satisfy `‖p ^ k‖ * (√p) ^ (2 k) = 1`. -/
theorem not_isRestricted_halfSlopeSeries_sqrt :
    ¬(halfSlopeSeries p).IsRestricted (Real.sqrt p) := by
  intro hres
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rw [_root_.PowerSeries.isRestricted_iff'] at hres
  have heven : Tendsto (fun k : ℕ ↦ ‖PowerSeries.coeff (2 * k) (halfSlopeSeries p)‖ *
      (Real.sqrt p) ^ (2 * k)) atTop (nhds 0) :=
    hres.comp (tendsto_id.const_mul_atTop' two_pos)
  have hconst : (fun k : ℕ ↦ ‖PowerSeries.coeff (2 * k) (halfSlopeSeries p)‖ *
      (Real.sqrt p) ^ (2 * k)) = fun _ ↦ (1 : ℝ) := by
    ext k
    rw [coeff_halfSlopeSeries, ceil_two_mul_div_two, norm_pow, Padic.norm_p,
      pow_mul, Real.sq_sqrt hp0.le, inv_pow, inv_mul_cancel₀ (pow_ne_zero k hp0.ne')]
  rw [hconst] at heven
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds heven)

/-- Over `ℂ_[p]`, `∑_{n ≥ 0} p ^ ⌈n / 2⌉ x ^ n` converges if and only if `‖x‖ < √p`. -/
theorem summable_halfSlopeSeries_padicComplex_iff {x : ℂ_[p]} :
    (Summable fun n ↦ PowerSeries.coeff n (halfSlopeSeries p) • x ^ n) ↔ ‖x‖ < Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  constructor
  · intro hs
    have hle : ‖x‖ ≤ Real.sqrt p := by
      have h := (le_convergenceRadius_of_summable hs).trans_eq
        convergenceRadius_padicComplex_halfSlopeSeries
      rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg p)] at h
      exact h
    refine hle.lt_of_ne fun heq ↦ not_isRestricted_halfSlopeSeries_sqrt (p := p) ?_
    exact isRestricted_of_summable_of_norm_eq hs heq
  · intro hx
    refine summable_of_lt_convergenceRadius ?_
    rw [convergenceRadius_padicComplex_halfSlopeSeries, ← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff (Real.sqrt_pos.mpr hp0) |>.mpr hx

/-- There exist points in `ℂ_[p]` of norm strictly greater than `1` where `halfSlopeSeries p`
converges (for instance, any element of norm `p ^ (1 / 3)`). -/
theorem exists_one_lt_norm_and_summable_halfSlopeSeries :
    ∃ x : ℂ_[p], 1 < ‖x‖ ∧
      Summable fun n ↦ PowerSeries.coeff n (halfSlopeSeries p) • x ^ n := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  obtain ⟨x, hx⟩ := PadicComplex.exists_norm_eq_rpow (p := p) (1 / 3 : ℚ)
  refine ⟨x, ?_, summable_halfSlopeSeries_padicComplex_iff.mpr ?_⟩
  · rw [hx]
    exact Real.one_lt_rpow hp1 (by norm_num)
  · rw [hx, Real.sqrt_eq_rpow]
    exact Real.rpow_lt_rpow_left_iff hp1 |>.mpr (by norm_num)

end HalfSlopeSeries

section PolynomialFiniteRootNorm

variable {p : ℕ} [Fact p.Prime]

/-- Every root of `1 - p X ^ 2 ∈ ℚ_[p][X]` in `ℂ_[p]` has finite positive norm `√p`. -/
theorem norm_eq_sqrt_of_aeval_one_sub_C_mul_X_sq_eq_zero {α : ℂ_[p]}
    (hα : Polynomial.aeval α (1 - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ 2) = 0) :
    ‖α‖ = Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have h1 : 1 - (p : ℂ_[p]) * α ^ 2 = 0 := by simpa using hα
  have hmul : ‖(p : ℂ_[p]) * α ^ 2‖ = 1 := by rw [← sub_eq_zero.mp h1, norm_one]
  rw [norm_mul, PadicComplex.norm_p, norm_pow] at hmul
  have hsq : ‖α‖ ^ 2 = (p : ℝ) := by
    calc ‖α‖ ^ 2 = (p : ℝ) * ((p : ℝ)⁻¹ * ‖α‖ ^ 2) := by
          rw [← mul_assoc, mul_inv_cancel₀ hp0.ne', one_mul]
      _ = (p : ℝ) := by rw [hmul, mul_one]
  rw [← hsq, Real.sqrt_sq (norm_nonneg α)]

/-- The quadratic polynomial `1 - p X ^ 2 ∈ ℚ_[p][X]` has a root in `ℂ_[p]` of norm `√p`. -/
theorem exists_aeval_one_sub_C_mul_X_sq_eq_zero :
    ∃ α : ℂ_[p],
      Polynomial.aeval α (1 - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ 2) = 0 ∧
        ‖α‖ = Real.sqrt p := by
  have hp_ne : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p])⁻¹ two_pos
  have hα_root : Polynomial.aeval α (1 - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ 2) = 0 := by
    simp [hα, mul_inv_cancel₀ hp_ne]
  exact ⟨α, hα_root, norm_eq_sqrt_of_aeval_one_sub_C_mul_X_sq_eq_zero hα_root⟩

-- Despite having roots of finite norm `√p`, `1 - p X ^ 2` has infinite intrinsic and pointwise
-- convergence radii over both `ℚ_[p]` and `ℂ_[p]`.
example :
    (((1 - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ 2 : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧)).radius =
      ⊤ :=
  PowerSeries.radius_coe _

example :
    (((1 - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ 2 : Polynomial ℚ_[p]) :
      ℚ_[p]⟦X⟧)).convergenceRadius ℚ_[p] = ⊤ :=
  PowerSeries.convergenceRadius_coe _ _

example :
    (((1 - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ 2 : Polynomial ℚ_[p]) :
      ℚ_[p]⟦X⟧)).convergenceRadius ℂ_[p] = ⊤ :=
  PowerSeries.convergenceRadius_coe _ _

end PolynomialFiniteRootNorm

end TauCeti.NewtonPolygonConvergenceExample
