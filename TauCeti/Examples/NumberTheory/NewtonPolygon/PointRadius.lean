/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Radius
public import TauCeti.NumberTheory.Padics.Complex.Valuation
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.PointRadius
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Explicit radii and point-convergence radii over `ℚ_[p]` and `ℂ_[p]`

Concrete `p`-adic instances comparing the intrinsic convergence radius `PowerSeries.radius`, the
Newton polygon, and the extension-dependent point-convergence radius `PowerSeries.pointRadius`:

* The series `ceilHalfPowSeries p = ∑ₙ p ^ ⌈n / 2⌉ Xⁿ` over `ℚ_[p]` has Newton polygon equal to the
  ray `n ↦ n / 2` with respect to `TauCeti.padicRealValuation p`, and intrinsic radius
  `(ceilHalfPowSeries p).radius = ENNReal.ofReal √p`.
* At the boundary radius `√p`, the weighted coefficient norms `‖p ^ ⌈n / 2⌉‖ (√p) ^ n` are bounded
  by `1` (`HasGaussNorm`) and equal `1` at every even index, so `ceilHalfPowSeries p` is *not*
  restricted at `√p` and diverges at every element of `ℂ_[p]` of norm `√p`.
* Because the nonzero norms on `ℚ_[p]` form the discrete group `{p ^ m | m : ℤ}` and `1 < √p < p`,
  the point-convergence radius drops strictly in `ℚ_[p]`:
  `(ceilHalfPowSeries p).pointRadius ℚ_[p] = 1 < (ceilHalfPowSeries p).radius`.
* Passing to `ℂ_[p]`, whose positive norms are dense in `(0, ∞)`, recovers the intrinsic radius:
  `(ceilHalfPowSeries p).pointRadius ℂ_[p] = ENNReal.ofReal √p`.
* By contrast, for a polynomial such as `1 - p X ^ 2 : ℚ_[p][X]`, every root in `ℂ_[p]` has
  finite norm `√p`, yet both its intrinsic radius and its point-convergence radii in `ℚ_[p]` and
  `ℂ_[p]` are `⊤`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV, §4.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 6, §1.
-/

public section

open Filter Polynomial TauCeti
open scoped NNReal ENNReal PowerSeries Topology

namespace TauCeti.NewtonPolygonPointRadiusExample

section CeilHalfPowSeries

/-- The `p`-adic power series `∑ₙ p ^ ⌈n / 2⌉ Xⁿ` over `ℚ_[p]`, whose intrinsic convergence radius
is `√p` while its point-convergence radius in `ℚ_[p]` is `1`. -/
noncomputable def ceilHalfPowSeries (p : ℕ) [Fact p.Prime] : ℚ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦ (p : ℚ_[p]) ^ ⌈(n : ℚ) / 2⌉₊

/-- The `n`-th coefficient of `ceilHalfPowSeries p` is `p ^ ⌈n / 2⌉`. -/
@[simp]
theorem coeff_ceilHalfPowSeries (p : ℕ) [Fact p.Prime] (n : ℕ) :
    PowerSeries.coeff n (ceilHalfPowSeries p) = (p : ℚ_[p]) ^ ⌈(n : ℚ) / 2⌉₊ :=
  PowerSeries.coeff_mk n _

private theorem ceil_div_two_eq (n : ℕ) : ⌈(n : ℚ) / 2⌉₊ = (n + 1) / 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hk : ((2 * k : ℕ) : ℚ) / 2 = (k : ℚ) := by push_cast; ring
    rw [hk, Nat.ceil_natCast]
    omega
  · have hceil : ⌈((2 * k + 1 : ℕ) : ℚ) / 2⌉₊ = k + 1 :=
      (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [hceil]
    omega

private theorem le_two_mul_ceil_div_two (n : ℕ) : n ≤ 2 * ⌈(n : ℚ) / 2⌉₊ := by
  rw [ceil_div_two_eq]
  omega

private theorem ceil_two_mul_div_two (k : ℕ) : ⌈((2 * k : ℕ) : ℚ) / 2⌉₊ = k := by
  rw [ceil_div_two_eq]
  omega

variable {p : ℕ} [Fact p.Prime]

private theorem norm_coeff_mul_sqrt_pow_le_one (n : ℕ) :
    ‖PowerSeries.coeff n (ceilHalfPowSeries p)‖ * √(p : ℝ) ^ n ≤ 1 := by
  set m := ⌈(n : ℚ) / 2⌉₊
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le
  have hsqrt1 : 1 ≤ √(p : ℝ) := Real.one_le_sqrt.mpr hp1
  have hpow : √(p : ℝ) ^ n ≤ (p : ℝ) ^ m := by
    calc √(p : ℝ) ^ n
        ≤ √(p : ℝ) ^ (2 * m) := pow_le_pow_right₀ hsqrt1 (le_two_mul_ceil_div_two n)
      _ = (√(p : ℝ) ^ 2) ^ m := pow_mul √(p : ℝ) 2 m
      _ = (p : ℝ) ^ m := by rw [Real.sq_sqrt hp0.le]
  calc ‖PowerSeries.coeff n (ceilHalfPowSeries p)‖ * √(p : ℝ) ^ n
      = ((p : ℝ)⁻¹) ^ m * √(p : ℝ) ^ n := by
        rw [coeff_ceilHalfPowSeries, norm_pow, Padic.norm_p]
    _ ≤ ((p : ℝ)⁻¹) ^ m * (p : ℝ) ^ m := by gcongr
    _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero m hp0.ne')]

private theorem norm_coeff_two_mul_mul_sqrt_pow (k : ℕ) :
    ‖PowerSeries.coeff (2 * k) (ceilHalfPowSeries p)‖ * √(p : ℝ) ^ (2 * k) = 1 := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rw [coeff_ceilHalfPowSeries, ceil_two_mul_div_two, norm_pow, Padic.norm_p,
    pow_mul √(p : ℝ) 2 k, Real.sq_sqrt hp0.le, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero k hp0.ne')

/-- At the boundary radius `√p`, the weighted coefficient norms of `ceilHalfPowSeries p` are
bounded (by `1`). -/
theorem hasGaussNorm_ceilHalfPowSeries_sqrt :
    (ceilHalfPowSeries p).HasGaussNorm norm √(p : ℝ) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact norm_coeff_mul_sqrt_pow_le_one n⟩

/-- `ceilHalfPowSeries p` is *not* restricted at its boundary radius `√p`, since at every even
index `2 * k` the weighted coefficient norm equals `1`. -/
theorem not_isRestricted_ceilHalfPowSeries_sqrt :
    ¬(ceilHalfPowSeries p).IsRestricted √(p : ℝ) := by
  intro hf
  rw [PowerSeries.isRestricted_iff'] at hf
  have h2k : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b, fun a ha ↦ by omega⟩
  have hlim : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_coeff_two_mul_mul_sqrt_pow] using hf.comp h2k
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- There exists an element of `ℂ_[p]` of norm `√p` (for instance a square root of `p⁻¹`). -/
theorem exists_norm_eq_sqrt_padicComplex : ∃ x : ℂ_[p], ‖x‖ = √(p : ℝ) := by
  obtain ⟨x, hx⟩ := PadicComplex.addValuation_surjective (p := p) ((-1 / 2 : ℚ) : WithTop ℚ)
  refine ⟨x, ?_⟩
  rw [PadicComplex.addValuation_eq_coe_iff] at hx
  rw [hx, Real.sqrt_eq_rpow]
  congr 1
  norm_num

/-- At any boundary point `x : ℂ_[p]` of norm `√p`, `ceilHalfPowSeries p` diverges. -/
theorem not_summable_ceilHalfPowSeries_of_norm_eq_sqrt {x : ℂ_[p]} (hx : ‖x‖ = √(p : ℝ)) :
    ¬Summable fun n ↦ PowerSeries.coeff n (ceilHalfPowSeries p) • x ^ n :=
  fun hs ↦ not_isRestricted_ceilHalfPowSeries_sqrt
    (PowerSeries.isRestricted_of_summable_of_norm_eq hs hx)

/-- With respect to `padicRealValuation p`, the Newton polygon of `ceilHalfPowSeries p` is the
infinite ray `n ↦ n / 2` of slope `1 / 2`. -/
theorem newtonPolygon_ceilHalfPowSeries (n : ℕ) :
    (ceilHalfPowSeries p).newtonPolygon (padicRealValuation p) n =
      (((n : ℝ) / 2 : ℝ) : WithTop ℝ) := by
  set v := padicRealValuation p
  have hval (m : ℕ) : v (PowerSeries.coeff m (ceilHalfPowSeries p)) =
      ((⌈(m : ℚ) / 2⌉₊ : ℝ) : WithTop ℝ) := by
    rw [coeff_ceilHalfPowSeries, v.map_pow, padicRealValuation_p, nsmul_one, ← WithTop.coe_natCast]
  have hminor (m : ℕ) :
      ((0 + (1 / 2 : ℝ) * m : ℝ) : WithTop ℝ) ≤ v (PowerSeries.coeff m (ceilHalfPowSeries p)) := by
    rw [hval]
    refine WithTop.coe_le_coe.mpr ?_
    have hm : (m : ℝ) ≤ 2 * (⌈(m : ℚ) / 2⌉₊ : ℝ) := by exact_mod_cast le_two_mul_ceil_div_two m
    linarith
  have hadm : IsAdmissible fun m ↦ v (PowerSeries.coeff m (ceilHalfPowSeries p)) :=
    isAdmissible_iff.mpr ⟨0, 1 / 2, hminor⟩
  have hlo (m : ℕ) :
      (((m : ℝ) / 2 : ℝ) : WithTop ℝ) ≤ (ceilHalfPowSeries p).newtonPolygon v m := by
    simpa [div_eq_inv_mul] using
      PowerSeries.le_newtonPolygon (isConvexSeq_affine 0 (1 / 2)) hminor m
  refine le_antisymm ?_ (hlo n)
  have heven (k : ℕ) : (ceilHalfPowSeries p).newtonPolygon v (2 * k) = ((k : ℝ) : WithTop ℝ) := by
    refine le_antisymm ?_ ?_
    · have hle := PowerSeries.newtonPolygon_le hadm (2 * k)
      rwa [hval, ceil_two_mul_div_two] at hle
    · convert hlo (2 * k) using 2
      push_cast
      ring
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [heven]
    exact WithTop.coe_le_coe.mpr (by push_cast; linarith)
  · have htop : (ceilHalfPowSeries p).newtonPolygon v (2 * k + 1) ≠ ⊤ :=
      ((PowerSeries.newtonPolygon_le hadm (2 * k + 1)).trans_lt
        (by rw [hval]; exact WithTop.coe_lt_top _)).ne
    have hconv := (isConvexSeq_iff_two_mul_le.mp
      ((ceilHalfPowSeries p).isConvexSeq_newtonPolygon v)).2 (2 * k)
      (by rw [heven]; exact WithTop.coe_ne_top)
      (by rw [show 2 * k + 2 = 2 * (k + 1) by omega, heven]; exact WithTop.coe_ne_top)
    rw [heven, show 2 * k + 2 = 2 * (k + 1) by omega, heven, WithTop.untop₀_coe,
      WithTop.untop₀_coe] at hconv
    rw [← WithTop.coe_untop₀_of_ne_top htop, WithTop.coe_le_coe]
    push_cast at hconv ⊢
    linarith

/-- The intrinsic convergence radius of `ceilHalfPowSeries p` is `√p`. -/
theorem radius_ceilHalfPowSeries :
    (ceilHalfPowSeries p).radius = ENNReal.ofReal √(p : ℝ) := by
  let r : ℝ≥0 := ⟨√(p : ℝ), Real.sqrt_nonneg p⟩
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg p)]
  refine le_antisymm ?_ (PowerSeries.le_radius_of_bound 1 norm_coeff_mul_sqrt_pow_le_one)
  by_contra! hlt
  have hres : (ceilHalfPowSeries p).IsRestricted √(p : ℝ) := by
    refine PowerSeries.isRestricted_of_lt_radius ?_
    simpa [r, eNorm_eq_nnNorm, Real.nnNorm_of_nonneg (Real.sqrt_nonneg p)] using hlt
  exact not_isRestricted_ceilHalfPowSeries_sqrt hres

/-- In `ℚ_[p]`, whose nonzero norms are integer powers of `p`, the point-convergence radius of
`ceilHalfPowSeries p` drops to `1`. -/
theorem pointRadius_ceilHalfPowSeries_padic :
    (ceilHalfPowSeries p).pointRadius ℚ_[p] = 1 := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  refine PowerSeries.pointRadius_eq_one_of_one_lt_radius_lt (b := (p : ℝ)) hp1
    (fun x hx ↦ ⟨-x.valuation, Padic.norm_eq_zpow_neg_valuation (norm_ne_zero_iff.mp hx)⟩) ?_ ?_
  · rw [radius_ceilHalfPowSeries, ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff (Real.sqrt_pos.mpr hp0)]
    exact Real.lt_sqrt_of_sq_lt (by linarith)
  · rw [radius_ceilHalfPowSeries, ENNReal.ofReal_lt_ofReal_iff hp0]
    exact (Real.sqrt_lt' hp0).mpr (by nlinarith)

/-- Over `ℚ_[p]`, the point-convergence radius of `ceilHalfPowSeries p` is strictly smaller than its
intrinsic radius `√p`. -/
theorem pointRadius_lt_radius_ceilHalfPowSeries_padic :
    (ceilHalfPowSeries p).pointRadius ℚ_[p] < (ceilHalfPowSeries p).radius := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  rw [pointRadius_ceilHalfPowSeries_padic, radius_ceilHalfPowSeries, ← ENNReal.ofReal_one,
    ENNReal.ofReal_lt_ofReal_iff (Real.sqrt_pos.mpr hp0)]
  exact Real.lt_sqrt_of_sq_lt (by linarith)

/-- Over `ℂ_[p]`, whose positive norms are dense in `(0, ∞)`, the point-convergence radius of
`ceilHalfPowSeries p` equals its intrinsic radius `√p`. -/
theorem pointRadius_ceilHalfPowSeries_padicComplex :
    (ceilHalfPowSeries p).pointRadius ℂ_[p] = ENNReal.ofReal √(p : ℝ) := by
  simp [radius_ceilHalfPowSeries]

end CeilHalfPowSeries

section PolynomialInfiniteRadius

variable {p : ℕ} [Fact p.Prime]

/-- Every root in `ℂ_[p]` of the polynomial `1 - p X ^ 2 : ℚ_[p][X]` has finite norm `√p`. -/
theorem norm_eq_sqrt_of_aeval_one_sub_p_X_sq_eq_zero {x : ℂ_[p]}
    (hx : Polynomial.aeval x (1 - C (p : ℚ_[p]) * X ^ 2 : ℚ_[p][X]) = 0) :
    ‖x‖ = √(p : ℝ) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hmul : (p : ℂ_[p]) * x ^ 2 = 1 := by
    have hsub : 1 - (p : ℂ_[p]) * x ^ 2 = 0 := by
      simpa [map_sub, map_one, map_mul, map_pow, aeval_C, aeval_X] using hx
    exact (sub_eq_zero.mp hsub).symm
  have hsq : ‖x‖ ^ 2 = (p : ℝ) := by
    have hnorm := congrArg norm hmul
    rw [norm_mul, PadicComplex.norm_p, norm_pow, norm_one, inv_mul_eq_iff_eq_mul₀ hp0.ne',
      mul_one] at hnorm
    exact hnorm
  rw [← Real.sqrt_sq (norm_nonneg x), hsq]

/-- Although every root of `1 - p X ^ 2` in `ℂ_[p]` has finite norm `√p`, its intrinsic radius and
its point-convergence radii in both `ℚ_[p]` and `ℂ_[p]` are `⊤`. -/
theorem radius_and_pointRadius_one_sub_p_X_sq :
    ((1 - C (p : ℚ_[p]) * X ^ 2 : ℚ_[p][X]) : ℚ_[p]⟦X⟧).radius = ⊤ ∧
      ((1 - C (p : ℚ_[p]) * X ^ 2 : ℚ_[p][X]) : ℚ_[p]⟦X⟧).pointRadius ℚ_[p] = ⊤ ∧
      ((1 - C (p : ℚ_[p]) * X ^ 2 : ℚ_[p][X]) : ℚ_[p]⟦X⟧).pointRadius ℂ_[p] = ⊤ :=
  ⟨PowerSeries.radius_coe _, PowerSeries.pointRadius_coe _ _, PowerSeries.pointRadius_coe _ _⟩

end PolynomialInfiniteRadius

end TauCeti.NewtonPolygonPointRadiusExample
