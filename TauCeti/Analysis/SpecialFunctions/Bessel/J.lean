/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Power series and integral representations of the Bessel function `J_ν`

Mathlib defines the Bessel function of the first kind `Complex.besselJ ν z` as
`(z / 2) ^ ν * ₀F₁(; ν + 1; -(z / 2) ^ 2)`, where `₀F₁` is the regularized hypergeometric function
`Complex.regularizedHGFun 0 {ν + 1}`. This file develops its everywhere-convergent power series,
its Schwarz reflection symmetry and real-line values, Bessel's circle and half-period integrals for
integer orders, the resulting uniform bounds on horizontal strips and the real axis, and Poisson's
integral representation for complex orders with `Re ν > -1 / 2`.

Because Mathlib's `Complex.Gamma` vanishes at nonpositive integers, the power series
`∑ⱼ (-1) ^ j * (z / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))` converges to `Complex.besselJ ν z` for
every `ν, z : ℂ` without exception, including at `z = 0`. Integrating the exponential series of
`e^{i z cos θ}` termwise against Fourier characters on `[-π, π]` yields the Hansen–Bessel circle
integrals and Bessel's integral `J_n(z) = π⁻¹ ∫₀^π cos(z sin θ - n θ) dθ` for all integer orders
`n : ℤ`, specialized at `n = 0` to `J₀(z) = (2π)⁻¹ ∫₀^{2π} e^{i z cos θ} dθ`. Integrating against
the symmetric Beta weight `(1 - t²) ^ (ν - 1 / 2)` on `[-1, 1]` and substituting `t = -cos θ`
gives Poisson's integral for `Re ν > -1 / 2`.

## Main declarations

* `Complex.hasSum_besselJ`, `Complex.summable_norm_besselJ`, `Complex.besselJ_eq_tsum` — the power
  series `∑ⱼ (-1) ^ j * (z / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))` converges absolutely to
  `besselJ ν z` for every `ν, z : ℂ` (DLMF 10.2.2).
* `Complex.hasSum_besselJ_natCast`, `Complex.hasSum_besselJ_zero_left`,
  `Complex.analyticAt_besselJ_natCast`, `Complex.analyticAt_besselJ_zero_left` — the factorial
  power series and `@[fun_prop]` analyticity bridges for natural orders `n : ℕ` and order `0`.
* `Complex.tendsto_cpow_neg_mul_besselJ_nhdsNE_zero` — `(z / 2) ^ (-ν) J_ν(z) → 1 / Γ(ν + 1)` as
  `z → 0` through `ℂ \ {0}` (DLMF 10.7.3).
* `Complex.besselJ_conj`, `Complex.besselJ_int_conj` — Schwarz reflection
  `J_{conj ν}(conj z) = conj (J_ν(z))` away from the negative real ray `arg z = π`, and for all
  `z : ℂ` at integer orders (DLMF 10.11.9).
* `Complex.besselJ_int_ofReal_im`, `Complex.besselJ_ofReal_im_of_nonneg` — real-valuedness on `ℝ`
  for integer orders and on `[0, ∞)` for real orders.
* `Complex.integral_exp_I_mul_cos_mul_exp`, `Complex.integral_exp_I_mul_sin_sub_int_mul` — the
  circle integrals `∫_{-π}^π e^{i z cos θ} e^{i n θ} dθ = 2π i^n J_n(z)` and
  `∫_{-π}^π e^{i (z sin θ - n θ)} dθ = 2π J_n(z)` for `n : ℤ` and `z : ℂ`, together with their
  shifts to `[a, a + 2π]`.
* `Complex.integral_cos_mul_sin_sub_int_mul`, `Complex.integral_exp_I_mul_cos_mul_cos` — Bessel's
  integrals on `[0, π]` for `n : ℤ` and `z : ℂ` (DLMF 10.9.2).
* `Complex.besselJ_zero_eq_integral_exp_I_mul_cos`, `Complex.integral_cos_mul_cos_zero_pi`,
  `Complex.integral_cos_mul_sin_zero_pi` — the order-zero Bessel integrals on `[0, 2π]` and
  `[0, π]` (DLMF 10.9.1).
* `Complex.norm_besselJ_int_le_exp_abs_im`, `Complex.norm_besselJ_int_ofReal_le_one` — the bounds
  `‖J_n(z)‖ ≤ e^{|Im z|}` and `‖J_n(x)‖ ≤ 1` for `n : ℤ` (DLMF 10.14.4, 10.14.1).
* `Complex.integral_exp_I_mul_cos_mul_sin_cpow`,
  `Complex.besselJ_eq_integral_cos_mul_cos_mul_sin_cpow` — Poisson's integral representations on
  `[-1, 1]` and `[0, π]` for `Re ν > -1 / 2` and `z : ℂ` (DLMF 10.9.4).
* `Real.integral_cos_mul_sin_sub_int_mul`, `Real.integral_cos_mul_cos_zero_pi`,
  `Real.integral_cos_mul_sin_zero_pi` — real-valued trigonometric integrals for `x : ℝ`.

## References

* *NIST Digital Library of Mathematical Functions*, [§10.2(ii)](https://dlmf.nist.gov/10.2.ii),
  [§10.7(i)](https://dlmf.nist.gov/10.7.i), [§10.9(i)](https://dlmf.nist.gov/10.9.i),
  [§10.11](https://dlmf.nist.gov/10.11), and [§10.14](https://dlmf.nist.gov/10.14).
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §§2.1–2.2, §3.3.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ComplexConjugate Nat Real Topology

namespace Complex

/-! ### Power series and behavior near zero -/

/-- `J_0(0) = 1`. -/
@[simp]
theorem besselJ_zero_zero : besselJ 0 0 = 1 := by
  simp [besselJ_zero]

/-- `J_n` is analytic on `ℂ` for every natural order `n : ℕ`. -/
@[fun_prop]
theorem analyticAt_besselJ_natCast (n : ℕ) (z : ℂ) : AnalyticAt ℂ (besselJ n) z := by
  simpa using analyticAt_besselJ_int (n : ℤ) z

/-- `J_0` is analytic on `ℂ`. -/
@[fun_prop]
theorem analyticAt_besselJ_zero_left (z : ℂ) : AnalyticAt ℂ (besselJ 0) z := by
  simpa using analyticAt_besselJ_int 0 z

/-- **Power series of `J_ν(z)`** (DLMF 10.2.2): for every complex order `ν` and argument `z`,
`besselJ ν z = ∑ⱼ (-1) ^ j * (z / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))`. At `z = 0` with `ν ≠ 0`,
any term whose exponent `2 j + ν` vanishes has `j ≥ 1` and `j + ν + 1 = 1 - j ≤ 0`, where
`Complex.Gamma` vanishes. -/
theorem hasSum_besselJ (ν z : ℂ) :
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (z / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1)))
      (besselJ ν z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [besselJ_zero]
    split_ifs with hν
    · subst hν
      convert hasSum_ite_eq 0 (1 : ℂ) using 1
      ext j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · simp [hj.ne']
    · convert hasSum_zero with j
      rw [zero_div]
      by_cases h : (2 : ℂ) * j + ν = 0
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact absurd (by simpa using h) hν
        · have harg : (j : ℂ) + ν + 1 = -((j - 1 : ℕ) : ℂ) := by
            have hj1 : ((j - 1 : ℕ) : ℂ) = (j : ℂ) - 1 := by
              rw [Nat.cast_sub (Nat.one_le_of_lt hj), Nat.cast_one]
            rw [hj1]
            linear_combination h
          rw [harg, Gamma_neg_nat_eq_zero, mul_zero, div_zero]
      · rw [zero_cpow h, mul_zero, zero_div]
  · have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
    rw [besselJ]
    convert (hasSum_regularizedHGFun (a := 0) (b := {ν + 1}) (by simp) (-(z / 2) ^ 2)).mul_left
      ((z / 2) ^ ν) using 2 with j
    have hexp : (2 : ℂ) * j + ν = ν + ((2 * j : ℕ) : ℂ) := by push_cast; ring
    have hadd : (j : ℂ) + ν + 1 = ν + 1 + j := by ring
    rw [hexp, cpow_add _ _ hz2, cpow_natCast, pow_mul, regularizedHGFunCoeff_zero_singleton, hadd,
      neg_eq_neg_one_mul ((z / 2) ^ 2), mul_pow]
    ring

/-- The power series of `besselJ ν z` converges absolutely at every `ν, z : ℂ`. -/
theorem summable_norm_besselJ (ν z : ℂ) :
    Summable fun j : ℕ =>
      ‖(-1 : ℂ) ^ j * (z / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1))‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    have hj0 : j ≠ 0 := Finset.notMem_singleton.mp hj
    rw [zero_div]
    by_cases h : (2 : ℂ) * j + ν = 0
    · have harg : (j : ℂ) + ν + 1 = -((j - 1 : ℕ) : ℂ) := by
        have hj1 : ((j - 1 : ℕ) : ℂ) = (j : ℂ) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj0), Nat.cast_one]
        rw [hj1]
        linear_combination h
      rw [harg, Gamma_neg_nat_eq_zero, mul_zero, div_zero, norm_zero]
    · rw [zero_cpow h, mul_zero, zero_div, norm_zero]
  · have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
    convert (summable_norm_regularizedHGFun (a := 0) (b := {ν + 1}) (by simp)
      (-(z / 2) ^ 2)).mul_left ‖(z / 2) ^ ν‖ using 2 with j
    rw [← norm_mul]
    congr 1
    have hexp : (2 : ℂ) * j + ν = ν + ((2 * j : ℕ) : ℂ) := by push_cast; ring
    have hadd : (j : ℂ) + ν + 1 = ν + 1 + j := by ring
    rw [hexp, cpow_add _ _ hz2, cpow_natCast, pow_mul, regularizedHGFunCoeff_zero_singleton, hadd,
      neg_eq_neg_one_mul ((z / 2) ^ 2), mul_pow]
    ring

/-- `besselJ ν z` as a `tsum` over `ℕ`, valid for every `ν, z : ℂ`. -/
theorem besselJ_eq_tsum (ν z : ℂ) :
    besselJ ν z =
      ∑' j : ℕ, (-1 : ℂ) ^ j * (z / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1)) :=
  (hasSum_besselJ ν z).tsum_eq.symm

/-- For a natural order `n`, `J_n(z) = ∑ⱼ (-1) ^ j * (z / 2) ^ (2 j + n) / (j! (j + n)!)` at every
`z : ℂ`. -/
theorem hasSum_besselJ_natCast (n : ℕ) (z : ℂ) :
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (z / 2) ^ (2 * j + n) / (j ! * (j + n)!))
      (besselJ n z) := by
  simpa only [← Nat.cast_ofNat (R := ℂ) (n := 2), ← Nat.cast_mul, ← Nat.cast_add, cpow_natCast,
    Gamma_nat_eq_factorial] using hasSum_besselJ (n : ℂ) z

/-- Power series of `J_0(z)`: `J_0(z) = ∑ⱼ (-1) ^ j * (z / 2) ^ (2 j) / (j!)²` at every `z : ℂ`. -/
theorem hasSum_besselJ_zero_left (z : ℂ) :
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (z / 2) ^ (2 * j) / (j ! : ℂ) ^ 2) (besselJ 0 z) := by
  simpa only [Nat.cast_zero, add_zero, sq] using hasSum_besselJ_natCast 0 z

/-- Near `0` through `ℂ \ {0}`, `(z / 2) ^ (-ν) J_ν(z) → 1 / Γ(ν + 1)` for every `ν : ℂ`
(DLMF 10.7.3). When `ν + 1` is a nonpositive integer, both sides vanish. -/
theorem tendsto_cpow_neg_mul_besselJ_nhdsNE_zero (ν : ℂ) :
    Tendsto (fun z : ℂ => (z / 2) ^ (-ν) * besselJ ν z) (𝓝[≠] 0) (𝓝 (Gamma (ν + 1))⁻¹) := by
  have hcont : Continuous fun z : ℂ => regularizedHGFun 0 {ν + 1} (-(z / 2) ^ 2) :=
    (analyticOnNhd_regularizedHGFun_of_card_le (a := 0) (b := {ν + 1}) (by simp)).continuousOn
      |>.comp_continuous (by fun_prop) fun _ => mem_univ _
  have h0 : regularizedHGFun 0 {ν + 1} (-((0 : ℂ) / 2) ^ 2) = (Gamma (ν + 1))⁻¹ := by
    simp [regularizedHGFunCoeff_zero_singleton]
  have htend : Tendsto (fun z : ℂ => regularizedHGFun 0 {ν + 1} (-(z / 2) ^ 2))
      (𝓝[≠] 0) (𝓝 (Gamma (ν + 1))⁻¹) :=
    h0 ▸ hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine htend.congr' (eventually_nhdsWithin_of_forall fun z (hz : z ≠ 0) => ?_)
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  dsimp only
  rw [besselJ, ← mul_assoc, ← cpow_add _ _ hz2, neg_add_cancel, cpow_zero, one_mul]

/-! ### Conjugation symmetry and real values -/

/-- **Schwarz reflection for `J_ν`** (DLMF 10.11.9): away from the open negative real ray
`arg z = π`, `J_{conj ν}(conj z) = conj (J_ν(z))`. Note that `z = 0` has `arg 0 = 0 ≠ π` and is
included. -/
theorem besselJ_conj (ν : ℂ) {z : ℂ} (hz : z.arg ≠ π) :
    besselJ (conj ν) (conj z) = conj (besselJ ν z) := by
  have hz2 : (z / 2).arg ≠ π := by
    have hhalf : z / 2 = ((1 / 2 : ℝ) : ℂ) * z := by push_cast; ring
    rwa [hhalf, arg_real_mul z (by positivity)]
  have hstar := (hasSum_besselJ ν z).star
  simp_rw [Complex.star_def] at hstar
  refine (hasSum_besselJ (conj ν) (conj z)).unique ?_
  convert hstar using 1
  ext j
  have hdiv : conj z / 2 = conj (z / 2) := by simp [map_ofNat]
  have hexp : conj ((2 : ℂ) * j + conj ν) = (2 : ℂ) * j + ν := by simp [map_ofNat]
  have hgam : (j : ℂ) + conj ν + 1 = conj ((j : ℂ) + ν + 1) := by simp
  rw [hdiv, conj_cpow _ _ hz2, hexp, hgam, Gamma_conj]
  simp

/-- For an integer order `n`, `J_n(conj z) = conj (J_n(z))` at every `z : ℂ`, including on the
negative real axis. -/
theorem besselJ_int_conj (n : ℤ) (z : ℂ) : besselJ n (conj z) = conj (besselJ n z) := by
  have hnat (m : ℕ) : besselJ m (conj z) = conj (besselJ m z) := by
    have hstar := (hasSum_besselJ_natCast m z).star
    simp_rw [Complex.star_def] at hstar
    refine (hasSum_besselJ_natCast m (conj z)).unique ?_
    convert hstar using 1
    ext j
    simp [map_ofNat]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using hnat m
  · rw [Int.cast_neg, besselJ_neg_int, besselJ_neg_int, Int.cast_natCast, hnat m, map_mul,
      map_zpow₀, map_neg, map_one]

/-- For a real order `ν` and a nonnegative real argument `x ≥ 0`, `J_ν(x)` is real. -/
theorem besselJ_ofReal_im_of_nonneg (ν : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (besselJ ν x).im = 0 := by
  have harg : (x : ℂ).arg ≠ π := by
    rw [arg_ofReal_of_nonneg hx]
    exact Real.pi_ne_zero.symm
  have h := besselJ_conj (ν : ℂ) harg
  simp only [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- For a real order `ν` and `x ≥ 0`, `J_ν(x)` coincides with the coercion of its real part. -/
theorem ofReal_re_besselJ_ofReal_of_nonneg (ν : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ((besselJ ν x).re : ℂ) = besselJ ν x := by
  apply Complex.ext <;> simp [besselJ_ofReal_im_of_nonneg ν hx]

/-- For an integer order `n` and any real argument `x`, `J_n(x)` is real. -/
@[simp]
theorem besselJ_int_ofReal_im (n : ℤ) (x : ℝ) : (besselJ n x).im = 0 := by
  have h := besselJ_int_conj n x
  rw [conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- For an integer order `n` and any real argument `x`, `((J_n(x)).re : ℂ) = J_n(x)`. -/
theorem ofReal_re_besselJ_int_ofReal (n : ℤ) (x : ℝ) :
    ((besselJ n x).re : ℂ) = besselJ n x := by
  apply Complex.ext <;> simp

/-! ### Hansen–Bessel circle integrals and Bessel's integrals for integer orders -/

/-- Termwise integration of `e^{w cos θ} = ∑ₖ wᵏ cosᵏ θ / k!` against the Fourier character
`e^{i n θ}` over `[-π, π]`, for any complex parameter `w`. -/
theorem hasSum_integral_exp_mul_cos_mul_exp (w : ℂ) (n : ℤ) :
    HasSum (fun k : ℕ => w ^ k / k ! *
        ∫ θ in -π..π, (Real.cos θ : ℂ) ^ k * exp (n * θ * I))
      (∫ θ in -π..π, exp (w * Real.cos θ) * exp (n * θ * I)) := by
  simp_rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => ‖w‖ ^ k / k !)
    (fun k => by fun_prop) (fun k => ae_of_all _ fun θ _ => ?_)
    (ae_of_all _ fun _ _ => Real.summable_pow_div_factorial ‖w‖)
    intervalIntegrable_const (ae_of_all _ fun θ _ => ?_)
  · have harg : (n : ℂ) * θ * I = ((n * θ : ℝ) : ℂ) * I := by push_cast; ring
    have hexp : ‖exp (n * θ * I)‖ = 1 := by rw [harg, norm_exp_ofReal_mul_I]
    have hcos : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by
      rw [norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one θ
    rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, norm_natCast, hexp, mul_one]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hcos)
  · have h := (NormedSpace.expSeries_div_hasSum_exp (w * Real.cos θ)).mul_right (exp (n * θ * I))
    rw [← exp_eq_exp_ℂ] at h
    convert h using 2 with k
    rw [mul_pow]
    ring

private theorem integral_exp_I_mul_cos_mul_exp_natCast (z : ℂ) (n : ℕ) :
    ∫ θ in -π..π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  have h := hasSum_integral_exp_mul_cos_mul_exp (I * z) (n : ℤ)
  simp_rw [TauCeti.integral_cos_pow_mul_cexp] at h
  simp only [Int.cast_natCast] at h
  have hz : ∀ k ∉ Set.range (fun j : ℕ => 2 * j + n),
      (I * z) ^ k / k ! * (∑ m ∈ Finset.range (k + 1), (1 / 2 : ℂ) ^ k * k.choose m *
        if 2 * (m : ℤ) - k + n = 0 then 2 * (π : ℂ) else 0) = 0 := by
    intro k hk
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m _ => ?_)
    rw [ite_eq_right fun hm => hk ⟨m, by dsimp only; omega⟩, mul_zero]
  have hinj : Function.Injective fun j : ℕ => 2 * j + n := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff hz] at h
  refine h.unique ?_
  convert (hasSum_besselJ_natCast n z).mul_left (2 * (π : ℂ) * I ^ n) using 2 with j
  dsimp only [Function.comp_apply]
  rw [Finset.sum_eq_single j (fun m _ hm => by rw [ite_eq_right (by omega), mul_zero])
    (fun hj => absurd (Finset.mem_range.mpr (by omega)) hj), ite_eq_left (by push_cast; ring)]
  have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ 2 * j + n)
  have hsub : 2 * j + n - j = j + n := by omega
  rw [hsub] at hfac
  have hc : ((2 * j + n).choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hIpow : I ^ (2 * j + n) = (-1 : ℂ) ^ j * I ^ n := by
    rw [pow_add, pow_mul, I_sq]
  rw [mul_pow I z, hIpow, ← hfac]
  push_cast
  field_simp
  ring

/-- **Hansen–Bessel circle integral**: for every `z : ℂ` and `n : ℤ`,
`∫_{-π}^π e^{i z cos θ} e^{i n θ} dθ = 2π i^n J_n(z)`. -/
theorem integral_exp_I_mul_cos_mul_exp (z : ℂ) (n : ℤ) :
    ∫ θ in -π..π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using integral_exp_I_mul_cos_mul_exp_natCast z m
  · have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
      (fun θ : ℝ => exp (I * z * Real.cos θ) * exp (m * θ * I))
    rw [neg_neg, integral_exp_I_mul_cos_mul_exp_natCast] at h
    have hI : I ^ (-m : ℤ) * (-1 : ℂ) ^ (m : ℤ) = I ^ m := by
      rw [zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, inv_I, ← mul_pow]
      simp
    have hrhs : 2 * (π : ℂ) * I ^ (-m : ℤ) * besselJ ((-m : ℤ) : ℂ) z =
        2 * (π : ℂ) * I ^ m * besselJ m z := by
      rw [Int.cast_neg, besselJ_neg_int, Int.cast_natCast]
      linear_combination 2 * (π : ℂ) * besselJ m z * hI
    rw [hrhs, ← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Real.cos_neg, ofReal_neg, Int.cast_neg, Int.cast_natCast]
    ring_nf

/-- Because `θ ↦ e^{i z cos θ}` is even, replacing `e^{i n θ}` by `e^{-i n θ}` leaves the circle
integral unchanged: `∫_{-π}^π e^{i z cos θ} e^{-i n θ} dθ = 2π i^n J_n(z)`. -/
theorem integral_exp_I_mul_cos_mul_exp_neg (z : ℂ) (n : ℤ) :
    ∫ θ in -π..π, exp (I * z * Real.cos θ) * exp (-(n * θ * I)) =
      2 * π * I ^ n * besselJ n z := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
    (fun θ : ℝ => exp (I * z * Real.cos θ) * exp (n * θ * I))
  rw [neg_neg, integral_exp_I_mul_cos_mul_exp] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Real.cos_neg, ofReal_neg]
  ring_nf

private theorem periodic_exp_I_mul_cos_mul_exp (z : ℂ) (n : ℤ) :
    Function.Periodic (fun θ : ℝ => exp (I * z * Real.cos θ) * exp (n * θ * I)) (2 * π) := by
  intro θ
  have hexp : exp ((n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) = exp (n * θ * I) := by
    have hsplit : (n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I =
        n * θ * I + n * (2 * π * I) := by push_cast; ring
    rw [hsplit, exp_add, exp_int_mul, exp_two_pi_mul_I, one_zpow, mul_one]
  simp only [Real.cos_add_two_pi, hexp]

/-- **Hansen–Bessel circle integral over any period `[a, a + 2π]`**:
`∫_a^{a + 2π} e^{i z cos θ} e^{i n θ} dθ = 2π i^n J_n(z)`. -/
theorem integral_exp_I_mul_cos_mul_exp_add_two_pi (z : ℂ) (n : ℤ) (a : ℝ) :
    ∫ θ in a..a + 2 * π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  rw [(periodic_exp_I_mul_cos_mul_exp z n).intervalIntegral_add_eq a (-π)]
  have hpi : -π + 2 * π = π := by ring
  rw [hpi, integral_exp_I_mul_cos_mul_exp]

/-- **Sine-phase circle integral over any period `[a, a + 2π]`**:
`∫_a^{a + 2π} e^{i (z sin θ - n θ)} dθ = 2π J_n(z)` for every `z : ℂ` and `n : ℤ`. -/
theorem integral_exp_I_mul_sin_sub_int_mul_add_two_pi (z : ℂ) (n : ℤ) (a : ℝ) :
    ∫ θ in a..a + 2 * π, exp (I * (z * Real.sin θ - n * θ)) = 2 * π * besselJ n z := by
  have hI : I ^ n ≠ 0 := zpow_ne_zero n I_ne_zero
  apply mul_right_cancel₀ hI
  rw [← intervalIntegral.integral_mul_const]
  have hpoint (θ : ℝ) : exp (I * (z * Real.sin θ - n * θ)) * I ^ n =
      exp (I * z * Real.cos (π / 2 - θ)) * exp (n * ((π / 2 - θ : ℝ) : ℂ) * I) := by
    have hIn : I ^ n = exp ((n : ℂ) * (π / 2 * I)) := by
      rw [exp_int_mul, exp_pi_div_two_mul_I]
    have hexp_eq : I * (z * (Real.sin θ : ℂ) - n * θ) + (n : ℂ) * (π / 2 * I) =
        I * z * (Real.sin θ : ℂ) + (n : ℂ) * ((π / 2 - θ : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hIn, ← exp_add, hexp_eq, exp_add, ← Real.cos_pi_div_two_sub θ]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => exp (I * z * Real.cos u) * exp (n * u * I)) (π / 2)]
  have hend : π / 2 - a = (π / 2 - (a + 2 * π)) + 2 * π := by ring
  rw [hend, integral_exp_I_mul_cos_mul_exp_add_two_pi]
  ring

/-- **Sine-phase circle integral on `[-π, π]`**:
`∫_{-π}^π e^{i (z sin θ - n θ)} dθ = 2π J_n(z)` for every `z : ℂ` and `n : ℤ`. -/
theorem integral_exp_I_mul_sin_sub_int_mul (z : ℂ) (n : ℤ) :
    ∫ θ in -π..π, exp (I * (z * Real.sin θ - n * θ)) = 2 * π * besselJ n z := by
  have h := integral_exp_I_mul_sin_sub_int_mul_add_two_pi z n (-π)
  have hpi : -π + 2 * π = π := by ring
  rwa [hpi] at h

/-- **Bessel's first integral** (DLMF 10.9.2): for every `z : ℂ` and `n : ℤ`,
`∫_0^π cos(z sin θ - n θ) dθ = π J_n(z)`. -/
theorem integral_cos_mul_sin_sub_int_mul (z : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..π, cos (z * Real.sin θ - n * θ) = π * besselJ n z := by
  let f : ℝ → ℂ := fun θ => exp (I * (z * Real.sin θ - n * θ))
  have hf_cont : Continuous f := by fun_prop
  have hcos (θ : ℝ) : cos (z * Real.sin θ - n * θ) = (f θ + f (-θ)) / 2 := by
    dsimp only [f]
    have h1 : (z * (Real.sin θ : ℂ) - n * θ) * I = I * (z * Real.sin θ - n * θ) := by ring
    have h2 : -(z * (Real.sin θ : ℂ) - n * θ) * I =
        I * (z * (-Real.sin θ : ℂ) - n * (-θ : ℂ)) := by ring
    rw [Real.sin_neg, ofReal_neg, ofReal_neg, cos, h1, h2]
  have hneg : ∫ θ in (0 : ℝ)..π, f (-θ) = ∫ θ in -π..0, f θ := by
    simpa only [neg_zero] using intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) f
  simp_rw [hcos]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (hf_cont.intervalIntegrable 0 π)
      ((by fun_prop : Continuous fun θ => f (-θ)).intervalIntegrable 0 π),
    hneg, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hf_cont.intervalIntegrable (-π) 0)
      (hf_cont.intervalIntegrable 0 π)]
  dsimp only [f]
  rw [integral_exp_I_mul_sin_sub_int_mul]
  ring

/-- **Bessel's cosine-weighted exponential integral** (DLMF 10.9.2): for every `z : ℂ` and `n : ℤ`,
`∫_0^π e^{i z cos θ} cos(n θ) dθ = π i^n J_n(z)`. -/
theorem integral_exp_I_mul_cos_mul_cos (z : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..π, exp (I * z * Real.cos θ) * Real.cos (n * θ) =
      π * I ^ n * besselJ n z := by
  let g : ℝ → ℂ := fun θ => exp (I * z * Real.cos θ) * Real.cos (n * θ)
  have hg_cont : Continuous g := by fun_prop
  have heven : ∫ θ in -π..0, g θ = ∫ θ in (0 : ℝ)..π, g θ := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) g
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    dsimp only [g]
    rw [Real.cos_neg, mul_neg, Real.cos_neg]
  have hfull : ∫ θ in -π..π, g θ = 2 * π * I ^ n * besselJ n z := by
    have hdecomp (θ : ℝ) : g θ =
        (exp (I * z * Real.cos θ) * exp (n * θ * I) +
          exp (I * z * Real.cos θ) * exp (-(n * θ * I))) / 2 := by
      dsimp only [g]
      have hnθ : (((n : ℝ) * θ : ℝ) : ℂ) = n * θ := by push_cast; ring
      rw [ofReal_cos (n * θ), hnθ, cos]
      ring_nf
    simp_rw [hdecomp]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add
        ((by fun_prop : Continuous fun θ : ℝ =>
          exp (I * z * Real.cos θ) * exp (n * θ * I)).intervalIntegrable (-π) π)
        ((by fun_prop : Continuous fun θ : ℝ =>
          exp (I * z * Real.cos θ) * exp (-(n * θ * I))).intervalIntegrable (-π) π),
      integral_exp_I_mul_cos_mul_exp, integral_exp_I_mul_cos_mul_exp_neg]
    ring
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hg_cont.intervalIntegrable (μ := volume) (-π) 0)
    (hg_cont.intervalIntegrable (μ := volume) 0 π)
  rw [heven, hfull] at hadj
  have hg_half : ∫ θ in (0 : ℝ)..π, g θ = π * I ^ n * besselJ n z := by
    linear_combination hadj / 2
  exact hg_half

/-! ### Order-zero Bessel integrals (DLMF 10.9.1) -/

/-- For every `z : ℂ`, `∫_0^{2π} e^{i z cos θ} dθ = 2π J_0(z)`. -/
theorem integral_exp_I_mul_cos_zero_two_pi (z : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (I * z * Real.cos θ) = 2 * π * besselJ 0 z := by
  simpa using integral_exp_I_mul_cos_mul_exp_add_two_pi z 0 0

/-- **The Bessel integral for `J_0`** (DLMF 10.9.1): for every `z : ℂ`,
`J_0(z) = (2π)⁻¹ ∫_0^{2π} e^{i z cos θ} dθ`. -/
theorem besselJ_zero_eq_integral_exp_I_mul_cos (z : ℂ) :
    besselJ 0 z = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, exp (I * z * Real.cos θ) := by
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [integral_exp_I_mul_cos_zero_two_pi, inv_mul_cancel_left₀ h2pi]

/-- For every `z : ℂ`, `∫_0^π e^{i z cos θ} dθ = π J_0(z)` (DLMF 10.9.1). -/
theorem integral_exp_I_mul_cos_zero_pi (z : ℂ) :
    ∫ θ in (0 : ℝ)..π, exp (I * z * Real.cos θ) = π * besselJ 0 z := by
  simpa using integral_exp_I_mul_cos_mul_cos z 0

/-- For every `z : ℂ`, `∫_0^π cos(z sin θ) dθ = π J_0(z)` (DLMF 10.9.1). -/
theorem integral_cos_mul_sin_zero_pi (z : ℂ) :
    ∫ θ in (0 : ℝ)..π, cos (z * Real.sin θ) = π * besselJ 0 z := by
  simpa using integral_cos_mul_sin_sub_int_mul z 0

/-- For every `z : ℂ`, `∫_0^π cos(z cos θ) dθ = π J_0(z)` (DLMF 10.9.1). -/
theorem integral_cos_mul_cos_zero_pi (z : ℂ) :
    ∫ θ in (0 : ℝ)..π, cos (z * Real.cos θ) = π * besselJ 0 z := by
  have hsymm : ∫ θ in (0 : ℝ)..π, exp (-(I * z * Real.cos θ)) =
      ∫ θ in (0 : ℝ)..π, exp (I * z * Real.cos θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => exp (I * z * Real.cos θ)) π (a := 0) (b := π)
    rw [sub_self, sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Real.cos_pi_sub, ofReal_neg, mul_neg]
  have hcos (θ : ℝ) : cos (z * Real.cos θ) =
      (exp (I * z * Real.cos θ) + exp (-(I * z * Real.cos θ))) / 2 := by
    rw [cos]
    congr 1
    congr 1 <;> ring_nf
  simp_rw [hcos]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add
      ((by fun_prop : Continuous fun θ : ℝ => exp (I * z * Real.cos θ)).intervalIntegrable 0 π)
      ((by fun_prop : Continuous fun θ : ℝ => exp (-(I * z * Real.cos θ))).intervalIntegrable 0 π),
    hsymm, integral_exp_I_mul_cos_zero_pi]
  ring

/-! ### Uniform bounds from Bessel's integral (DLMF 10.14.1, 10.14.4) -/

/-- **Strip bound for integer-order Bessel functions** (DLMF 10.14.4): for every `n : ℤ` and
`z : ℂ`, `‖J_n(z)‖ ≤ e^{|Im z|}`. -/
theorem norm_besselJ_int_le_exp_abs_im (n : ℤ) (z : ℂ) :
    ‖besselJ n z‖ ≤ Real.exp |z.im| := by
  have h2pi_pos : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hbound : ‖∫ θ in -π..π, exp (I * (z * Real.sin θ - n * θ))‖ ≤
      Real.exp |z.im| * |π - -π| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (I * (z * Real.sin θ - n * θ)).re = -z.im * Real.sin θ := by
      simp only [mul_re, sub_re, mul_im, sub_im, I_re, I_im, ofReal_re, ofReal_im,
        intCast_re, intCast_im]
      ring
    rw [hre]
    calc -z.im * Real.sin θ ≤ |-z.im * Real.sin θ| := le_abs_self _
      _ = |z.im| * |Real.sin θ| := by rw [abs_mul, abs_neg]
      _ ≤ |z.im| * 1 := by gcongr; exact Real.abs_sin_le_one θ
      _ = |z.im| := mul_one _
  rw [integral_exp_I_mul_sin_sub_int_mul, norm_mul, norm_mul, norm_ofNat, norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, show π - -π = 2 * π by ring,
    abs_of_pos h2pi_pos] at hbound
  exact le_of_mul_le_mul_left (by linarith) h2pi_pos

/-- **Real-axis bound for integer-order Bessel functions** (DLMF 10.14.1): for every `n : ℤ` and
`x : ℝ`, `‖J_n(x)‖ ≤ 1`. -/
theorem norm_besselJ_int_ofReal_le_one (n : ℤ) (x : ℝ) : ‖besselJ n x‖ ≤ 1 := by
  simpa using norm_besselJ_int_le_exp_abs_im n (x : ℂ)

/-- For every `n : ℤ` and `x : ℝ`, `|(J_n(x)).re| ≤ 1`. -/
theorem abs_re_besselJ_int_ofReal_le_one (n : ℤ) (x : ℝ) : |(besselJ n x).re| ≤ 1 :=
  (abs_re_le_norm (besselJ n x)).trans (norm_besselJ_int_ofReal_le_one n x)

/-! ### Poisson's integral for complex order `Re ν > -1 / 2` (DLMF 10.9.4) -/

private theorem ofReal_sq_cpow_mul_ofReal {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    ((s ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) * s = (s : ℂ) ^ (2 * ν) := by
  have hs_ne : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hs2_ne : ((s ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (pow_ne_zero 2 hs.ne')
  have hlog : log ((s ^ 2 : ℝ) : ℂ) = 2 * log (s : ℂ) := by
    rw [← ofReal_log (sq_nonneg s), Real.log_pow, ← ofReal_log hs.le]
    push_cast
    ring
  rw [cpow_def_of_ne_zero hs2_ne, cpow_def_of_ne_zero hs_ne, hlog]
  conv_lhs => rhs; rw [← exp_log hs_ne]
  rw [← exp_add]
  congr 1
  ring

private theorem gamma_nat_add_half (j : ℕ) :
    Gamma ((j : ℂ) + 1 / 2) = (2 * j)! / ((4 : ℂ) ^ j * j !) * √π := by
  have hreal : Real.Gamma ((j : ℝ) + 1 / 2) = (2 * j)! / ((4 : ℝ) ^ j * j !) * √π := by
    rw [Real.Gamma_nat_add_half_eq_factorial]
    ring
  have hcast : (((j : ℝ) + 1 / 2 : ℝ) : ℂ) = (j : ℂ) + 1 / 2 := by push_cast; ring
  rw [← hcast, Gamma_ofReal, hreal]
  push_cast
  rfl

private theorem integral_pow_mul_one_sub_sq_cpow_zero_one {ν : ℂ} (hν : -1 / 2 < ν.re) (j : ℕ) :
    ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (2 * j) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) =
      Gamma (j + 1 / 2) * Gamma (ν + 1 / 2) / (2 * Gamma (j + ν + 1)) := by
  let g : ℝ → ℂ := fun u => (u : ℂ) ^ ((j : ℂ) + 1 / 2 - 1) * (1 - (u : ℂ)) ^ (ν + 1 / 2 - 1)
  have himg : (fun t : ℝ => t ^ 2) '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext u
    simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact ⟨sq_pos_of_pos ht0, by nlinarith⟩
    · rintro ⟨hu0, hu1⟩
      exact ⟨√u, ⟨Real.sqrt_pos.mpr hu0, by simpa using Real.sqrt_lt_sqrt hu0.le hu1⟩,
        Real.sq_sqrt hu0.le⟩
  have hinj : InjOn (fun t : ℝ => t ^ 2) (Ioo (0 : ℝ) 1) :=
    fun a ha b hb hab => (sq_eq_sq₀ ha.1.le hb.1.le).mp hab
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * t) (Ioo 0 1) t :=
    fun t _ => by
      have h := (hasDerivAt_pow 2 t).hasDerivWithinAt (s := Ioo 0 1)
      rwa [Nat.cast_ofNat, pow_one] at h
  have hchg := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  have hlhs : ∫ u in (fun t : ℝ => t ^ 2) '' Ioo (0 : ℝ) 1, g u =
      Gamma (j + 1 / 2) * Gamma (ν + 1 / 2) / Gamma (j + ν + 1) := by
    have hj_pos : 0 < ((j : ℂ) + 1 / 2).re := by
      rw [add_re, natCast_re, div_ofNat_re, one_re]; positivity
    have hν_pos : 0 < (ν + 1 / 2).re := by
      rw [add_re, div_ofNat_re, one_re]; linarith
    have hsum : (j : ℂ) + 1 / 2 + (ν + 1 / 2) = j + ν + 1 := by ring
    rw [himg, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    dsimp only [g]
    rw [← betaIntegral, betaIntegral_eq_Gamma_mul_div _ _ hj_pos hν_pos, hsum]
  have hrhs : ∫ t in Ioo (0 : ℝ) 1, |2 * t| • g (t ^ 2) =
      2 * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (2 * j) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) := by
    have hcongr : EqOn (fun t : ℝ => |2 * t| • g (t ^ 2))
        (fun t : ℝ => 2 * ((t : ℂ) ^ (2 * j) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)))
        (Ioo 0 1) := by
      intro t ht
      have ht2 : 0 < 2 * t := by linarith [ht.1]
      dsimp only [g]
      rw [abs_of_pos ht2, real_smul]
      have h1 : (j : ℂ) + 1 / 2 - 1 = j - 1 / 2 := by ring
      have h2 : ν + 1 / 2 - 1 = ν - 1 / 2 := by ring
      have h3 : (1 : ℂ) - ((t ^ 2 : ℝ) : ℂ) = ((1 - t ^ 2 : ℝ) : ℂ) := by push_cast; ring
      have hpow : ((t ^ 2 : ℝ) : ℂ) ^ ((j : ℂ) - 1 / 2) * t = (t : ℂ) ^ (2 * j) := by
        rw [ofReal_sq_cpow_mul_ofReal ht.1 j, ← Nat.cast_ofNat (R := ℂ) (n := 2), ← Nat.cast_mul,
          cpow_natCast]
      rw [h1, h2, h3, ofReal_mul, ofReal_ofNat]
      linear_combination 2 * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) * hpow
    rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_const_mul,
      setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  rw [hlhs, hrhs] at hchg
  linear_combination -hchg / 2

private theorem integrableOn_pow_mul_one_sub_sq_cpow {ν : ℂ} (hν : -1 / 2 < ν.re) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2))
      (Ioo (-1 : ℝ) 1) := by
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2))
      (Ioo (-1 : ℝ) 1) :=
    (continuous_ofReal.pow k).continuousOn.mul
      ((by fun_prop : Continuous fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ)).continuousOn.cpow_const
        fun t ht => ofReal_mem_slitPlane.mpr (by nlinarith [ht.1, ht.2]))
  refine (TauCeti.integrableOn_Ioo_one_sub_sq_rpow (a := ν.re + 1 / 2) (by linarith)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioo)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_)
  have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  have hre : (ν - 1 / 2).re = ν.re + 1 / 2 - 1 := by
    rw [sub_re, div_ofNat_re, one_re]; ring
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hpos, hre]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hpos.le _) (pow_le_one₀ (abs_nonneg t) habs)

private theorem integral_pow_mul_one_sub_sq_cpow_neg_one_one {ν : ℂ} (hν : -1 / 2 < ν.re)
    (k : ℕ) :
    ∫ t in (-1 : ℝ)..1, (t : ℂ) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) =
      (∫ t in (0 : ℝ)..1, (-(t : ℂ)) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)) +
        ∫ t in (0 : ℝ)..1, (t : ℂ) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) := by
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)
  have hint_all : IntervalIntegrable f volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr
      (integrableOn_pow_mul_one_sub_sq_cpow hν k)
  have hint_neg : IntervalIntegrable f volume (-1) 0 :=
    hint_all.mono_set (uIcc_subset_uIcc left_mem_uIcc (by norm_num [uIcc_of_le]))
  have hint_pos : IntervalIntegrable f volume 0 1 :=
    hint_all.mono_set (uIcc_subset_uIcc (by norm_num [uIcc_of_le]) right_mem_uIcc)
  have hneg : ∫ t in (-1 : ℝ)..0, f t =
      ∫ t in (0 : ℝ)..1, (-(t : ℂ)) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) f
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp only [f]
    rw [ofReal_neg, neg_sq]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_neg hint_pos, hneg]

private theorem integral_pow_mul_one_sub_sq_cpow_even {ν : ℂ} (hν : -1 / 2 < ν.re) (j : ℕ) :
    ∫ t in (-1 : ℝ)..1, (t : ℂ) ^ (2 * j) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) =
      Gamma (j + 1 / 2) * Gamma (ν + 1 / 2) / Gamma (j + ν + 1) := by
  have heven : ∫ t in (0 : ℝ)..1, (-(t : ℂ)) ^ (2 * j) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) =
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (2 * j) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [pow_mul (-(t : ℂ)) 2 j, neg_sq, ← pow_mul]
  rw [integral_pow_mul_one_sub_sq_cpow_neg_one_one hν (2 * j), heven,
    integral_pow_mul_one_sub_sq_cpow_zero_one hν j]
  ring

private theorem integral_pow_mul_one_sub_sq_cpow_odd {ν : ℂ} (hν : -1 / 2 < ν.re) (j : ℕ) :
    ∫ t in (-1 : ℝ)..1, (t : ℂ) ^ (2 * j + 1) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) = 0 := by
  have hodd :
      ∫ t in (0 : ℝ)..1, (-(t : ℂ)) ^ (2 * j + 1) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) =
        -∫ t in (0 : ℝ)..1, (t : ℂ) ^ (2 * j + 1) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [pow_succ (-(t : ℂ)), pow_mul (-(t : ℂ)) 2 j, neg_sq, ← pow_mul, pow_succ]
    ring
  rw [integral_pow_mul_one_sub_sq_cpow_neg_one_one hν (2 * j + 1), hodd, neg_add_cancel]

/-- **Poisson's integral on `[-1, 1]`** (DLMF 10.9.4): for `Re ν > -1 / 2` and any `z : ℂ`,
`∫_{-1}^1 e^{i z t} (1 - t²) ^ (ν - 1 / 2) dt = √π Γ(ν + 1 / 2) ₀F₁(; ν + 1; -(z / 2)²)`. -/
theorem integral_exp_I_mul_mul_one_sub_sq_cpow {ν : ℂ} (hν : -1 / 2 < ν.re) (z : ℂ) :
    ∫ t in (-1 : ℝ)..1, exp (I * z * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) =
      √π * Gamma (ν + 1 / 2) * regularizedHGFun 0 {ν + 1} (-(z / 2) ^ 2) := by
  let F : ℕ → ℝ → ℂ := fun k t =>
    (I * z) ^ k / k ! * ((t : ℂ) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2))
  have hF_int (k : ℕ) : Integrable (F k) (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    (integrableOn_pow_mul_one_sub_sq_cpow hν k).const_mul _
  have hw_int : Integrable (fun t : ℝ => (1 - t ^ 2) ^ (ν.re + 1 / 2 - 1))
      (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    TauCeti.integrableOn_Ioo_one_sub_sq_rpow (by linarith)
  have hF_norm_le (k : ℕ) : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1),
      ‖F k t‖ ≤ ‖z‖ ^ k / k ! * (1 - t ^ 2) ^ (ν.re + 1 / 2 - 1) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
    have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
    have hre : (ν - 1 / 2).re = ν.re + 1 / 2 - 1 := by
      rw [sub_re, div_ofNat_re, one_re]; ring
    dsimp only [F]
    rw [norm_mul, norm_div, norm_pow, norm_mul, norm_I, one_mul, norm_natCast, norm_mul, norm_pow,
      norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hpos, hre]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (Real.rpow_nonneg hpos.le _) (pow_le_one₀ (abs_nonneg t) habs))
      (by positivity)
  have hsum_norm : Summable fun k : ℕ => ∫ t in Ioo (-1 : ℝ) 1, ‖F k t‖ := by
    refine Summable.of_nonneg_of_le (fun k => setIntegral_nonneg measurableSet_Ioo fun _ _ =>
      norm_nonneg _) (fun k => ?_)
      ((Real.summable_pow_div_factorial ‖z‖).mul_right
        (∫ t in Ioo (-1 : ℝ) 1, (1 - t ^ 2) ^ (ν.re + 1 / 2 - 1)))
    rw [← integral_const_mul]
    exact integral_mono_ae (hF_int k).norm (hw_int.const_mul _) (hF_norm_le k)
  have hsum := hasSum_integral_of_summable_integral_norm hF_int hsum_norm
  have hpt : EqOn (fun t : ℝ => ∑' k : ℕ, F k t)
      (fun t : ℝ => exp (I * z * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)) (Ioo (-1 : ℝ) 1) := by
    intro t _
    have hexp := (NormedSpace.expSeries_div_hasSum_exp (I * z * t)).mul_right
      (((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2))
    rw [← exp_eq_exp_ℂ] at hexp
    refine (HasSum.tsum_eq ?_)
    convert hexp using 2 with k
    dsimp only [F]
    rw [mul_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hsum
  have hterm (k : ℕ) : ∫ t in Ioo (-1 : ℝ) 1, F k t =
      (I * z) ^ k / k ! *
        ∫ t in (-1 : ℝ)..1, (t : ℂ) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) := by
    dsimp only [F]
    rw [integral_const_mul, setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [hterm] at hsum
  have hodd_zero : ∀ k ∉ Set.range (fun j : ℕ => 2 * j),
      (I * z) ^ k / k ! *
        (∫ t in (-1 : ℝ)..1, (t : ℂ) ^ k * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)) = 0 := by
    intro k hk
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exact absurd ⟨j, rfl⟩ hk
    · rw [integral_pow_mul_one_sub_sq_cpow_odd hν j, mul_zero]
  have hinj : Function.Injective fun j : ℕ => 2 * j := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff hodd_zero] at hsum
  refine hsum.unique ?_
  convert (hasSum_regularizedHGFun (a := 0) (b := {ν + 1}) (by simp) (-(z / 2) ^ 2)).mul_left
    (√π * Gamma (ν + 1 / 2)) using 2 with j
  dsimp only [Function.comp_apply]
  have hadd : (j : ℂ) + ν + 1 = ν + 1 + j := by ring
  have hfac_ne : ((2 * j)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (2 * j).factorial_ne_zero
  have h4_ne : (4 : ℂ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
  have hj_ne : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  rw [integral_pow_mul_one_sub_sq_cpow_even hν j, gamma_nat_add_half j,
    regularizedHGFunCoeff_zero_singleton, hadd, mul_pow I z, pow_mul I 2 j, I_sq,
    neg_eq_neg_one_mul ((z / 2) ^ 2), mul_pow, div_pow, pow_mul z 2 j,
    show (2 : ℂ) ^ 2 = 4 by norm_num, div_pow, ← pow_mul z 2 j]
  by_cases hG : Gamma (ν + 1 + j) = 0
  · simp [hG]
  · field_simp [hfac_ne, h4_ne, hj_ne, hG]

/-- **Poisson's cosine integral on `[-1, 1]`** (DLMF 10.9.4): for `Re ν > -1 / 2` and `z : ℂ`,
`∫_{-1}^1 cos(z t) (1 - t²) ^ (ν - 1 / 2) dt = √π Γ(ν + 1 / 2) ₀F₁(; ν + 1; -(z / 2)²)`. -/
theorem integral_cos_mul_mul_one_sub_sq_cpow {ν : ℂ} (hν : -1 / 2 < ν.re) (z : ℂ) :
    ∫ t in (-1 : ℝ)..1, cos (z * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) =
      √π * Gamma (ν + 1 / 2) * regularizedHGFun 0 {ν + 1} (-(z / 2) ^ 2) := by
  have hint (w : ℂ) : IntervalIntegrable
      (fun t : ℝ => exp (I * w * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)) volume (-1) 1 := by
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr ?_
    refine ((integrableOn_pow_mul_one_sub_sq_cpow hν 0).norm.const_mul (Real.exp ‖w‖)).mono'
      (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => exp (I * w * t)).continuousOn.mul
        ((by fun_prop : Continuous fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ)).continuousOn.cpow_const
          fun t ht => ofReal_mem_slitPlane.mpr (by nlinarith [ht.1, ht.2]))
    · simp only [pow_zero, one_mul, norm_mul]
      have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
      have hexp : ‖exp (I * w * t)‖ ≤ Real.exp ‖w‖ := by
        rw [norm_exp]
        apply Real.exp_le_exp.mpr
        calc (I * w * t).re ≤ ‖I * w * (t : ℂ)‖ := re_le_norm _
          _ = ‖w‖ * |t| := by rw [norm_mul, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
          _ ≤ ‖w‖ * 1 := by gcongr
          _ = ‖w‖ := mul_one _
      exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hcos (t : ℝ) : cos (z * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) =
      (exp (I * z * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) +
        exp (I * (-z) * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)) / 2 := by
    rw [cos]
    ring_nf
  simp_rw [hcos]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint z) (hint (-z)),
    integral_exp_I_mul_mul_one_sub_sq_cpow hν z, integral_exp_I_mul_mul_one_sub_sq_cpow hν (-z),
    neg_div, neg_sq]
  ring

/-- `J_ν(z)` as an integral on `[-1, 1]` (DLMF 10.9.4): for `Re ν > -1 / 2` and every `z : ℂ`,
`J_ν(z) = (z / 2) ^ ν / (√π Γ(ν + 1 / 2)) ∫_{-1}^1 cos(z t) (1 - t²) ^ (ν - 1 / 2) dt`. -/
theorem besselJ_eq_integral_cos_mul_mul_one_sub_sq_cpow {ν : ℂ} (hν : -1 / 2 < ν.re) (z : ℂ) :
    besselJ ν z =
      (z / 2) ^ ν / (√π * Gamma (ν + 1 / 2)) *
        ∫ t in (-1 : ℝ)..1, cos (z * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2) := by
  have hne : √π * Gamma (ν + 1 / 2) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos))
      (Gamma_ne_zero_of_re_pos (by rw [add_re, div_ofNat_re, one_re]; linarith))
  rw [integral_cos_mul_mul_one_sub_sq_cpow hν z, besselJ,
    div_eq_mul_inv ((z / 2) ^ ν) (√π * Gamma (ν + 1 / 2)),
    mul_assoc ((z / 2) ^ ν), ← mul_assoc (√π * Gamma (ν + 1 / 2))⁻¹, inv_mul_cancel₀ hne, one_mul]

private theorem image_neg_cos_Ioo :
    (fun θ : ℝ => -Real.cos θ) '' Ioo (0 : ℝ) π = Ioo (-1 : ℝ) 1 := by
  ext t
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθpi⟩, rfl⟩
    have h1 : Real.cos θ < Real.cos 0 :=
      Real.strictAntiOn_cos (left_mem_Icc.mpr Real.pi_pos.le) ⟨hθ0.le, hθpi.le⟩ hθ0
    have h2 : Real.cos π < Real.cos θ :=
      Real.strictAntiOn_cos ⟨hθ0.le, hθpi.le⟩ (right_mem_Icc.mpr Real.pi_pos.le) hθpi
    rw [Real.cos_zero] at h1
    rw [Real.cos_pi] at h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ht_neg, ht_pos⟩
    refine ⟨Real.arccos (-t), ⟨Real.arccos_pos.mpr (by linarith),
      Real.arccos_lt_pi.mpr (by linarith)⟩, ?_⟩
    rw [Real.cos_arccos (by linarith) (by linarith), neg_neg]

private theorem hasDerivWithinAt_neg_cos (θ : ℝ) (s : Set ℝ) :
    HasDerivWithinAt (fun x : ℝ => -Real.cos x) (Real.sin θ) s θ := by
  have h := (Real.hasDerivAt_cos θ).neg.hasDerivWithinAt (s := s)
  rwa [neg_neg] at h

/-- **Poisson's exponential integral on `[0, π]`** (DLMF 10.9.4): for `Re ν > -1 / 2` and `z : ℂ`,
`∫_0^π e^{i z cos θ} (sin θ) ^ (2 ν) dθ = √π Γ(ν + 1 / 2) ₀F₁(; ν + 1; -(z / 2)²)`. -/
theorem integral_exp_I_mul_cos_mul_sin_cpow {ν : ℂ} (hν : -1 / 2 < ν.re) (z : ℂ) :
    ∫ θ in (0 : ℝ)..π, exp (I * z * Real.cos θ) * (Real.sin θ : ℂ) ^ (2 * ν) =
      √π * Gamma (ν + 1 / 2) * regularizedHGFun 0 {ν + 1} (-(z / 2) ^ 2) := by
  let g : ℝ → ℂ := fun t => exp (I * (-z) * t) * ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)
  have hinj : InjOn (fun θ : ℝ => -Real.cos θ) (Ioo (0 : ℝ) π) :=
    (Real.strictAntiOn_cos.neg.mono Ioo_subset_Icc_self).injOn
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) π,
      HasDerivWithinAt (fun x : ℝ => -Real.cos x) (Real.sin θ) (Ioo 0 π) θ :=
    fun θ _ => hasDerivWithinAt_neg_cos θ (Ioo 0 π)
  have hchg := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g
  rw [image_neg_cos_Ioo, setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hchg
  dsimp only [g] at hchg
  rw [integral_exp_I_mul_mul_one_sub_sq_cpow hν (-z), neg_div, neg_sq] at hchg
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc, hchg]
  refine (setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_).symm
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h1 : 1 - (-Real.cos θ) ^ 2 = Real.sin θ ^ 2 := by
    rw [neg_sq, Real.sin_sq]
  rw [abs_of_pos hsin_pos, real_smul, h1, ofReal_neg,
    show I * -z * -(Real.cos θ : ℂ) = I * z * Real.cos θ by ring,
    mul_comm (Real.sin θ : ℂ), mul_assoc, ofReal_sq_cpow_mul_ofReal hsin_pos ν]

/-- **Poisson's cosine integral on `[0, π]`** (DLMF 10.9.4): for `Re ν > -1 / 2` and `z : ℂ`,
`∫_0^π cos(z cos θ) (sin θ) ^ (2 ν) dθ = √π Γ(ν + 1 / 2) ₀F₁(; ν + 1; -(z / 2)²)`. -/
theorem integral_cos_mul_cos_mul_sin_cpow {ν : ℂ} (hν : -1 / 2 < ν.re) (z : ℂ) :
    ∫ θ in (0 : ℝ)..π, cos (z * Real.cos θ) * (Real.sin θ : ℂ) ^ (2 * ν) =
      √π * Gamma (ν + 1 / 2) * regularizedHGFun 0 {ν + 1} (-(z / 2) ^ 2) := by
  have hint (w : ℂ) : IntervalIntegrable
      (fun θ : ℝ => exp (I * w * Real.cos θ) * (Real.sin θ : ℂ) ^ (2 * ν)) volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
    have hinj : InjOn (fun θ : ℝ => -Real.cos θ) (Ioo (0 : ℝ) π) :=
      (Real.strictAntiOn_cos.neg.mono Ioo_subset_Icc_self).injOn
    have hderiv : ∀ θ ∈ Ioo (0 : ℝ) π,
        HasDerivWithinAt (fun x : ℝ => -Real.cos x) (Real.sin θ) (Ioo 0 π) θ :=
      fun θ _ => hasDerivWithinAt_neg_cos θ (Ioo 0 π)
    have hbase : IntegrableOn
        (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2)) (Ioo (-1 : ℝ) 1) := by
      simpa using integrableOn_pow_mul_one_sub_sq_cpow hν 0
    have hpull := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj
      (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2))).mp (image_neg_cos_Ioo.symm ▸ hbase)
    refine (hpull.norm.const_mul (Real.exp ‖w‖)).mono'
      (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_)
    · exact (by fun_prop : Continuous fun θ : ℝ => exp (I * w * Real.cos θ)).continuousOn.mul
        ((continuous_ofReal.comp Real.continuous_sin).continuousOn.cpow_const
          fun θ hθ => ofReal_mem_slitPlane.mpr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))
    · have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
      have h1 : 1 - (-Real.cos θ) ^ 2 = Real.sin θ ^ 2 := by rw [neg_sq, Real.sin_sq]
      have hnorm_sin : ‖(Real.sin θ : ℂ) ^ (2 * ν)‖ =
          ‖|Real.sin θ| • (((1 - (-Real.cos θ) ^ 2 : ℝ) : ℂ) ^ (ν - 1 / 2))‖ := by
        rw [abs_of_pos hsin_pos, real_smul, h1, mul_comm (Real.sin θ : ℂ),
          ofReal_sq_cpow_mul_ofReal hsin_pos ν]
      have hexp : ‖exp (I * w * Real.cos θ)‖ ≤ Real.exp ‖w‖ := by
        rw [norm_exp]
        apply Real.exp_le_exp.mpr
        calc (I * w * Real.cos θ).re ≤ ‖I * w * (Real.cos θ : ℂ)‖ := re_le_norm _
          _ = ‖w‖ * |Real.cos θ| := by
              rw [norm_mul, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
          _ ≤ ‖w‖ * 1 := by gcongr; exact Real.abs_cos_le_one θ
          _ = ‖w‖ := mul_one _
      rw [norm_mul, hnorm_sin]
      exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hcos (θ : ℝ) : cos (z * Real.cos θ) * (Real.sin θ : ℂ) ^ (2 * ν) =
      (exp (I * z * Real.cos θ) * (Real.sin θ : ℂ) ^ (2 * ν) +
        exp (I * (-z) * Real.cos θ) * (Real.sin θ : ℂ) ^ (2 * ν)) / 2 := by
    rw [cos]
    ring_nf
  simp_rw [hcos]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint z) (hint (-z)),
    integral_exp_I_mul_cos_mul_sin_cpow hν z, integral_exp_I_mul_cos_mul_sin_cpow hν (-z),
    neg_div, neg_sq]
  ring

/-- **Poisson's integral for `J_ν(z)`** (DLMF 10.9.4): for `Re ν > -1 / 2` and every `z : ℂ`,
`J_ν(z) = (z / 2) ^ ν / (√π Γ(ν + 1 / 2)) ∫_0^π cos(z cos θ) (sin θ) ^ (2 ν) dθ`. -/
theorem besselJ_eq_integral_cos_mul_cos_mul_sin_cpow {ν : ℂ} (hν : -1 / 2 < ν.re) (z : ℂ) :
    besselJ ν z =
      (z / 2) ^ ν / (√π * Gamma (ν + 1 / 2)) *
        ∫ θ in (0 : ℝ)..π, cos (z * Real.cos θ) * (Real.sin θ : ℂ) ^ (2 * ν) := by
  have hne : √π * Gamma (ν + 1 / 2) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos))
      (Gamma_ne_zero_of_re_pos (by rw [add_re, div_ofNat_re, one_re]; linarith))
  rw [integral_cos_mul_cos_mul_sin_cpow hν z, besselJ,
    div_eq_mul_inv ((z / 2) ^ ν) (√π * Gamma (ν + 1 / 2)),
    mul_assoc ((z / 2) ^ ν), ← mul_assoc (√π * Gamma (ν + 1 / 2))⁻¹, inv_mul_cancel₀ hne, one_mul]

end Complex

namespace Real

/-- **Bessel's integral for real arguments** (DLMF 10.9.2): for every `x : ℝ` and `n : ℤ`,
`∫_0^π cos(x sin θ - n θ) dθ = π Re(J_n(x))` (where `J_n(x)` is real by
`Complex.besselJ_int_ofReal_im`). -/
theorem integral_cos_mul_sin_sub_int_mul (x : ℝ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..π, cos (x * sin θ - n * θ) = π * (Complex.besselJ n x).re := by
  have h := congrArg Complex.re (Complex.integral_cos_mul_sin_sub_int_mul (x : ℂ) n)
  rw [← RCLike.re_to_complex, ← intervalIntegral.intervalIntegral_re
    ((by fun_prop : Continuous fun θ : ℝ =>
      Complex.cos ((x : ℂ) * sin θ - n * θ)).intervalIntegrable 0 π)] at h
  refine (intervalIntegral.integral_congr fun θ _ => ?_).trans (h.trans ?_)
  · rw [RCLike.re_to_complex]
    have hcast : (x : ℂ) * (sin θ : ℂ) - (n : ℂ) * (θ : ℂ) =
        ((x * sin θ - n * θ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_cos, Complex.ofReal_re]
  · exact Complex.re_ofReal_mul _ _

/-- For every `x : ℝ`, `∫_0^π cos(x cos θ) dθ = π Re(J_0(x))` (DLMF 10.9.1). -/
theorem integral_cos_mul_cos_zero_pi (x : ℝ) :
    ∫ θ in (0 : ℝ)..π, cos (x * cos θ) = π * (Complex.besselJ 0 x).re := by
  have h := congrArg Complex.re (Complex.integral_cos_mul_cos_zero_pi (x : ℂ))
  rw [← RCLike.re_to_complex, ← intervalIntegral.intervalIntegral_re
    ((by fun_prop : Continuous fun θ : ℝ =>
      Complex.cos ((x : ℂ) * cos θ)).intervalIntegrable 0 π)] at h
  refine (intervalIntegral.integral_congr fun θ _ => ?_).trans (h.trans ?_)
  · rw [RCLike.re_to_complex, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.ofReal_re]
  · exact Complex.re_ofReal_mul _ _

/-- For every `x : ℝ`, `∫_0^π cos(x sin θ) dθ = π Re(J_0(x))` (DLMF 10.9.1). -/
theorem integral_cos_mul_sin_zero_pi (x : ℝ) :
    ∫ θ in (0 : ℝ)..π, cos (x * sin θ) = π * (Complex.besselJ 0 x).re := by
  simpa using integral_cos_mul_sin_sub_int_mul x 0

end Real
