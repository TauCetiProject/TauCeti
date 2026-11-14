/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.NumberTheory.ZetaValues

/-!
# Bose–Einstein integrals on the positive half-line

For real parameters `p > 1` and `c > 0`, the Bose–Einstein (or Debye) integral
`∫ y in Ioi 0, y ^ (p - 1) / (exp (c * y) - 1)` converges at `0` because `exp (c * y) - 1 ≥ c * y`
leaves an integrable singularity `y ^ (p - 2)`, and at `+∞` because of exponential decay. Expanding
`1 / (exp (c * y) - 1) = ∑' n : ℕ, exp (-c * (n + 1) * y)` and integrating term-by-term evaluates
the integral in terms of `Real.Gamma p` and the Hurwitz/Riemann zeta series
`∑' n : ℕ, 1 / (n + 1) ^ p`.

At odd positive integer powers `y ^ (2 * s - 1)` (`p = 2 * s`), Euler's even-zeta identity
`hasSum_zeta_nat` expresses the integral in closed form through the Bernoulli number
`bernoulli (2 * s)`. When `c = 2 * π`, these moments `(-1) ^ (s + 1) * bernoulli (2 * s) / (4 * s)`
convert the Taylor expansion of `Im f(n + i * y)` into the Bernoulli derivative terms of the
Abel–Plana summation formula.

## Main declarations

* `TauCeti.integrableOn_rpow_div_exp_mul_sub_one`: integrability of
  `y ^ (p - 1) / (exp (c * y) - 1)` on `(0, ∞)` for `p > 1` and `c > 0`.
* `TauCeti.integrableOn_pow_div_exp_mul_sub_one`: integrability of `y ^ k / (exp (c * y) - 1)` on
  `(0, ∞)` for `k : ℕ` with `1 ≤ k` and `c > 0`.
* `TauCeti.hasSum_integral_Ioi_rpow_div_exp_mul_sub_one`: series evaluation of the Bose–Einstein
  integral as `∑_n Γ(p) / (c * (n + 1)) ^ p`.
* `TauCeti.integral_Ioi_rpow_div_exp_mul_sub_one`: evaluation as
  `Γ(p) / c ^ p * ∑' n : ℕ, 1 / (n + 1) ^ p`.
* `TauCeti.integral_Ioi_pow_div_exp_mul_sub_one`: closed form at odd integer exponents `2 * s - 1`
  in terms of `bernoulli (2 * s)`.
* `TauCeti.integral_Ioi_pow_div_exp_two_pi_mul_sub_one` and
  `TauCeti.integral_Ioi_div_exp_two_pi_mul_sub_one`: specializations to `c = 2 * π`.

## References

* NIST *Digital Library of Mathematical Functions*, §25.5(i), formula 25.5.1, and §2.10(i),
  formula 2.10.2.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §3.3.
-/

public section

namespace TauCeti

open Filter Finset MeasureTheory Real Set
open scoped Nat Topology

/-- Pointwise geometric series expansion `y ^ (p - 1) / (exp (c * y) - 1) =
∑_n y ^ (p - 1) * exp (-c * (n + 1) * y)` for `c > 0` and `y > 0`. -/
private theorem hasSum_rpow_mul_exp_neg_mul {p c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    HasSum (fun n : ℕ => y ^ (p - 1) * exp (-(c * (n + 1) * y)))
      (y ^ (p - 1) / (exp (c * y) - 1)) := by
  have hcy : 0 < c * y := mul_pos hc hy
  have hr0 : 0 ≤ exp (-(c * y)) := (exp_pos _).le
  have hr1 : exp (-(c * y)) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hcy)
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (y ^ (p - 1) * exp (-(c * y)))
  convert hgeom using 1
  · ext n
    rw [← exp_nat_mul, mul_assoc (y ^ (p - 1)), ← exp_add]
    ring_nf
  · have hexp_ne : exp (c * y) - 1 ≠ 0 := sub_ne_zero.mpr (one_lt_exp_iff.mpr hcy).ne'
    have h1 : 1 - exp (-(c * y)) ≠ 0 := sub_ne_zero.mpr hr1.ne'
    symm
    rw [mul_inv_eq_iff_eq_mul₀ h1]
    calc
      y ^ (p - 1) * exp (-(c * y)) =
          y ^ (p - 1) / (exp (c * y) - 1) * ((exp (c * y) - 1) * exp (-(c * y))) := by
        field_simp
      _ = y ^ (p - 1) / (exp (c * y) - 1) * (1 - exp (-(c * y))) := by
        congr 1
        rw [sub_mul, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- For `p > 1` and `c > 0`, the Bose–Einstein integrand `y ^ (p - 1) / (exp (c * y) - 1)` is
integrable on `(0, ∞)`. -/
theorem integrableOn_rpow_div_exp_mul_sub_one {p c : ℝ} (hp : 1 < p) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ (p - 1) / (exp (c * y) - 1)) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ => y ^ (p - 1) / (exp (c * y) - 1))
      (volume.restrict (Ioi 0)) := by
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  -- Near `0`, `exp (c * y) - 1 ≥ c * y`, bounding the integrand by `c⁻¹ * y ^ (p - 2)`.
  have hzero_major : IntegrableOn (fun y : ℝ => c⁻¹ * y ^ (p - 2)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)).const_mul c⁻¹
  have hzero : IntegrableOn (fun y : ℝ => y ^ (p - 1) / (exp (c * y) - 1)) (Ioo 0 1) := by
    refine hzero_major.mono' (hmeas.mono_set Ioo_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hy0 : 0 < y := hy.1
    have hcy : 0 < c * y := mul_pos hc hy0
    have hden_ge : c * y ≤ exp (c * y) - 1 := by linarith [add_one_le_exp (c * y)]
    have hden_pos : 0 < exp (c * y) - 1 := hcy.trans_le hden_ge
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (rpow_nonneg hy0.le _) hden_pos.le)]
    calc
      y ^ (p - 1) / (exp (c * y) - 1) ≤ y ^ (p - 1) / (c * y) := by gcongr
      _ = c⁻¹ * (y ^ (p - 1) * y ^ (-1 : ℝ)) := by
        rw [rpow_neg_one, div_eq_mul_inv, mul_inv]
        ring
      _ = c⁻¹ * y ^ (p - 2) := by
        rw [← rpow_add hy0]
        ring_nf
  -- On `[1, ∞)`, `exp (c * y) - 1 ≥ (1 - exp (-c)) * exp (c * y)`.
  have h1exp : 0 < 1 - exp (-c) := sub_pos.mpr (exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have htop_major : IntegrableOn
      (fun y : ℝ => (1 - exp (-c))⁻¹ * (y ^ (p - 1) * exp (-c * y))) (Ioi 1) := by
    have hgamma := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := p - 1) (b := c)
      (by linarith) zero_lt_one hc
    simp only [rpow_one] at hgamma
    exact (hgamma.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
  have htop_Ioi : IntegrableOn (fun y : ℝ => y ^ (p - 1) / (exp (c * y) - 1)) (Ioi 1) := by
    refine htop_major.mono' (hmeas.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := zero_lt_one.trans hy
    have hcy : 0 < c * y := mul_pos hc hy0
    have hexp_le : exp (-c * y) ≤ exp (-c) :=
      exp_le_exp.mpr (by nlinarith [hy.le])
    have hden_ge : (1 - exp (-c)) * exp (c * y) ≤ exp (c * y) - 1 := by
      calc
        (1 - exp (-c)) * exp (c * y) ≤ (1 - exp (-c * y)) * exp (c * y) := by gcongr
        _ = exp (c * y) - 1 := by
          rw [sub_mul, one_mul, neg_mul, ← exp_add, neg_add_cancel, exp_zero]
    have hden_pos : 0 < exp (c * y) - 1 := sub_pos.mpr (one_lt_exp_iff.mpr hcy)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (rpow_nonneg hy0.le _) hden_pos.le)]
    calc
      y ^ (p - 1) / (exp (c * y) - 1) ≤ y ^ (p - 1) / ((1 - exp (-c)) * exp (c * y)) := by
        gcongr
      _ = (1 - exp (-c))⁻¹ * (y ^ (p - 1) * exp (-c * y)) := by
        rw [div_eq_mul_inv, mul_inv, ← exp_neg, neg_mul]
        ring
  have htop : IntegrableOn (fun y : ℝ => y ^ (p - 1) / (exp (c * y) - 1)) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 htop_Ioi
  rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
  exact hzero.union htop

/-- Natural-power specialization of `integrableOn_rpow_div_exp_mul_sub_one`: for `1 ≤ k` and
`c > 0`, `y ^ k / (exp (c * y) - 1)` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_div_exp_mul_sub_one {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ k / (exp (c * y) - 1)) (Ioi 0) := by
  have hp : (1 : ℝ) < k + 1 := by exact_mod_cast Nat.succ_lt_succ hk
  refine (integrableOn_rpow_div_exp_mul_sub_one hp hc).congr_fun ?_ measurableSet_Ioi
  intro y _
  dsimp only
  rw [add_sub_cancel_right, rpow_natCast]

/-- Series evaluation of the Bose–Einstein integral: for `p > 1` and `c > 0`,
`∫ y in Ioi 0, y ^ (p - 1) / (exp (c * y) - 1)` is the sum of `Γ(p) / (c * (n + 1)) ^ p` over
`n : ℕ`. -/
theorem hasSum_integral_Ioi_rpow_div_exp_mul_sub_one {p c : ℝ} (hp : 1 < p) (hc : 0 < c) :
    HasSum (fun n : ℕ => Gamma p / (c * (n + 1)) ^ p)
      (∫ y in Ioi (0 : ℝ), y ^ (p - 1) / (exp (c * y) - 1)) := by
  let F : ℕ → ℝ → ℝ := fun n y => y ^ (p - 1) * exp (-(c * (n + 1)) * y)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Ioi 0)) := fun n => by
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  have hF_nonneg : ∀ n, ∀ᵐ y ∂volume.restrict (Ioi 0), 0 ≤ F n y := fun n => by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (rpow_nonneg (mem_Ioi.mp hy).le _) (exp_pos _).le
  have h_bound : ∀ n, ∀ᵐ y ∂volume.restrict (Ioi 0), ‖F n y‖ ≤ F n y := fun n => by
    filter_upwards [hF_nonneg n] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg hy]
  have h_lim : ∀ᵐ y ∂volume.restrict (Ioi 0),
      HasSum (fun n => F n y) (y ^ (p - 1) / (exp (c * y) - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa [F, neg_mul] using hasSum_rpow_mul_exp_neg_mul hc hy
  have bound_summable : ∀ᵐ y ∂volume.restrict (Ioi 0), Summable fun n => F n y := by
    filter_upwards [h_lim] with y hy
    exact hy.summable
  have bound_integrable : Integrable (fun y => ∑' n, F n y) (volume.restrict (Ioi 0)) := by
    refine (integrableOn_rpow_div_exp_mul_sub_one hp hc).congr ?_
    filter_upwards [h_lim] with y hy
    exact hy.tsum_eq.symm
  have hsum := hasSum_integral_of_dominated_convergence F hF_meas h_bound bound_summable
    bound_integrable h_lim
  convert hsum using 2 with n
  have hcn : 0 < c * (n + 1) := by positivity
  have hterm := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := p - 1) (b := c * (n + 1))
    zero_lt_one (by linarith) hcn
  simp only [rpow_one, sub_add_cancel, div_one] at hterm
  simpa [F, rpow_neg hcn.le, div_eq_inv_mul] using hterm.symm

/-- Evaluation of the Bose–Einstein integral in terms of `Real.Gamma` and the series
`∑' n : ℕ, 1 / (n + 1) ^ p`. -/
theorem integral_Ioi_rpow_div_exp_mul_sub_one {p c : ℝ} (hp : 1 < p) (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), y ^ (p - 1) / (exp (c * y) - 1) =
      Gamma p / c ^ p * ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ p := by
  have hsum := hasSum_integral_Ioi_rpow_div_exp_mul_sub_one hp hc
  have hconst : Gamma p / c ^ p ≠ 0 :=
    div_ne_zero (Gamma_pos_of_pos (by linarith)).ne' (by positivity)
  have hrewrite : (fun n : ℕ => Gamma p / (c * (n + 1)) ^ p) =
      fun n : ℕ => (Gamma p / c ^ p) * (1 / (n + 1 : ℝ) ^ p) := by
    ext n
    rw [mul_rpow hc.le (by positivity)]
    ring
  rw [hrewrite] at hsum
  have hzeta : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ p) :=
    (summable_mul_left_iff hconst).mp hsum.summable
  exact hsum.unique (hzeta.hasSum.mul_left (Gamma p / c ^ p))

/-- Closed-form evaluation of the odd-moment Bose–Einstein integral: for `s ≥ 1` and `c > 0`,
`∫ y in Ioi 0, y ^ (2 * s - 1) / (exp (c * y) - 1) =
  (-1) ^ (s + 1) * (2 * π / c) ^ (2 * s) * bernoulli (2 * s) / (4 * s)`. -/
theorem integral_Ioi_pow_div_exp_mul_sub_one {s : ℕ} (hs : 1 ≤ s) {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * s - 1) / (exp (c * y) - 1) =
      (-1 : ℝ) ^ (s + 1) * (2 * π / c) ^ (2 * s) * bernoulli (2 * s) / (4 * s) := by
  have hs0 : s ≠ 0 := by omega
  have hp : (1 : ℝ) < (2 * s : ℕ) := by
    have : 2 ≤ 2 * s := by omega
    exact_mod_cast Nat.lt_of_lt_of_le one_lt_two this
  have hcongr : ∫ y in Ioi (0 : ℝ), y ^ (2 * s - 1) / (exp (c * y) - 1) =
      ∫ y in Ioi (0 : ℝ), y ^ (((2 * s : ℕ) : ℝ) - 1) / (exp (c * y) - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    have hcast : ((2 * s : ℕ) : ℝ) - 1 = ((2 * s - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast, rpow_natCast]
  rw [hcongr, integral_Ioi_rpow_div_exp_mul_sub_one hp hc]
  -- Evaluate `∑' n : ℕ, 1 / (n + 1) ^ (2 * s)` from `hasSum_zeta_nat`.
  have hzeta0 := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat hs0)
  simp only [Finset.range_one, sum_singleton, Nat.cast_zero, zero_pow (by positivity : 2 * s ≠ 0),
    div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at hzeta0
  have htsum : (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ ((2 * s : ℕ) : ℝ)) =
      (-1 : ℝ) ^ (s + 1) * (2 : ℝ) ^ (2 * s - 1) * π ^ (2 * s) *
        bernoulli (2 * s) / (2 * s)! := by
    simp_rw [rpow_natCast]
    exact hzeta0.tsum_eq
  rw [htsum, rpow_natCast]
  have hGamma : Gamma ((2 * s : ℕ) : ℝ) = ((2 * s - 1)! : ℝ) := by
    have h2s : ((2 * s : ℕ) : ℝ) = ((2 * s - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel]
    rw [h2s, Gamma_nat_eq_factorial]
  have hfact : ((2 * s)! : ℝ) = (2 * s : ℝ) * ((2 * s - 1)! : ℝ) := by
    conv_lhs => rw [show 2 * s = (2 * s - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    rw [show ((2 * s - 1 : ℕ) : ℝ) + 1 = 2 * (s : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
  have hpow2 : (2 : ℝ) ^ (2 * s) = 2 * (2 : ℝ) ^ (2 * s - 1) := by
    conv_lhs => rw [show 2 * s = 1 + (2 * s - 1) by omega, pow_add, pow_one]
  have hfac_ne : ((2 * s - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs_ne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs0
  rw [hGamma, div_pow, mul_pow, hpow2, hfact]
  field_simp
  ring

/-- Specialization of `integral_Ioi_pow_div_exp_mul_sub_one` to `c = 2 * π`, the kernel appearing
in the Abel–Plana formula: `∫ y in Ioi 0, y ^ (2 * s - 1) / (exp (2 * π * y) - 1) =
(-1) ^ (s + 1) * bernoulli (2 * s) / (4 * s)`. -/
theorem integral_Ioi_pow_div_exp_two_pi_mul_sub_one {s : ℕ} (hs : 1 ≤ s) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * s - 1) / (exp (2 * π * y) - 1) =
      (-1 : ℝ) ^ (s + 1) * bernoulli (2 * s) / (4 * s) := by
  rw [integral_Ioi_pow_div_exp_mul_sub_one hs two_pi_pos, div_self two_pi_pos.ne', one_pow,
    mul_one]

/-- The first odd moment (`s = 1`) for the Abel–Plana kernel:
`∫ y in Ioi 0, y / (exp (2 * π * y) - 1) = 1 / 24`. -/
theorem integral_Ioi_div_exp_two_pi_mul_sub_one :
    ∫ y in Ioi (0 : ℝ), y / (exp (2 * π * y) - 1) = 1 / 24 := by
  have h := integral_Ioi_pow_div_exp_two_pi_mul_sub_one (s := 1) le_rfl
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two] at h
  simpa using (h.trans (by norm_num))

end TauCeti
