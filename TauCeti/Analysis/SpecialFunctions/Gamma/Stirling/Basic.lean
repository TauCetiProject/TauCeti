/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
public import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.Sectorial
public import Mathlib.Analysis.SpecialFunctions.Stirling
import TauCeti.Analysis.SpecialFunctions.Integrals.PeriodicStieltjes

/-!
# Stirling's formula on sectors

On the slit plane `ℂ ∖ (-∞, 0]`, the remainder
`stirlingRemainder z = logGamma z - ((z - 1 / 2) * log z - z + log (2π) / 2)`
in Stirling's formula (with `log` the principal branch) satisfies the periodic-quadratic Stieltjes
integral representation
`stirlingRemainder z = ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ 2 dt`
(`TauCeti.stirlingRemainder_eq_integral`).

The proof identifies the derivative of `stirlingRemainder` with `ψ(z) - log z + 1 / (2z)`, matches
it to the derivative of the Stieltjes integral via
`Complex.digamma_sub_log_add_inv_two_mul_eq_integral` and
`TauCeti.hasDerivAt_integral_fract_sub_fract_sq_div_add_pow`, and fixes the additive constant at
`0` by letting `z = n + 1 → ∞` using Stirling's formula for `n!`
(`Stirling.tendsto_log_factorial_sub_stirling`).

Combining the Stieltjes representation with
`TauCeti.norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le` yields Nemes's explicit bounds
`‖stirlingRemainder z‖ ≤ 1 / (8 * cos (arg z / 2) ^ 2 * ‖z‖)` on `slitPlane` and
`‖stirlingRemainder z‖ ≤ 1 / (8 * sin (δ / 2) ^ 2 * ‖z‖)` on every closed sector `|arg z| ≤ π - δ`
(`0 < δ`, `z ≠ 0`). Taking real parts gives the corresponding bound for `log ‖Γ s‖`, whose
consequence on vertical strips is in
`TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Vertical.lean`. Higher derivatives and positive-
axis sign alternation are in `TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Remainder.lean`.

## Main declarations

* `Stirling.tendsto_log_factorial_sub_stirling`: the logarithmic form of Stirling's formula at
  `n + 1`.
* `TauCeti.stirlingRemainder`: the remainder `logGamma s - ((s - 1/2) log s - s + log (2π) / 2)`
  in Stirling's formula on the slit plane, together with its real-part and positive-real
  evaluations (`TauCeti.stirlingRemainder_re`, `TauCeti.stirlingRemainder_ofReal`), derivative,
  conjugation symmetry, shift identity, and vanishing limit at positive integers.
* `TauCeti.stirlingRemainder_eq_integral`: Stieltjes integral representation of
  `stirlingRemainder` on `slitPlane`.
* `TauCeti.norm_stirlingRemainder_le`, `TauCeti.norm_stirlingRemainder_le_of_abs_arg_le`: Nemes's
  explicit slit-plane and closed-sector bounds for `stirlingRemainder`.
* `TauCeti.abs_log_norm_Gamma_sub_stirling_le`: the real-part form for `log ‖Γ s‖`.

## References

* G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, Proc. Roy. Soc. Edinburgh Sect. A **145** (2015), 571–596, §2
  (eq. (2.5) and Lemma 2.1).
* [F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §5.11](https://dlmf.nist.gov/5.11).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., §12.33.
-/

public section

open Complex Real Filter Set Topology MeasureTheory

namespace Stirling

/-- Stirling's formula in logarithmic form at `n + 1`:
`log n! - ((n + 1/2) log (n + 1) - (n + 1) + log (2π) / 2) → 0`. -/
theorem tendsto_log_factorial_sub_stirling :
    Tendsto (fun n : ℕ ↦ Real.log (n.factorial : ℝ) -
      (((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1) - ((n : ℝ) + 1) + Real.log (2 * π) / 2))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.log (stirlingSeq n)) atTop (𝓝 (Real.log √π)) :=
    (continuousAt_log (by positivity)).tendsto.comp tendsto_stirlingSeq_sqrt_pi
  have hm : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log (1 + 1 / (n : ℝ))) atTop (𝓝 1) :=
    (tendsto_mul_log_one_add_div_atTop 1).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ ↦ Real.log (1 + 1 / (n : ℝ))) atTop (𝓝 0) := by
    have h := ((continuousAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)).tendsto.comp
      ((tendsto_one_div_atTop_nhds_zero_nat).const_add (1 : ℝ)))
    simpa [Function.comp_def] using h
  have hlim := ((hs.sub_const (Real.log π / 2)).sub hm).sub (hl.const_mul (1 / 2)) |>.add_const 1
  rw [Real.log_sqrt pi_pos.le] at hlim
  simp only [mul_zero, sub_zero] at hlim
  rw [show Real.log π / 2 - Real.log π / 2 - 1 + 1 = 0 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [log_stirlingSeq_formula, show (1 : ℝ) + 1 / n = (n + 1) / n by field_simp,
    Real.log_div (by positivity) hn0.ne', Real.log_mul two_ne_zero hn0.ne',
    Real.log_div hn0.ne' (exp_pos 1).ne', Real.log_exp, Real.log_mul two_ne_zero pi_ne_zero]
  ring

end Stirling

namespace TauCeti

/-- The remainder in Stirling's asymptotic expansion of the normalized logarithm of Gamma:
`stirlingRemainder s = logGamma s - ((s - 1 / 2) * log s - s + log (2π) / 2)`. -/
noncomputable def stirlingRemainder (s : ℂ) : ℂ :=
  logGamma s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * π) / 2 : ℝ))

/-- Unfolding formula for `TauCeti.stirlingRemainder`. -/
theorem stirlingRemainder_def (s : ℂ) :
    stirlingRemainder s =
      logGamma s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * π) / 2 : ℝ)) := by
  rfl

/-- Decomposition of `logGamma` into Stirling's main term plus `stirlingRemainder`. -/
theorem logGamma_eq_add_stirlingRemainder (s : ℂ) :
    logGamma s = (s - 1 / 2) * Complex.log s - s + (Real.log (2 * π) / 2 : ℝ) +
      stirlingRemainder s := by
  rw [stirlingRemainder_def]
  ring

/-- At `1`, `stirlingRemainder 1 = 1 - log (2π) / 2`. -/
@[simp]
theorem stirlingRemainder_one : stirlingRemainder 1 = 1 - (Real.log (2 * π) / 2 : ℝ) := by
  simp [stirlingRemainder_def]
  ring

/-- The derivative of `stirlingRemainder` on the slit plane is `ψ(z) - log z + 1 / (2z)`. -/
theorem hasDerivAt_stirlingRemainder {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt stirlingRemainder (digamma z - Complex.log z + (2 * z)⁻¹) z := by
  have hz0 := slitPlane_ne_zero hz
  have h := (hasDerivAt_logGamma hz).sub
    ((((hasDerivAt_id z).sub_const (1 / 2 : ℂ)).mul (Complex.hasDerivAt_log hz)).sub
      (hasDerivAt_id z) |>.add_const ((Real.log (2 * π) / 2 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- `stirlingRemainder` is complex differentiable on the slit plane. -/
theorem differentiableOn_stirlingRemainder : DifferentiableOn ℂ stirlingRemainder slitPlane :=
  fun _ hz ↦ (hasDerivAt_stirlingRemainder hz).differentiableAt.differentiableWithinAt

/-- `stirlingRemainder` is complex analytic at every point of the slit plane. -/
theorem analyticOnNhd_stirlingRemainder : AnalyticOnNhd ℂ stirlingRemainder slitPlane :=
  differentiableOn_stirlingRemainder.analyticOnNhd isOpen_slitPlane

/-- Formula for `deriv stirlingRemainder` on the slit plane. -/
theorem deriv_stirlingRemainder {z : ℂ} (hz : z ∈ slitPlane) :
    deriv stirlingRemainder z = digamma z - Complex.log z + (2 * z)⁻¹ :=
  (hasDerivAt_stirlingRemainder hz).deriv

/-- `stirlingRemainder` commutes with complex conjugation on the slit plane. -/
theorem stirlingRemainder_conj {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder ((starRingEnd ℂ) z) = (starRingEnd ℂ) (stirlingRemainder z) := by
  rw [stirlingRemainder_def, stirlingRemainder_def, logGamma_conj hz,
    Complex.log_conj z (slitPlane_arg_ne_pi hz)]
  simp [map_ofNat]

/-- On the slit plane, the real part of `stirlingRemainder z` is the error in Stirling's formula
for `log ‖Γ z‖`. -/
theorem stirlingRemainder_re {z : ℂ} (hz : z ∈ slitPlane) :
    (stirlingRemainder z).re =
      Real.log ‖Complex.Gamma z‖ -
        ((z.re - 1 / 2) * Real.log ‖z‖ - z.im * z.arg - z.re + Real.log (2 * π) / 2) := by
  rw [stirlingRemainder_def, sub_re, logGamma_re hz]
  simp only [sub_re, add_re, mul_re, log_re, log_im, ofReal_re, sub_im, one_div, inv_re,
    normSq_ofNat, re_ofNat]
  norm_num

/-- On the positive real axis, `stirlingRemainder x` is the real logarithmic Stirling remainder
cast to `ℂ`. -/
theorem stirlingRemainder_ofReal {x : ℝ} (hx : 0 < x) :
    stirlingRemainder x =
      ((Real.log (Real.Gamma x) -
        ((x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2) : ℝ) : ℂ) := by
  rw [stirlingRemainder_def, logGamma_ofReal hx, ← ofReal_log hx.le]
  push_cast
  ring

/-- On the positive real axis, `stirlingRemainder` is real-valued. -/
theorem stirlingRemainder_ofReal_im {x : ℝ} (hx : 0 < x) :
    (stirlingRemainder x).im = 0 := by
  rw [stirlingRemainder_ofReal hx, ofReal_im]

/-- Shift relation for `stirlingRemainder` under `z ↦ z + 1` on the slit plane. -/
theorem stirlingRemainder_add_one {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder (z + 1) =
      stirlingRemainder z + 1 - (z + 1 / 2) * (Complex.log (z + 1) - Complex.log z) := by
  rw [stirlingRemainder_def, stirlingRemainder_def, logGamma_add_one hz]
  ring

/-- At the positive integers `n + 1`, `stirlingRemainder (n + 1) → 0`: this is Stirling's formula
for `n!`. -/
theorem tendsto_stirlingRemainder_natCast_add_one :
    Tendsto (fun n : ℕ ↦ stirlingRemainder ((n : ℝ) + 1 : ℝ)) atTop (𝓝 0) := by
  have h := (continuous_ofReal.tendsto 0).comp Stirling.tendsto_log_factorial_sub_stirling
  rw [ofReal_zero] at h
  refine h.congr fun n ↦ ?_
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [Function.comp_apply, stirlingRemainder_ofReal hn, Real.Gamma_nat_eq_factorial]
  congr 1
  ring

/-- **Stieltjes integral representation of the Stirling remainder** (Nemes 2015, §2, eq. (2.5);
Whittaker and Watson, §12.33): for every `z ∈ slitPlane`,
`stirlingRemainder z = ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ 2 dt`. -/
theorem stirlingRemainder_eq_integral {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder z =
      ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ 2 := by
  let K : ℂ → ℂ := fun w ↦
    ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + t) ^ 2
  let d : ℂ → ℂ := fun w ↦ stirlingRemainder w - K w
  have hd_deriv : ∀ w ∈ slitPlane, HasDerivAt d 0 w := fun w hw ↦ by
    have h1 := hasDerivAt_stirlingRemainder hw
    have h2 : HasDerivAt K (-2 * ∫ t : ℝ in Ioi 0,
        (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + t) ^ 3) w :=
      (hasDerivAt_integral_fract_sub_fract_sq_div_add_pow hw 0).congr_deriv (by ring)
    have h3 := Complex.digamma_sub_log_add_inv_two_mul_eq_integral (Or.inl hw)
    have hd := h1.sub h2
    rw [h3, sub_self] at hd
    exact hd
  have hconn :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  have hconst : ∀ n : ℕ, d z = d ((n : ℝ) + 1 : ℝ) := fun n ↦ by
    have hn : (((n : ℝ) + 1 : ℝ) : ℂ) ∈ slitPlane :=
      ofReal_mem_slitPlane.mpr (by positivity)
    exact isOpen_slitPlane.is_const_of_deriv_eq_zero hconn
      (fun w hw ↦ (hd_deriv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hd_deriv w hw).deriv) hz hn
  have hk_lim : Tendsto (fun n : ℕ ↦ K ((n : ℝ) + 1 : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ ↦ (8 * ((n : ℝ) + 1))⁻¹) (fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_) ?_
    · have hn : (0 : ℝ) < n + 1 := by positivity
      have hb := norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le 0 (((n : ℝ) + 1 : ℝ) : ℂ)
      rw [arg_ofReal_of_nonneg hn.le, Complex.norm_real, Real.norm_of_nonneg hn.le] at hb
      simpa [K] using hb
    · refine tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop (by norm_num) ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hd_lim : Tendsto (fun n : ℕ ↦ d ((n : ℝ) + 1 : ℝ)) atTop (𝓝 0) := by
    simpa [d] using tendsto_stirlingRemainder_natCast_add_one.sub hk_lim
  have hd0 : d z = 0 := tendsto_const_nhds_iff.mp (hd_lim.congr fun n ↦ (hconst n).symm)
  exact sub_eq_zero.mp hd0

/-- Nemes's explicit slit-plane bound for the Stirling remainder:
`‖stirlingRemainder z‖ ≤ 1 / (8 * cos (arg z / 2) ^ 2 * ‖z‖)` for `z ∈ slitPlane`. -/
theorem norm_stirlingRemainder_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingRemainder z‖ ≤ 1 / (8 * Real.cos (z.arg / 2) ^ 2 * ‖z‖) := by
  rw [stirlingRemainder_eq_integral hz]
  simpa using norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le 0 z

/-- Nemes's explicit closed-sector bound for the Stirling remainder: for `0 < δ` and nonzero `z`
with `|arg z| ≤ π - δ`,
`‖stirlingRemainder z‖ ≤ 1 / (8 * sin (δ / 2) ^ 2 * ‖z‖)`. -/
theorem norm_stirlingRemainder_le_of_abs_arg_le {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingRemainder z‖ ≤ 1 / (8 * Real.sin (δ / 2) ^ 2 * ‖z‖) := by
  rw [stirlingRemainder_eq_integral (mem_slitPlane_of_abs_arg_le hδ hz hz0)]
  simpa using norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le_of_abs_arg_le 0 hδ hz

/-- Stirling's formula for `log ‖Γ s‖` on a sector: for `0 < δ` and nonzero `s` with
`|arg s| ≤ π - δ`,
`|log ‖Γ s‖ - ((re s - 1/2) log ‖s‖ - im s · arg s - re s + log (2π) / 2)| ≤
1 / (8 * sin (δ / 2) ^ 2 * ‖s‖)`. -/
theorem abs_log_norm_Gamma_sub_stirling_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hs : |s.arg| ≤ π - δ) (hs0 : s ≠ 0) :
    |Real.log ‖Complex.Gamma s‖ - ((s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg - s.re +
      Real.log (2 * π) / 2)| ≤ 1 / (8 * Real.sin (δ / 2) ^ 2 * ‖s‖) := by
  rw [← stirlingRemainder_re (mem_slitPlane_of_abs_arg_le hδ hs hs0)]
  exact (abs_re_le_norm _).trans (norm_stirlingRemainder_le_of_abs_arg_le hδ hs hs0)

end TauCeti
