/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Envelope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.NumberTheory.ZetaValues

/-!
# Stieltjes representation and higher derivatives of the Stirling remainder

On the slit plane `ℂ ∖ (-∞, 0]`, the remainder
`stirlingRemainder z = logGamma z - ((z - 1 / 2) * log z - z + log (2π) / 2)`
in Stirling's formula is given by the periodic-quadratic Stieltjes integral
`stirlingRemainder z = ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ 2 dt`.

Specializing `TauCeti.iteratedDeriv_stirlingSeriesRemainder` at `n = 1` yields, for every `j : ℕ`
and `z ∈ slitPlane`,
`iteratedDeriv j stirlingRemainder z =
  (-1) ^ j * (j + 1)! * ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt`.

Combined with the sharp `1 / 12` half-angle bounds
`TauCeti.norm_iteratedDeriv_stirlingRemainder_lt` and
`TauCeti.norm_iteratedDeriv_stirlingRemainder_lt_of_abs_arg_le`
(`TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Envelope.lean`), on any closed sector
`|arg z| ≤ π - δ` (`0 < δ`, `z ≠ 0`) this gives
`‖iteratedDeriv j stirlingRemainder z‖ < j! / (12 * sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`,
and hence `iteratedDeriv j stirlingRemainder =O ‖z‖ ^ (-(j + 1))` as `z → ∞` in the sector.
Along the positive real axis `(0, ∞)`, `iteratedDeriv j stirlingRemainder` is real-valued and
strictly alternates in sign: `0 < (-1) ^ j * (iteratedDeriv j stirlingRemainder x).re <
j! / (12 * x ^ (j + 1))`; in particular `(stirlingRemainder x).re > 0` and
`(deriv stirlingRemainder x).re < 0` for `x > 0`.

## Main declarations

* `TauCeti.iteratedDeriv_stirlingRemainder`, `TauCeti.iteratedDeriv_succ_stirlingRemainder`,
  `TauCeti.deriv_stirlingRemainder_eq_integral`: integral representation of all iterated
  derivatives of `stirlingRemainder` (extending `TauCeti.stirlingRemainder_eq_integral`) and
  identification with iterated derivatives of `digamma z - log z + (2 * z)⁻¹`.
* `TauCeti.norm_deriv_stirlingRemainder_lt`,
  `TauCeti.exists_norm_iteratedDeriv_stirlingRemainder_le`,
  `TauCeti.isBigO_iteratedDeriv_stirlingRemainder`: `j = 1` specialization of
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_lt`, existential sector bound, and asymptotic
  `O(‖z‖ ^ (-(j + 1)))` bound for all `j : ℕ`.
* `TauCeti.iteratedDeriv_stirlingRemainder_ofReal_im`,
  `TauCeti.iteratedDeriv_stirlingRemainder_ofReal_re`,
  `TauCeti.neg_one_pow_mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos`,
  `TauCeti.neg_one_pow_mul_iteratedDeriv_stirlingRemainder_ofReal_re_lt`,
  `TauCeti.stirlingRemainder_ofReal_re_pos`, `TauCeti.stirlingRemainder_ofReal_re_lt`,
  `TauCeti.deriv_stirlingRemainder_ofReal_re_neg`: real-valuedness, strict sign alternation, and
  sharp `1 / 12` upper bounds on `(0, ∞)`.

## References

* G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, Proc. Roy. Soc. Edinburgh Sect. A **145** (2015), 571–596, §2
  (eq. (2.5) and Lemma 2.1).
* [F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §5.11](https://dlmf.nist.gov/5.11).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., §12.33.
-/

public section

open Complex Real Filter Set Topology MeasureTheory Asymptotics Bornology

namespace TauCeti

/-! ### Iterated derivatives of `stirlingRemainder` -/

/-- Integral representation of all higher derivatives of the Stirling remainder on the slit plane:
for every `j : ℕ` and `z ∈ slitPlane`,
`iteratedDeriv j stirlingRemainder z =
  (-1) ^ j * (j + 1)! * ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt`. -/
theorem iteratedDeriv_stirlingRemainder (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv j stirlingRemainder z = (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
      ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2) := by
  rw [← stirlingSeriesRemainder_one, iteratedDeriv_stirlingSeriesRemainder le_rfl j hz]
  have hidx : 2 * 1 + j - 1 = j + 1 := by omega
  have hpow : 2 * 1 + j = j + 2 := by omega
  rw [hidx, hpow, Nat.mul_one]
  have hcoe : (-1 : ℂ) ^ j * (((j + 1).factorial : ℂ) / ((2 : ℕ).factorial : ℂ)) *
      ∫ u in Ioi (0 : ℝ),
        (((bernoulli 2 : ℝ) - bernoulliFun 2 (Int.fract u) : ℝ) : ℂ) / ((u : ℂ) + z) ^ (j + 2) =
      (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
        ((2 : ℂ)⁻¹ * ∫ u in Ioi (0 : ℝ),
          (((bernoulli 2 : ℝ) - bernoulliFun 2 (Int.fract u) : ℝ) : ℂ) /
            ((u : ℂ) + z) ^ (j + 2)) := by
    rw [Nat.factorial_two, Nat.cast_ofNat]; ring
  rw [hcoe, ← MeasureTheory.integral_const_mul]
  refine congr_arg (_ * ·) (setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_)
  rw [bernoulli_two, bernoulliFun_two]
  push_cast
  rw [add_comm (t : ℂ) z]
  ring

/-- For `j : ℕ` and `z ∈ slitPlane`, the `(j + 1)`-st derivative of `stirlingRemainder` coincides
with the `j`-th derivative of `w ↦ digamma w - log w + (2 * w)⁻¹`. -/
theorem iteratedDeriv_succ_stirlingRemainder (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv (j + 1) stirlingRemainder z =
      iteratedDeriv j (fun w ↦ Complex.digamma w - Complex.log w + (2 * w)⁻¹) z := by
  rw [iteratedDeriv_succ']
  exact EqOn.iteratedDeriv_of_isOpen (fun _ hw ↦ deriv_stirlingRemainder hw) isOpen_slitPlane j hz

/-- Explicit Stieltjes integral formula for `deriv stirlingRemainder` on the slit plane. -/
theorem deriv_stirlingRemainder_eq_integral {z : ℂ} (hz : z ∈ slitPlane) :
    deriv stirlingRemainder z =
      -2 * ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ 3 := by
  simpa [iteratedDeriv_one] using iteratedDeriv_stirlingRemainder 1 hz

/-! ### Sector bounds and asymptotics for `stirlingRemainder` and its derivatives -/

/-- Sharp `1 / 12` slit-plane bound for `deriv stirlingRemainder` (`j = 1`):
`‖deriv stirlingRemainder z‖ < 1 / (12 * cos (arg z / 2) ^ 3 * ‖z‖ ^ 2)` for `z ∈ slitPlane`. -/
theorem norm_deriv_stirlingRemainder_lt {z : ℂ} (hz : z ∈ slitPlane) :
    ‖deriv stirlingRemainder z‖ < 1 / (12 * Real.cos (z.arg / 2) ^ 3 * ‖z‖ ^ 2) := by
  simpa [iteratedDeriv_one] using norm_iteratedDeriv_stirlingRemainder_lt 1 hz

/-- Existential sector bound for higher derivatives of `stirlingRemainder`: for every `j : ℕ` and
`0 < δ`, there exists `C > 0` with `‖iteratedDeriv j stirlingRemainder z‖ ≤ C / ‖z‖ ^ (j + 1)`
whenever `|arg z| ≤ π - δ` and `z ≠ 0`. -/
theorem exists_norm_iteratedDeriv_stirlingRemainder_le (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ z : ℂ, |z.arg| ≤ π - δ → z ≠ 0 →
      ‖iteratedDeriv j stirlingRemainder z‖ ≤ C / ‖z‖ ^ (j + 1) := by
  rcases le_or_gt δ π with hδπ | hπδ
  · have hsin : 0 < Real.sin (δ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (half_pos hδ) (by linarith [Real.pi_pos])
    refine ⟨(j.factorial : ℝ) / (12 * Real.sin (δ / 2) ^ (j + 2)),
      div_pos (Nat.cast_pos.mpr (Nat.factorial_pos j)) (by positivity),
      fun z hz hz0 ↦ ?_⟩
    rw [div_div]
    exact (norm_iteratedDeriv_stirlingRemainder_lt_of_abs_arg_le j hδ hz hz0).le
  · exact ⟨1, one_pos, fun z hz _ ↦ False.elim (by linarith [abs_nonneg z.arg])⟩

/-- Asymptotic `O(‖z‖ ^ (-(j + 1)))` bound for the `j`-th derivative of `stirlingRemainder` as
`z → ∞` in any closed sector `|arg z| ≤ π - δ` (`0 < δ`). -/
theorem isBigO_iteratedDeriv_stirlingRemainder (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    iteratedDeriv j stirlingRemainder
      =O[cobounded ℂ ⊓ 𝓟 {z : ℂ | |z.arg| ≤ π - δ}] fun z : ℂ ↦ (‖z‖ ^ (j + 1))⁻¹ := by
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedDeriv_stirlingRemainder_le j hδ
  refine IsBigO.of_bound C ?_
  rw [eventually_inf_principal]
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz0 hz
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg z) _)), ← div_eq_mul_inv]
  exact hC z hz (norm_pos_iff.mp hz0)

/-! ### Positive real axis: real-valuedness and strict sign alternation -/

/-- For every `j : ℕ` and `0 < x`, `iteratedDeriv j stirlingRemainder x` is real-valued. -/
theorem iteratedDeriv_stirlingRemainder_ofReal_im (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (iteratedDeriv j stirlingRemainder x).im = 0 := by
  rw [← stirlingSeriesRemainder_one, iteratedDeriv_stirlingSeriesRemainder_ofReal 1 j hx, ofReal_im]

/-- Real integral representation of `(iteratedDeriv j stirlingRemainder x).re` for `0 < x`. -/
theorem iteratedDeriv_stirlingRemainder_ofReal_re (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (iteratedDeriv j stirlingRemainder x).re =
      (-1 : ℝ) ^ j * ((j + 1).factorial : ℝ) *
        ∫ t : ℝ in Ioi 0, ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) := by
  rw [iteratedDeriv_stirlingRemainder j (ofReal_mem_slitPlane.mpr hx)]
  have hint :
      ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + t) ^ (j + 2) =
        ((∫ t : ℝ in Ioi 0,
          ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t _ ↦
      show (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + t) ^ (j + 2) =
          ((((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) by
        simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add]]
    exact integral_ofReal
  rw [hint]
  norm_cast

/-- Strict sign alternation of the Stirling remainder and its derivatives on `(0, ∞)`:
for every `j : ℕ` and `0 < x`, `0 < (-1) ^ j * (iteratedDeriv j stirlingRemainder x).re`. -/
theorem neg_one_pow_mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos (j : ℕ) {x : ℝ}
    (hx : 0 < x) :
    0 < (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re := by
  rw [← stirlingSeriesRemainder_one, iteratedDeriv_stirlingSeriesRemainder_ofReal 1 j hx, ofReal_re]
  exact neg_one_pow_mul_iteratedDeriv_realStirlingSeriesRemainder_odd_pos 0 j hx

/-- Sharp upper bound on `(-1) ^ j * (iteratedDeriv j stirlingRemainder x).re` for `0 < x`:
`(-1) ^ j * (iteratedDeriv j stirlingRemainder x).re < j! / (12 * x ^ (j + 1))`. -/
theorem neg_one_pow_mul_iteratedDeriv_stirlingRemainder_ofReal_re_lt (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re <
      (j.factorial : ℝ) / (12 * x ^ (j + 1)) := by
  have hb : ‖iteratedDeriv j stirlingRemainder x‖ < (j.factorial : ℝ) / (12 * x ^ (j + 1)) := by
    simpa [arg_ofReal_of_nonneg hx.le, abs_of_pos hx] using
      norm_iteratedDeriv_stirlingRemainder_lt j (ofReal_mem_slitPlane.mpr hx)
  calc
    (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re
        ≤ |(-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re| := le_abs_self _
    _ = |(iteratedDeriv j stirlingRemainder x).re| := by simp
    _ ≤ ‖iteratedDeriv j stirlingRemainder x‖ := abs_re_le_norm _
    _ < (j.factorial : ℝ) / (12 * x ^ (j + 1)) := hb

/-- On `(0, ∞)` the Stirling remainder has strictly positive real part. -/
theorem stirlingRemainder_ofReal_re_pos {x : ℝ} (hx : 0 < x) :
    0 < (stirlingRemainder x).re := by
  simpa [iteratedDeriv_zero] using
    neg_one_pow_mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos 0 hx

/-- On `(0, ∞)` the Stirling remainder satisfies `(stirlingRemainder x).re < 1 / (12 * x)`. -/
theorem stirlingRemainder_ofReal_re_lt {x : ℝ} (hx : 0 < x) :
    (stirlingRemainder x).re < 1 / (12 * x) := by
  simpa [iteratedDeriv_zero] using
    neg_one_pow_mul_iteratedDeriv_stirlingRemainder_ofReal_re_lt 0 hx

/-- On `(0, ∞)`, `deriv stirlingRemainder` has strictly negative real part:
`(deriv stirlingRemainder x).re < 0` for `0 < x`. -/
theorem deriv_stirlingRemainder_ofReal_re_neg {x : ℝ} (hx : 0 < x) :
    (deriv stirlingRemainder x).re < 0 := by
  have h := neg_one_pow_mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos 1 hx
  rw [pow_one, iteratedDeriv_one, neg_one_mul, neg_pos] at h
  exact h

end TauCeti
