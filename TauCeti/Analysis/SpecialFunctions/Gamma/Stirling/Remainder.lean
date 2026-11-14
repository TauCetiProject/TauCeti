/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.SpecialFunctions.Integrals.PeriodicStieltjes

/-!
# Stieltjes representation and higher derivatives of the Stirling remainder

On the slit plane `ℂ ∖ (-∞, 0]`, the remainder
`stirlingRemainder z = logGamma z - ((z - 1 / 2) * log z - z + log (2π) / 2)`
in Stirling's formula is given by the periodic-quadratic Stieltjes integral
`stirlingRemainder z = ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ 2 dt`.

Differentiating under the integral sign `j` times on `slitPlane`
(`TauCeti.hasDerivAt_integral_fract_sub_fract_sq_div_add_pow`) yields, for every `j : ℕ` and
`z ∈ slitPlane`,
`iteratedDeriv j stirlingRemainder z =
  (-1) ^ j * (j + 1)! * ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt`.

Combining `0 ≤ (fract t - fract t ^ 2) / 2 ≤ 1 / 8` with the sharp half-angle lower bound
`cos (arg z / 2) * (‖z‖ + t) ≤ ‖z + t‖` and the exact half-line evaluation
`∫_{t > 0} 1 / (a + t) ^ (j + 2) dt = 1 / ((j + 1) * a ^ (j + 1))`
(`TauCeti.norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le`) gives Nemes's explicit bound on
the whole slit plane:
`‖iteratedDeriv j stirlingRemainder z‖ ≤ j! / (8 * cos (arg z / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`.
On any closed sector `|arg z| ≤ π - δ` (`0 < δ`, `z ≠ 0`) this specializes to
`‖iteratedDeriv j stirlingRemainder z‖ ≤ j! / (8 * sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`,
and hence `iteratedDeriv j stirlingRemainder =O ‖z‖ ^ (-(j + 1))` as `z → ∞` in the sector.
Along the positive real axis `(0, ∞)`, `iteratedDeriv j stirlingRemainder` is real-valued and
strictly alternates in sign: `0 < (-1) ^ j * (iteratedDeriv j stirlingRemainder x).re ≤
j! / (8 * x ^ (j + 1))`; in particular `(stirlingRemainder x).re > 0` and
`(deriv stirlingRemainder x).re < 0` for `x > 0`.

## Main declarations

* `TauCeti.stirlingRemainder_eq_integral`: Stieltjes integral representation of
  `stirlingRemainder` on `slitPlane`.
* `TauCeti.iteratedDeriv_stirlingRemainder`, `TauCeti.iteratedDeriv_succ_stirlingRemainder`:
  integral representation of all iterated derivatives of `stirlingRemainder` and identification
  with iterated derivatives of `digamma z - log z + (2 * z)⁻¹`.
* `TauCeti.norm_iteratedDeriv_stirlingRemainder_le`,
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le`,
  `TauCeti.isBigO_iteratedDeriv_stirlingRemainder`: Nemes's explicit slit-plane and sector bounds
  for all `j : ℕ`, with specializations `TauCeti.norm_stirlingRemainder_le`,
  `TauCeti.norm_stirlingRemainder_le_of_abs_arg_le`, and `TauCeti.norm_deriv_stirlingRemainder_le`.
* `TauCeti.iteratedDeriv_stirlingRemainder_ofReal_im`,
  `TauCeti.mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos`,
  `TauCeti.deriv_stirlingRemainder_ofReal_re_neg`: real-valuedness and strict sign alternation on
  `(0, ∞)`.

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

/-! ### Stieltjes representation and iterated derivatives of `stirlingRemainder` -/

private noncomputable abbrev stieltjesKernel (j : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2)

/-- **Stieltjes integral representation of the Stirling remainder** (Nemes 2015, §2, eq. (2.5);
Whittaker and Watson, §12.33): for every `z ∈ slitPlane`,
`stirlingRemainder z = ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ 2 dt`. -/
theorem stirlingRemainder_eq_integral {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder z =
      ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ 2 := by
  let d : ℂ → ℂ := fun w ↦ stirlingRemainder w - stieltjesKernel 0 w
  have hd_deriv : ∀ w ∈ slitPlane, HasDerivAt d 0 w := fun w hw ↦ by
    have h1 := hasDerivAt_stirlingRemainder hw
    have h2 : HasDerivAt (stieltjesKernel 0) (-2 * stieltjesKernel 1 w) w :=
      (hasDerivAt_integral_fract_sub_fract_sq_div_add_pow hw 0).congr_deriv (by ring)
    have h3 : Complex.digamma w - Complex.log w + (2 * w)⁻¹ = -2 * stieltjesKernel 1 w :=
      Complex.digamma_sub_log_add_inv_two_mul_eq_integral (Or.inl hw)
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
  have hk_lim : Tendsto (fun n : ℕ ↦ stieltjesKernel 0 ((n : ℝ) + 1 : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ ↦ (8 * ((n : ℝ) + 1))⁻¹) (fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_) ?_
    · have hn : (0 : ℝ) < n + 1 := by positivity
      have hb := norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le 0 (((n : ℝ) + 1 : ℝ) : ℂ)
      have harg : (((n : ℝ) + 1 : ℝ) : ℂ).arg = 0 := arg_ofReal_of_nonneg hn.le
      rw [harg, zero_div, Real.cos_zero, Complex.norm_real, Real.norm_of_nonneg hn.le] at hb
      simpa [stieltjesKernel] using hb
    · refine tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop (by norm_num) ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hd_lim : Tendsto (fun n : ℕ ↦ d ((n : ℝ) + 1 : ℝ)) atTop (𝓝 0) := by
    simpa [d] using tendsto_stirlingRemainder_natCast_add_one.sub hk_lim
  have hd0 : d z = 0 := tendsto_const_nhds_iff.mp (hd_lim.congr fun n ↦ (hconst n).symm)
  exact sub_eq_zero.mp hd0

/-- Integral representation of all higher derivatives of the Stirling remainder on the slit plane:
for every `j : ℕ` and `z ∈ slitPlane`,
`iteratedDeriv j stirlingRemainder z =
  (-1) ^ j * (j + 1)! * ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt`. -/
theorem iteratedDeriv_stirlingRemainder (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv j stirlingRemainder z = (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
      ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2) := by
  induction j generalizing z with
  | zero =>
    simpa [iteratedDeriv_zero] using stirlingRemainder_eq_integral hz
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have heq : EqOn (iteratedDeriv j stirlingRemainder)
        (fun w ↦ (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * stieltjesKernel j w) slitPlane :=
      fun w hw ↦ ih hw
    have hd : HasDerivAt (fun w ↦ (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * stieltjesKernel j w)
        ((-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (-(j + 2 : ℂ) * stieltjesKernel (j + 1) z))
        z :=
      (hasDerivAt_integral_fract_sub_fract_sq_div_add_pow hz j).const_mul _
    rw [(heq.eventuallyEq_of_mem (isOpen_slitPlane.mem_nhds hz)).deriv_eq, hd.deriv]
    have hfac : ((j + 2).factorial : ℂ) = (j + 2 : ℂ) * ((j + 1).factorial : ℂ) := by
      rw [show j + 2 = (j + 1) + 1 by ring, Nat.factorial_succ]
      push_cast
      ring
    rw [pow_succ, hfac]
    dsimp [stieltjesKernel]
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

/-! ### Nemes's explicit sector bounds for `stirlingRemainder` and its derivatives -/

/-- **Nemes's bound for higher derivatives of the Stirling remainder** on the slit plane (Nemes
2015, eq. (2.5) and Lemma 2.1): for every `j : ℕ` and `z ∈ slitPlane`,
`‖iteratedDeriv j stirlingRemainder z‖ ≤
  j! / (8 * cos (arg z / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_le (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖iteratedDeriv j stirlingRemainder z‖ ≤
      (j.factorial : ℝ) / (8 * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  rw [iteratedDeriv_stirlingRemainder j hz, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_natCast]
  calc
    ((j + 1).factorial : ℝ) * ‖stieltjesKernel j z‖
        ≤ ((j + 1).factorial : ℝ) *
          (1 / (8 * (j + 1 : ℝ) * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))) :=
      mul_le_mul_of_nonneg_left (norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le j z)
        (Nat.cast_nonneg _)
    _ = (j.factorial : ℝ) / (8 * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
      rw [Nat.factorial_succ]
      push_cast
      have hj1 : (j + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hj1]

/-- Nemes's explicit sector bound for higher derivatives of the Stirling remainder: for `0 < δ`,
every nonzero `z` with `|arg z| ≤ π - δ`, and every `j : ℕ`,
`‖iteratedDeriv j stirlingRemainder z‖ ≤ j! / (8 * sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`.
Note that `δ ≤ π` follows automatically from `|arg z| ≤ π - δ`. -/
theorem norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le (j : ℕ) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖iteratedDeriv j stirlingRemainder z‖ ≤
      (j.factorial : ℝ) / (8 * Real.sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  have hslit := mem_slitPlane_of_abs_arg_le hδ hz hz0
  have hδπ : δ ≤ π := by linarith [abs_nonneg z.arg]
  have hsin : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (half_pos hδ) (by linarith [Real.pi_pos])
  have hsc := sin_half_le_cos_half_arg_of_abs_arg_le hδ.le hz
  refine (norm_iteratedDeriv_stirlingRemainder_le j hslit).trans ?_
  have hzn : 0 < ‖z‖ ^ (j + 1) := pow_pos (norm_pos_iff.mpr hz0) _
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsin.le hsc _) (by norm_num)) hzn.le)

/-- Nemes's explicit slit-plane bound for the Stirling remainder itself (`j = 0`):
`‖stirlingRemainder z‖ ≤ 1 / (8 * cos (arg z / 2) ^ 2 * ‖z‖)` for `z ∈ slitPlane`. -/
theorem norm_stirlingRemainder_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingRemainder z‖ ≤ 1 / (8 * Real.cos (z.arg / 2) ^ 2 * ‖z‖) := by
  simpa [iteratedDeriv_zero] using norm_iteratedDeriv_stirlingRemainder_le 0 hz

/-- Nemes's explicit closed-sector bound for the Stirling remainder (`j = 0`): for `0 < δ` and
nonzero `z` with `|arg z| ≤ π - δ`,
`‖stirlingRemainder z‖ ≤ 1 / (8 * sin (δ / 2) ^ 2 * ‖z‖)`. -/
theorem norm_stirlingRemainder_le_of_abs_arg_le {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingRemainder z‖ ≤ 1 / (8 * Real.sin (δ / 2) ^ 2 * ‖z‖) := by
  simpa [iteratedDeriv_zero] using norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le 0 hδ hz hz0

/-- Nemes's explicit slit-plane bound for `deriv stirlingRemainder` (`j = 1`):
`‖deriv stirlingRemainder z‖ ≤ 1 / (8 * cos (arg z / 2) ^ 3 * ‖z‖ ^ 2)` for `z ∈ slitPlane`. -/
theorem norm_deriv_stirlingRemainder_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖deriv stirlingRemainder z‖ ≤ 1 / (8 * Real.cos (z.arg / 2) ^ 3 * ‖z‖ ^ 2) := by
  simpa [iteratedDeriv_one] using norm_iteratedDeriv_stirlingRemainder_le 1 hz

/-- Existential sector bound for higher derivatives of `stirlingRemainder`: for every `j : ℕ` and
`0 < δ`, there exists `C > 0` with `‖iteratedDeriv j stirlingRemainder z‖ ≤ C / ‖z‖ ^ (j + 1)`
whenever `|arg z| ≤ π - δ` and `z ≠ 0`. -/
theorem exists_norm_iteratedDeriv_stirlingRemainder_le (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ z : ℂ, |z.arg| ≤ π - δ → z ≠ 0 →
      ‖iteratedDeriv j stirlingRemainder z‖ ≤ C / ‖z‖ ^ (j + 1) := by
  rcases le_or_gt δ π with hδπ | hπδ
  · have hsin : 0 < Real.sin (δ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (half_pos hδ) (by linarith [Real.pi_pos])
    refine ⟨(j.factorial : ℝ) / (8 * Real.sin (δ / 2) ^ (j + 2)),
      div_pos (Nat.cast_pos.mpr (Nat.factorial_pos j)) (by positivity),
      fun z hz hz0 ↦ ?_⟩
    rw [div_div]
    exact norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le j hδ hz hz0
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

private theorem iteratedDeriv_stirlingRemainder_ofReal_eq (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv j stirlingRemainder x =
      (((-1 : ℝ) ^ j * ((j + 1).factorial : ℝ) *
        ∫ t : ℝ in Ioi 0, ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
  rw [iteratedDeriv_stirlingRemainder j (ofReal_mem_slitPlane.mpr hx)]
  have heq : (∫ t : ℝ in Ioi 0,
      (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + t) ^ (j + 2)) =
      ((∫ t : ℝ in Ioi 0,
        ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
    calc
      (∫ t : ℝ in Ioi 0,
          (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + t) ^ (j + 2))
          = ∫ t : ℝ in Ioi 0,
            ((((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
        push_cast
        rfl
      _ = ((∫ t : ℝ in Ioi 0,
            ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) :=
        integral_ofReal
  rw [heq]
  push_cast
  rfl

/-- For every `j : ℕ` and `0 < x`, `iteratedDeriv j stirlingRemainder x` is real-valued. -/
theorem iteratedDeriv_stirlingRemainder_ofReal_im (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (iteratedDeriv j stirlingRemainder x).im = 0 := by
  rw [iteratedDeriv_stirlingRemainder_ofReal_eq j hx, ofReal_im]

/-- Real integral representation of `(iteratedDeriv j stirlingRemainder x).re` for `0 < x`. -/
theorem iteratedDeriv_stirlingRemainder_ofReal_re (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (iteratedDeriv j stirlingRemainder x).re =
      (-1 : ℝ) ^ j * ((j + 1).factorial : ℝ) *
        ∫ t : ℝ in Ioi 0, ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) := by
  rw [iteratedDeriv_stirlingRemainder_ofReal_eq j hx, ofReal_re]

/-- Strict sign alternation of the Stirling remainder and its derivatives on `(0, ∞)`:
for every `j : ℕ` and `0 < x`, `0 < (-1) ^ j * (iteratedDeriv j stirlingRemainder x).re`. -/
theorem mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos (j : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re := by
  rw [iteratedDeriv_stirlingRemainder_ofReal_re j hx, ← mul_assoc, ← mul_assoc, ← mul_pow,
    neg_one_mul, neg_neg, one_pow, one_mul]
  let f : ℝ → ℝ := fun t ↦ ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2)
  have hf_int : IntegrableOn f (Ioi 0) := by
    have hc := (integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff (j := j)).mpr
      (ofReal_mem_slitPlane.mpr hx)
    refine hc.re.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp [f]
    rw [← ofReal_add, ← ofReal_pow, ← ofReal_div, ofReal_re]
  have hf_nn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : 0 < x + t := by linarith [mem_Ioi.mp ht]
    exact div_nonneg (div_nonneg (Int.fract_sub_fract_sq_nonneg t) zero_le_two)
      (pow_nonneg hxt.le _)
  have hint_pos : 0 < ∫ t : ℝ in Ioi 0, f t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hf_nn hf_int]
    have hsub : Ioo (1 / 4 : ℝ) (3 / 4) ⊆ Function.support f ∩ Ioi 0 := by
      intro t ht
      refine ⟨Function.mem_support.mpr ?_, mem_Ioi.mpr (by linarith [ht.1])⟩
      have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hnum : 0 < (Int.fract t - Int.fract t ^ 2) / 2 := by
        rw [hfr]
        nlinarith [ht.1, ht.2]
      have hden : 0 < (x + t) ^ (j + 2) := pow_pos (by linarith [ht.1]) _
      exact (div_pos hnum hden).ne'
    have hvol : 0 < volume (Ioo (1 / 4 : ℝ) (3 / 4)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by norm_num)
    exact hvol.trans_le (measure_mono hsub)
  exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hint_pos

/-- Explicit upper bound on `(-1) ^ j * (iteratedDeriv j stirlingRemainder x).re` for `0 < x`:
`(-1) ^ j * (iteratedDeriv j stirlingRemainder x).re ≤ j! / (8 * x ^ (j + 1))`. -/
theorem mul_iteratedDeriv_stirlingRemainder_ofReal_re_le (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re ≤
      (j.factorial : ℝ) / (8 * x ^ (j + 1)) := by
  have hb := norm_iteratedDeriv_stirlingRemainder_le j (ofReal_mem_slitPlane.mpr hx)
  rw [arg_ofReal_of_nonneg hx.le, zero_div, Real.cos_zero, one_pow, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hx.le] at hb
  calc
    (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re
        ≤ |(-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re| := le_abs_self _
    _ = |(iteratedDeriv j stirlingRemainder x).re| := by rw [abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul]
    _ ≤ ‖iteratedDeriv j stirlingRemainder x‖ := abs_re_le_norm _
    _ ≤ (j.factorial : ℝ) / (8 * x ^ (j + 1)) := hb

/-- On `(0, ∞)` the Stirling remainder has strictly positive real part. -/
theorem stirlingRemainder_ofReal_re_pos {x : ℝ} (hx : 0 < x) :
    0 < (stirlingRemainder x).re := by
  simpa [iteratedDeriv_zero] using mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos 0 hx

/-- On `(0, ∞)` the Stirling remainder satisfies `(stirlingRemainder x).re ≤ 1 / (8 * x)`. -/
theorem stirlingRemainder_ofReal_re_le {x : ℝ} (hx : 0 < x) :
    (stirlingRemainder x).re ≤ 1 / (8 * x) := by
  simpa [iteratedDeriv_zero] using mul_iteratedDeriv_stirlingRemainder_ofReal_re_le 0 hx

/-- On `(0, ∞)` the Stirling remainder is strictly decreasing:
`(deriv stirlingRemainder x).re < 0` for `0 < x`. -/
theorem deriv_stirlingRemainder_ofReal_re_neg {x : ℝ} (hx : 0 < x) :
    (deriv stirlingRemainder x).re < 0 := by
  have h := mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos 1 hx
  rw [pow_one, iteratedDeriv_one, neg_one_mul, neg_pos] at h
  exact h

end TauCeti
