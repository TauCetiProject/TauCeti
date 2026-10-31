/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Precomp

import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Measure.AddCircle

/-!
# The Gagliardo–Slobodeckij characterization of the circle Sobolev spaces

For `0 < s < 1`, the Fourier-coefficient Sobolev space `H^s` of the circle `AddCircle T` has an
equivalent description by differences instead of Fourier coefficients: an element `a` of
`H⁰ = L²` lies in `H^s` exactly when its **Gagliardo–Slobodeckij energy**

`∫ ‖τ_h a - a‖² / ‖h‖ ^ (1 + 2 s) dh`

is finite. Here `τ_h` is the rotation by `h` (`TauCeti.CircleSobolev.rotate`), `‖h‖` is the
distance from `h` to `0` on the circle and `dh` is Lebesgue measure on the circle. The energy is
at most a constant times the squared `H^s` norm
(`TauCeti.CircleSobolev.exists_slobodeckijEnergy_le`), and the squared `H^s` norm is at most the
squared `H⁰` norm plus a constant times the energy
(`TauCeti.CircleSobolev.exists_norm_sq_le_slobodeckijEnergy`). So the squared `H⁰` norm plus the
energy is equivalent to the squared `H^s` norm; the energy alone vanishes on constants.

By Parseval's identity, the energy is `∑ₙ K(n) ‖aₙ‖²`, with the multiplier
`K(n) = ∫ |e^{2πinh/T} - 1|² / ‖h‖ ^ (1 + 2 s) dh`. This multiplier vanishes at `n = 0` and is
comparable to `|n| ^ (2 s)` otherwise. The lower bound comes from the interval of `h` on which
`|e^{2πinh/T} - 1| ≥ 1`. The upper bound uses `|e^{iθ} - 1| ≤ min |θ| 2`, splitting the integral
at `|h| = T / (2π|n|)`.

Unlike the Fourier description, differences behave well under nonlinear maps. If `f : ℂ → ℂ` is
`K`-Lipschitz then `‖f ∘ τ_h u - f ∘ u‖ ≤ K ‖τ_h u - u‖` pointwise, so the energy of `f ∘ u` is at
most `K²` times that of `u`. Hence composition with a Lipschitz function maps `H^s` to itself for
`0 < s < 1` (`TauCeti.CircleSobolev.exists_toLpₗᵢ_inclusion_eq_comp_of_lipschitzWith`). These
Nemytskii maps need no holomorphy of `f`, unlike those of
`TauCeti/Analysis/Sobolev/Circle/Nemytskii.lean`, and the orders `1/2 < s < 1` covered here are
those at which `H^s` consists of continuous functions.

## Main definitions

* `TauCeti.CircleSobolev.slobodeckijEnergy T s a`: the Gagliardo–Slobodeckij energy of order `s`
  of `a ∈ H⁰`, as an extended nonnegative real.

## Main statements

* `TauCeti.CircleSobolev.exists_slobodeckijEnergy_le`: for `0 < s < 1` the energy of `a ∈ H^s`
  is at most a constant times `‖a‖²`.
* `TauCeti.CircleSobolev.exists_norm_sq_le_slobodeckijEnergy`: conversely, for `0 ≤ s`, `‖a‖²` is
  at most the squared `H⁰` norm plus a constant times the energy.
* `TauCeti.CircleSobolev.exists_inclusion_eq_iff_slobodeckijEnergy_ne_top`: for `0 < s < 1`, an
  element of `H⁰` lies in `H^s` exactly when its energy is finite.
* `TauCeti.CircleSobolev.exists_toLpₗᵢ_inclusion_eq_comp_of_lipschitzWith`: for `0 < s < 1` and
  `f` Lipschitz, `f ∘ u` lies in `H^s` for every `u ∈ H^s`, with energy at most `K²` times that
  of `u`.

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, *Hitchhiker's guide to the fractional Sobolev
  spaces*, Bull. Sci. Math. **136** (2012), 521–573, Proposition 3.4 (the equivalence of the
  Fourier and Gagliardo descriptions on `ℝⁿ`, whose circle analogue is proved here).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the boundary Sobolev spaces on which nonlinear
  maps of boundary values act.
-/

public section

noncomputable section

open MeasureTheory AddCircle Set Real
open scoped ENNReal NNReal

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ℝ) [hT : Fact (0 < T)]

/-- The **Gagliardo–Slobodeckij energy** of order `s` of an element `a` of `H⁰` on the circle
`AddCircle T`:

`∫ ‖τ_h a - a‖² / ‖h‖ ^ (1 + 2 s) dh`,

where `τ_h = rotate h` is the rotation by `h`, `‖h‖` is the distance from `h` to `0` on the circle
and `dh` is Lebesgue measure on the circle. For `0 < s < 1` it is finite exactly on `H^s`. -/
def slobodeckijEnergy (s : ℝ) (a : CircleSobolev 0 E) : ℝ≥0∞ :=
  ∫⁻ h : AddCircle T, ENNReal.ofReal (‖rotate h a - a‖ ^ 2 / ‖h‖ ^ (1 + 2 * s))

theorem slobodeckijEnergy_def (s : ℝ) (a : CircleSobolev 0 E) :
    slobodeckijEnergy T s a =
      ∫⁻ h : AddCircle T, ENNReal.ofReal (‖rotate h a - a‖ ^ 2 / ‖h‖ ^ (1 + 2 * s)) :=
  (rfl)

@[simp]
theorem slobodeckijEnergy_zero (s : ℝ) : slobodeckijEnergy T s (0 : CircleSobolev 0 E) = 0 := by
  simp [slobodeckijEnergy_def]

/-- The energy is homogeneous of degree two. -/
@[simp]
theorem slobodeckijEnergy_smul (s : ℝ) (z : ℂ) (a : CircleSobolev 0 E) :
    slobodeckijEnergy T s (z • a) = ENNReal.ofReal (‖z‖ ^ 2) * slobodeckijEnergy T s a := by
  simp_rw [slobodeckijEnergy_def, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, map_smul,
    ← smul_sub, norm_smul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (sq_nonneg ‖z‖)]

/-! ### The Fourier multiplier of the energy -/

/-- The Fourier multiplier `∫ |e_n(h) - 1|² / ‖h‖ ^ (1 + 2 s) dh` of the energy. -/
private def kernel (s : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ∫⁻ h : AddCircle T, ENNReal.ofReal (‖fourier n h - 1‖ ^ 2 / ‖h‖ ^ (1 + 2 * s))

omit hT in
private theorem measurable_kernel_integrand (s : ℝ) (n : ℤ) :
    Measurable fun h : AddCircle T ↦ ENNReal.ofReal (‖fourier n h - 1‖ ^ 2 / ‖h‖ ^ (1 + 2 * s)) :=
  ((((fourier n).continuous.sub continuous_const).norm.pow 2).measurable.div
    (continuous_norm.measurable.pow_const _)).ennreal_ofReal

/-- By Parseval's identity, the energy is the sum of the squared coefficient norms weighted by the
multiplier. -/
private theorem slobodeckijEnergy_eq_tsum (s : ℝ) (a : CircleSobolev 0 E) :
    slobodeckijEnergy T s a = ∑' n, ENNReal.ofReal (‖a.coeff n‖ ^ 2) * kernel T s n := by
  have hpt (h : AddCircle T) : ENNReal.ofReal (‖rotate h a - a‖ ^ 2 / ‖h‖ ^ (1 + 2 * s)) =
      ∑' n, ENNReal.ofReal (‖a.coeff n‖ ^ 2) *
        ENNReal.ofReal (‖fourier n h - 1‖ ^ 2 / ‖h‖ ^ (1 + 2 * s)) := by
    have hsum : HasSum (fun n ↦ ‖a.coeff n‖ ^ 2 * (‖fourier n h - 1‖ ^ 2 / ‖h‖ ^ (1 + 2 * s)))
        (‖rotate h a - a‖ ^ 2 / ‖h‖ ^ (1 + 2 * s)) := by
      convert (hasSum_norm_sq (rotate h a - a)).div_const (‖h‖ ^ (1 + 2 * s)) using 2 with n
      rw [coeff_sub, Pi.sub_apply, coeff_rotate, mul_zero, weight_zero_left, one_mul,
        show fourier n h • a.coeff n - a.coeff n = (fourier n h - 1) • a.coeff n by
          rw [sub_smul, one_smul], norm_smul]
      ring
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum.summable]
    simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
  simp_rw [slobodeckijEnergy_def, hpt]
  rw [lintegral_tsum fun n ↦ ((measurable_kernel_integrand T s n).const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, kernel]

private theorem kernel_zero (s : ℝ) : kernel T s 0 = 0 := by
  simp [kernel]

/-- The lower bound `K(n) ≥ c (1 + |n|) ^ (2 s)` of the multiplier, for `n ≠ 0`. -/
private theorem ofReal_mul_weight_le_kernel (hs : 0 ≤ s) {n : ℤ} (hn : n ≠ 0) :
    ENNReal.ofReal (2⁻¹ * (3 / (2 * T)) ^ (2 * s) * weight (2 * s) n) ≤ kernel T s n := by
  have hT0 := hT.out
  have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
  have hn1 : 1 ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn
  set a := T / (6 * |(n : ℝ)|)
  set b := T / (3 * |(n : ℝ)|)
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hba : b - a = b / 2 := by
    simp only [a, b]
    field_simp
    ring
  have hsub : Icc a b ⊆ Ioc 0 (0 + T) := by
    intro x hx
    refine ⟨ha.trans_le hx.1, hx.2.trans ?_⟩
    rw [zero_add]
    exact div_le_self hT0.le (by nlinarith)
  -- On `[a, b]` the integrand is at least `1 / b ^ (1 + 2 s)`.
  have hpt : ∀ x ∈ Icc a b, ENNReal.ofReal (1 / b ^ (1 + 2 * s)) ≤
      ENNReal.ofReal
        (‖fourier n (x : AddCircle T) - 1‖ ^ 2 / ‖(x : AddCircle T)‖ ^ (1 + 2 * s)) := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    have hnorm : ‖(x : AddCircle T)‖ = x := by
      rw [(norm_coe_eq_abs_iff (p := T) hT0.ne').2, abs_of_pos hx0]
      rw [abs_of_pos hx0, abs_of_pos hT0]
      refine hx.2.trans (div_le_div_of_nonneg_left hT0.le (by norm_num) (by nlinarith))
    rw [hnorm]
    refine ENNReal.ofReal_le_ofReal (div_le_div₀ (by positivity) ?_ (by positivity)
      (rpow_le_rpow hx0.le hx.2 (by linarith)))
    exact one_le_pow₀ (one_le_norm_fourier_sub_one hT0 hn hx.1 hx.2)
  have hlow : ENNReal.ofReal (1 / b ^ (1 + 2 * s)) * ENNReal.ofReal (b - a) ≤ kernel T s n := by
    rw [kernel, ← AddCircle.lintegral_preimage T 0, ← Real.volume_Icc, ← setLIntegral_const]
    refine (setLIntegral_mono ?_ hpt).trans (lintegral_mono_set hsub)
    exact (measurable_kernel_integrand T s n).comp measurable_quotient_mk''
  rw [← ENNReal.ofReal_mul (by positivity)] at hlow
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlow
  -- The real inequality `c (1 + |n|) ^ (2 s) ≤ (b - a) / b ^ (1 + 2 s) = (1 / b) ^ (2 s) / 2`.
  rw [hba, rpow_add hb, rpow_one, weight_def]
  have hb' : (3 / (2 * T)) * (1 + |(n : ℝ)|) ≤ 1 / b := by
    simp only [b, one_div_div]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hT0]
    nlinarith
  have hpow := rpow_le_rpow (by positivity) hb' (by linarith : (0 : ℝ) ≤ 2 * s)
  rw [mul_rpow (by positivity) (by positivity), one_div, inv_rpow hb.le] at hpow
  calc 2⁻¹ * (3 / (2 * T)) ^ (2 * s) * (1 + |(n : ℝ)|) ^ (2 * s)
      ≤ 2⁻¹ * (b ^ (2 * s))⁻¹ := by nlinarith [inv_nonneg.2 (by norm_num : (0 : ℝ) ≤ 2)]
    _ = 1 / (b * b ^ (2 * s)) * (b / 2) := by
      field_simp

/-- The radial majorant of the integrand of the multiplier at the frequency scale `m`:
`m² t ^ (1 - 2 s)` for `m t < 1` and `4 t ^ (-1 - 2 s)` for `m t ≥ 1`. -/
private def majorant (s m : ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (m ^ 2) *
      {t : ℝ | ENNReal.ofReal (m * t) < 1}.indicator (fun t ↦ ENNReal.ofReal (t ^ (1 - 2 * s))) t +
    4 * {t : ℝ | 1 ≤ ENNReal.ofReal (m * t)}.indicator (fun t ↦ ENNReal.ofReal (t ^ (-1 - 2 * s))) t

omit hT in
private theorem measurable_majorant_near (s m : ℝ) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (m ^ 2) *
      {t : ℝ | ENNReal.ofReal (m * t) < 1}.indicator (fun t ↦ ENNReal.ofReal (t ^ (1 - 2 * s))) t :=
  ((measurable_id.pow_const _).ennreal_ofReal.indicator
    (measurableSet_lt (by fun_prop) measurable_const)).const_mul _

omit hT in
private theorem measurable_majorant (s m : ℝ) : Measurable (majorant s m) :=
  (measurable_majorant_near s m).add (((measurable_id.pow_const _).ennreal_ofReal.indicator
    (measurableSet_le measurable_const (by fun_prop))).const_mul _)

omit hT in
private theorem majorant_of_lt {s m t : ℝ} (h : m * t < 1) :
    majorant s m t = ENNReal.ofReal (m ^ 2 * t ^ (1 - 2 * s)) := by
  simp [majorant, indicator, h, not_le.2 h, ENNReal.ofReal_mul (sq_nonneg m)]

omit hT in
private theorem majorant_of_le {s m t : ℝ} (h : 1 ≤ m * t) :
    majorant s m t = ENNReal.ofReal (4 * t ^ (-1 - 2 * s)) := by
  simp [majorant, indicator, h, not_lt.2 h, ENNReal.ofReal_mul (zero_le_four : (0 : ℝ) ≤ 4)]

/-- The integrand of the multiplier is bounded by the radial majorant at the scale `2π |n| / T`,
evaluated at the distance `‖h‖` to `0`. -/
private theorem kernel_integrand_le (n : ℤ) (h : AddCircle T) :
    ENNReal.ofReal (‖fourier n h - 1‖ ^ 2 / ‖h‖ ^ (1 + 2 * s)) ≤
      majorant s (2 * π / T * |(n : ℝ)|) ‖h‖ := by
  set m := 2 * π / T * |(n : ℝ)|
  rcases (norm_nonneg h).eq_or_lt with ht | ht
  · simp [norm_eq_zero.1 ht.symm]
  set t := ‖h‖
  have he : ‖fourier n h - 1‖ ≤ m * t := by
    simpa only [norm_two_pi_I_mul_intCast_div hT.out] using norm_fourier_sub_one_le n h
  have he2 : ‖fourier n h - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [fourier_apply, Circle.norm_coe, norm_one]
    norm_num
  have htp : 0 < t ^ (1 + 2 * s) := rpow_pos_of_pos ht _
  rcases lt_or_ge (m * t) 1 with hmt | hmt
  · rw [majorant_of_lt hmt]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖fourier n h - 1‖ ^ 2 / t ^ (1 + 2 * s) ≤ (m * t) ^ 2 / t ^ (1 + 2 * s) := by gcongr
      _ = m ^ 2 * t ^ (1 - 2 * s) := by
        rw [show 1 - 2 * s = 2 - (1 + 2 * s) by ring, rpow_sub ht, rpow_two]
        ring
  · rw [majorant_of_le hmt, show -1 - 2 * s = -(1 + 2 * s) by ring, rpow_neg ht.le,
      ← div_eq_mul_inv]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ htp.le)
    nlinarith [norm_nonneg (fourier n h - 1)]

/-- The integral of the majorant over the half line: `m ^ (2 s) (1 / (2 - 2 s) + 4 / (2 s))`. -/
private theorem setLIntegral_majorant (hs0 : 0 < s) (hs1 : s < 1) {m : ℝ} (hm : 0 < m) :
    ∫⁻ t in Ioi 0, majorant s m t =
      ENNReal.ofReal (m ^ (2 * s) * (1 / (2 - 2 * s) + 4 / (2 * s))) := by
  have h₁ : 0 < 2 - 2 * s := by linarith
  -- The part `m t < 1` near the origin and the part `m t ≥ 1` away from it.
  have hnear : ∫⁻ t in Ioi 0,
      {t : ℝ | ENNReal.ofReal (m * t) < 1}.indicator (fun t ↦ ENNReal.ofReal (t ^ (1 - 2 * s))) t =
        ENNReal.ofReal (m ^ (2 * s - 2) / (2 - 2 * s)) := by
    rw [lintegral_indicator_ofReal_rpow_Ioi (by linarith) hm, ENNReal.one_rpow, mul_one,
      show -(1 - 2 * s + 1) = 2 * s - 2 by ring, show 1 - 2 * s + 1 = 2 - 2 * s by ring]
  have hfar : ∫⁻ t in Ioi 0,
      {t : ℝ | 1 ≤ ENNReal.ofReal (m * t)}.indicator (fun t ↦ ENNReal.ofReal (t ^ (-1 - 2 * s))) t =
        ENNReal.ofReal (m ^ (2 * s) / (2 * s)) := by
    rw [lintegral_indicator_le_ofReal_rpow_Ioi (by linarith) hm, ENNReal.one_rpow, mul_one,
      show -(-1 - 2 * s + 1) = 2 * s by ring]
  simp only [majorant]
  rw [lintegral_add_left (measurable_majorant_near s m), lintegral_const_mul' _ _ (by simp),
    lintegral_const_mul' _ _ (by simp), hnear, hfar, ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (sq_nonneg m), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity), rpow_sub hm, rpow_two]
  congr 1
  field_simp

/-- The upper bound `K(n) ≤ C (1 + |n|) ^ (2 s)` of the multiplier, for `0 < s < 1`. -/
private theorem kernel_le (hs0 : 0 < s) (hs1 : s < 1) (n : ℤ) :
    kernel T s n ≤ ENNReal.ofReal
      (2 * (2 * π / T) ^ (2 * s) * (1 / (2 - 2 * s) + 4 / (2 * s)) * weight (2 * s) n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [kernel_zero]
    exact bot_le
  have hT0 := hT.out
  have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
  have hm : 0 < 2 * π / T * |(n : ℝ)| := by positivity
  have hD : 0 ≤ 1 / (2 - 2 * s) + 4 / (2 * s) := by
    have : 0 < 2 - 2 * s := by linarith
    positivity
  calc kernel T s n ≤ ∫⁻ h : AddCircle T, majorant s (2 * π / T * |(n : ℝ)|) ‖h‖ :=
        lintegral_mono fun h ↦ kernel_integrand_le T n h
    _ ≤ 2 * ∫⁻ t in Ioi 0, majorant s (2 * π / T * |(n : ℝ)|) t :=
        AddCircle.lintegral_comp_norm_le (measurable_majorant s _)
    _ = ENNReal.ofReal (2 * ((2 * π / T * |(n : ℝ)|) ^ (2 * s) *
          (1 / (2 - 2 * s) + 4 / (2 * s)))) := by
        rw [setLIntegral_majorant hs0 hs1 hm, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_rpow (by positivity) hn0.le, weight_def]
        have := rpow_le_rpow hn0.le (by linarith : |(n : ℝ)| ≤ 1 + |(n : ℝ)|)
          (by linarith : (0 : ℝ) ≤ 2 * s)
        have hc : 0 ≤ (2 * π / T) ^ (2 * s) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this hc]

/-! ### Comparison of the energy with the norm of `H^s` -/

/-- The weighted coefficient sum of `H^s` is bounded by the squared `H⁰` norm and the energy. The
frequency `0` is controlled by the `H⁰` norm and the other frequencies by the lower bound on the
multiplier. -/
private theorem tsum_ofReal_weight_mul_le (hs : 0 ≤ s) (a : CircleSobolev 0 E) :
    ∑' n, ENNReal.ofReal (weight (2 * s) n * ‖a.coeff n‖ ^ 2) ≤
      ENNReal.ofReal (‖a‖ ^ 2) +
        ENNReal.ofReal (2⁻¹ * (3 / (2 * T)) ^ (2 * s))⁻¹ * slobodeckijEnergy T s a := by
  have hT0 := hT.out
  set c := 2⁻¹ * (3 / (2 * T)) ^ (2 * s)
  have hc : 0 < c := by positivity
  have hnorm := ofReal_norm_sq_eq_tsum a
  simp only [mul_zero, weight_zero_left, one_mul] at hnorm
  rw [hnorm, slobodeckijEnergy_eq_tsum, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [weight_def, Int.cast_zero, abs_zero, add_zero, one_rpow, one_mul]
    exact le_self_add
  refine le_add_left ?_
  calc ENNReal.ofReal (weight (2 * s) n * ‖a.coeff n‖ ^ 2)
      = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (c * weight (2 * s) n) *
          ENNReal.ofReal (‖a.coeff n‖ ^ 2) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le),
          ← ENNReal.ofReal_mul
            (mul_nonneg (inv_nonneg.2 hc.le) (mul_nonneg hc.le (weight_nonneg _ _)))]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (‖a.coeff n‖ ^ 2) * kernel T s n) := by
        rw [mul_assoc, mul_comm (ENNReal.ofReal (c * _))]
        gcongr
        exact ofReal_mul_weight_le_kernel T hs hn

/-- **The norm of `H^s` is controlled by the `H⁰` norm and the Gagliardo–Slobodeckij energy.**
For `0 ≤ s`, the
squared norm of `a ∈ H^s` is at most its squared `H⁰` norm plus a constant multiple of the energy
of order `s`. -/
theorem exists_norm_sq_le_slobodeckijEnergy (hs : 0 ≤ s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ a : CircleSobolev s E,
      ENNReal.ofReal (‖a‖ ^ 2) ≤
        ENNReal.ofReal (‖inclusion hs a‖ ^ 2) + C * slobodeckijEnergy T s (inclusion hs a) := by
  have hT0 := hT.out
  refine ⟨ENNReal.ofReal (2⁻¹ * (3 / (2 * T)) ^ (2 * s))⁻¹, ENNReal.ofReal_ne_top, fun a ↦ ?_⟩
  refine le_trans (le_of_eq ?_) (tsum_ofReal_weight_mul_le T hs (inclusion hs a))
  rw [ofReal_norm_sq_eq_tsum, coeff_inclusion]

/-- **The Gagliardo–Slobodeckij energy is controlled by the norm of `H^s`.** For `0 < s < 1`, the
energy of order `s` of `a ∈ H^s` is at most a constant multiple of `‖a‖²`. -/
theorem exists_slobodeckijEnergy_le (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : CircleSobolev s E,
      slobodeckijEnergy T s (inclusion hs0.le a) ≤ ENNReal.ofReal (C * ‖a‖ ^ 2) := by
  have hT0 := hT.out
  set C := 2 * (2 * π / T) ^ (2 * s) * (1 / (2 - 2 * s) + 4 / (2 * s))
  have hC : 0 ≤ C := by
    have : 0 < 2 - 2 * s := by linarith
    positivity
  refine ⟨C, hC, fun a ↦ ?_⟩
  rw [slobodeckijEnergy_eq_tsum, ENNReal.ofReal_mul hC, ofReal_norm_sq_eq_tsum,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n ↦ ?_
  rw [coeff_inclusion, ENNReal.ofReal_mul (weight_nonneg _ _), ← mul_assoc,
    ← ENNReal.ofReal_mul hC, mul_comm (ENNReal.ofReal (‖_‖ ^ 2))]
  gcongr
  exact kernel_le T hs0 hs1 n

/-- **The Gagliardo–Slobodeckij characterization of `H^s`.** For `0 < s < 1`, an element of
`H⁰ = L²` lies in `H^s` exactly when its energy of order `s` is finite. -/
theorem exists_inclusion_eq_iff_slobodeckijEnergy_ne_top (hs0 : 0 < s) (hs1 : s < 1)
    (a : CircleSobolev 0 E) :
    (∃ b : CircleSobolev s E, inclusion hs0.le b = a) ↔ slobodeckijEnergy T s a ≠ ∞ := by
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨C, -, hC⟩ := exists_slobodeckijEnergy_le (E := E) T hs0 hs1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC b)
  · intro ha
    have hfin := (tsum_ofReal_weight_mul_le T hs0.le a).trans_lt (ENNReal.add_lt_top.2
      ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top (by simp) ha.lt_top⟩)
    have hsum : Summable fun n ↦ weight (2 * s) n * ‖a.coeff n‖ ^ 2 := by
      convert ENNReal.summable_toReal hfin.ne using 2 with n
      rw [ENNReal.toReal_ofReal (by positivity [weight_nonneg (2 * s) n])]
    obtain ⟨b, hb⟩ := (exists_coeff_eq_iff (s := s) a.coeff).2 <| (memℓp_weight_smul_iff _).2 <| by
      convert hsum using 2 with n
      rw [two_mul, weight_add]
      ring
    exact ⟨b, CircleSobolev.ext (by rw [coeff_inclusion, hb])⟩

/-! ### Lipschitz maps -/

/-- **Lipschitz maps bound the energy.** If the `L²` function of `c ∈ H⁰` is a `K`-Lipschitz
function `f` of the `L²` function of `d ∈ H⁰`, then at every order the energy of `c` is at most
`K²` times that of `d`. -/
theorem slobodeckijEnergy_le_of_ae_eq_comp {f : ℂ → ℂ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {c d : CircleSobolev 0 ℂ} (hcd : toLpₗᵢ T c =ᵐ[haarAddCircle] f ∘ toLpₗᵢ T d) (s : ℝ) :
    slobodeckijEnergy T s c ≤ (K : ℝ≥0∞) ^ 2 * slobodeckijEnergy T s d := by
  have hrot (h : AddCircle T) : ‖rotate h c - c‖ ≤ K * ‖rotate h d - d‖ := by
    rw [← (toLpₗᵢ T).norm_map, ← (toLpₗᵢ T).norm_map, map_sub, map_sub]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    have htr : toLpₗᵢ T c ∘ (· + h) =ᵐ[haarAddCircle] (f ∘ toLpₗᵢ T d) ∘ (· + h) :=
      (measurePreserving_add_right haarAddCircle h).quasiMeasurePreserving.ae_eq_comp hcd
    filter_upwards [Lp.coeFn_sub (toLpₗᵢ T (rotate h c)) (toLpₗᵢ T c),
      Lp.coeFn_sub (toLpₗᵢ T (rotate h d)) (toLpₗᵢ T d), toLpₗᵢ_rotate h c, toLpₗᵢ_rotate h d,
      htr, hcd] with x h₁ h₂ h₃ h₄ h₅ h₆
    simp only [Function.comp_apply] at h₃ h₄ h₅ h₆
    rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply, h₃, h₄, h₅, h₆]
    exact hf.norm_sub_le _ _
  rw [slobodeckijEnergy_def, slobodeckijEnergy_def, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun h ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow K.coe_nonneg,
    ← ENNReal.ofReal_mul (by positivity), mul_div_assoc', ← mul_pow]
  gcongr
  exact hrot h

/-- **Lipschitz maps act on `H^s` for `0 < s < 1`.** If `f : ℂ → ℂ` is `K`-Lipschitz and
`a ∈ H^s`, then `f ∘ a` lies in `H^s`: some `b ∈ H^s` has `L²` function `f` composed with that of
`a`. Its energy is at most `K²` times that of `a`. -/
theorem exists_toLpₗᵢ_inclusion_eq_comp_of_lipschitzWith (hs0 : 0 < s) (hs1 : s < 1)
    {f : ℂ → ℂ} {K : ℝ≥0} (hf : LipschitzWith K f) (a : CircleSobolev s ℂ) :
    ∃ b : CircleSobolev s ℂ,
      toLpₗᵢ T (inclusion hs0.le b) =ᵐ[haarAddCircle] f ∘ toLpₗᵢ T (inclusion hs0.le a) ∧
        slobodeckijEnergy T s (inclusion hs0.le b) ≤
          (K : ℝ≥0∞) ^ 2 * slobodeckijEnergy T s (inclusion hs0.le a) := by
  set u := toLpₗᵢ T (inclusion hs0.le a)
  have hmem : MemLp (f ∘ u) 2 haarAddCircle := by
    have h0 := (hf.sub (LipschitzWith.const (f 0))).comp_memLp (by simp) (Lp.memLp u)
    exact (h0.add (memLp_const (f 0))).ae_eq (ae_of_all _ fun x ↦ by simp)
  set c := (toLpₗᵢ T).symm (hmem.toLp _)
  have hc : toLpₗᵢ T c =ᵐ[haarAddCircle] f ∘ u := by
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hmem.coeFn_toLp
  have hE := slobodeckijEnergy_le_of_ae_eq_comp T hf hc s
  obtain ⟨C, -, hC⟩ := exists_slobodeckijEnergy_le (E := ℂ) T hs0 hs1
  obtain ⟨b, hb⟩ := (exists_inclusion_eq_iff_slobodeckijEnergy_ne_top T hs0 hs1 c).2
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC a))) hE)
  exact ⟨b, hb ▸ hc, hb ▸ hE⟩

end CircleSobolev

end TauCeti
