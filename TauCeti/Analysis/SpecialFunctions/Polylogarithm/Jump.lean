/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Conjugation
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Continuity at `1`, half-plane boundary limits, and the cut jump of polylogarithms

This file establishes the unrestricted boundary behaviour of the principal integer-weight
polylogarithms `TauCeti.Polylog.polylog` at the branch point `z = 1` and along the open branch cut
`(1, ∞)`:

* For integer weight `n ≥ 2`, `polylog n` is continuous at `1` for unrestricted complex approach
  (`ContinuousAt (polylog n) 1`), and for every `n : ℤ` the value `polylog n 1` (hence `polylog n x`
  for all `x ≤ 1`) is real. By contrast, neither `polylog 0` nor `polylog 1` is continuous at `1`,
  and `‖polylog 1 z‖ → ∞` on `𝓝[≠] 1`.
* On `(1, ∞)`, Mathlib's principal logarithm assigns `arg (1 - t x) = π` for `t > x⁻¹` and `0` for
  `t ≤ x⁻¹`. Integrating `(-log t) ^ k / t` over `[x⁻¹, 1]` gives the exact lower-boundary
  imaginary part `(polylog n x).im = -π * (log x) ^ (n - 1) / (n - 1)!` for every `n ≥ 1` and
  `x > 1`.
* Uniform integrability of the radial integrand together with continuity of `Complex.log` from the
  closed upper side of `(-∞, 0)` shows that `polylog n` is continuous at every `x > 1` within the
  closed lower half-plane `{z : ℂ | z.im ≤ 0}`, while along `{z : ℂ | 0 < z.im}` it tends to
  `conj (polylog n x)`. Subtracting the vertical-ray limits at `x ± t * I` yields the classical
  principal jump `2 * π * I * (log x) ^ (n - 1) / (n - 1)!` for `n ≥ 1` and `x > 1`, and hence
  discontinuity of `polylog n` at every point of `(1, ∞)`.

## Main declarations

* `TauCeti.Polylog.continuousAt_polylog_one_of_two_le`: unrestricted complex continuity at `1` for
  `2 ≤ n`.
* `TauCeti.Polylog.im_polylog_one`, `TauCeti.Polylog.ofReal_re_polylog_one`,
  `TauCeti.Polylog.polylog_conj_one`, and `TauCeti.Polylog.im_polylog_of_le_one`: reality and
  conjugation compatibility at `1` (and on `(-∞, 1]`) for every `n : ℤ`.
* `TauCeti.Polylog.not_continuousAt_polylog_zero_weight_one`,
  `TauCeti.Polylog.tendsto_norm_polylog_one_nhdsNE_one`, and
  `TauCeti.Polylog.not_continuousAt_polylog_one_one`: blow-up and discontinuity at `1` in weights
  `0` and `1`.
* `TauCeti.Polylog.im_polylog_of_one_lt`: exact imaginary part on `(1, ∞)` for `1 ≤ n`.
* `TauCeti.Polylog.continuousWithinAt_polylog_im_nonpos` and
  `TauCeti.Polylog.tendsto_polylog_nhdsWithin_im_pos`: boundary limits from `{z | z.im ≤ 0}` and
  `{z | 0 < z.im}` at `x > 1` in every integer weight.
* `TauCeti.Polylog.tendsto_polylog_sub_mul_I`, `TauCeti.Polylog.tendsto_polylog_add_mul_I`,
  `TauCeti.Polylog.tendsto_polylog_jump`, and `TauCeti.Polylog.not_continuousAt_polylog_of_one_lt`:
  vertical-ray boundary limits, the principal jump formula, and discontinuity across `(1, ∞)`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.3, (6), p. 51; §1.4, p. 51; §2.2, (8), p. 53.
* Don Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*
  (2007), Part I, §1, p. 6.
-/

public section

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology

namespace TauCeti.Polylog

/-! ### Unrestricted continuity and reality at `1` -/

/-- For every `k : ℕ`, `polylog (k + 2)` is continuous at `1` for unrestricted complex approach. -/
theorem continuousAt_polylog_nat_add_two_one (k : ℕ) :
    ContinuousAt (polylog (k + 2 : ℕ)) 1 := by
  have hfn : polylog (k + 2 : ℕ) = fun z : ℂ ↦ (k.factorial : ℂ)⁻¹ *
      ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / t :=
    funext (polylog_nat_add_two k)
  rw [hfn, ContinuousAt]
  refine tendsto_const_nhds.mul ?_
  simpa only [id_eq] using
    tendsto_integral_radialIntegrand_of_tendsto_ae k (φ := id)
      ⟨‖(1 : ℂ)‖ + 1, tendsto_norm.eventually (Iic_mem_nhds (lt_add_one _))⟩
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc,
          ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (1 : ℝ)))] with t ht ht1
        have ht_lt : t < 1 := lt_of_le_of_ne ht.2 ht1
        have hmem : 1 - (t : ℂ) * 1 ∈ Complex.slitPlane :=
          Complex.mem_slitPlane_iff.2 (Or.inl (by simp [sub_pos.2 ht_lt]))
        have haff : Continuous (fun z : ℂ ↦ 1 - (t : ℂ) * z) := by fun_prop
        exact (continuousAt_clog hmem).tendsto.comp haff.continuousAt.tendsto)

/-- For integer weight `n ≥ 2`, `polylog n` is continuous at `1` for unrestricted complex
approach. -/
theorem continuousAt_polylog_one_of_two_le {n : ℤ} (hn : 2 ≤ n) :
    ContinuousAt (polylog n) 1 := by
  lift n - 2 to ℕ using sub_nonneg.2 hn with k hk
  have hn' : n = (k + 2 : ℕ) := by omega
  rw [hn']
  exact continuousAt_polylog_nat_add_two_one k

/-- For every integer weight `n`, `polylog n 1` has zero imaginary part (including the totalised
values in weights `n ≤ 1`). -/
@[simp] theorem im_polylog_one (n : ℤ) : (polylog n 1).im = 0 := by
  rcases le_or_gt n 0 with hn | hn
  · simpa using im_polylog_of_nonpos hn 1
  · rcases eq_or_lt_of_le (Int.add_one_le_iff.2 hn) with rfl | hn2
    · simp
    · set u : ℕ → ℝ := fun m ↦ 1 - ((m : ℝ) + 1)⁻¹
      have hu_lt : ∀ m, u m < 1 := fun m ↦ sub_lt_self 1 (by positivity)
      have hu_tendsto : Tendsto (fun m ↦ (u m : ℂ)) atTop (𝓝 1) := by
        have hinv : Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have hreal : Tendsto u atTop (𝓝 1) := by
          simpa [u] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
        simpa [Function.comp_def] using
          (Complex.continuous_ofReal.continuousAt (x := 1)).tendsto.comp hreal
      have him_tendsto : Tendsto (fun m ↦ (polylog n (u m)).im) atTop (𝓝 (polylog n 1).im) :=
        (Complex.continuous_im.continuousAt.comp
          (continuousAt_polylog_one_of_two_le hn2)).tendsto.comp hu_tendsto
      have him_zero : (fun m ↦ (polylog n (u m)).im) = fun _ ↦ 0 :=
        funext fun m ↦ im_polylog_of_lt_one n (hu_lt m)
      rw [him_zero] at him_tendsto
      exact tendsto_nhds_unique him_tendsto tendsto_const_nhds

/-- For every integer weight `n`, `polylog n 1` equals its real part coerced to `ℂ`. -/
theorem ofReal_re_polylog_one (n : ℤ) : ((polylog n 1).re : ℂ) = polylog n 1 := by
  simp [Complex.ext_iff]

/-- For every integer weight `n`, `polylog n` commutes with conjugation at `z = 1`. -/
theorem polylog_conj_one (n : ℤ) : polylog n (conj (1 : ℂ)) = conj (polylog n 1) := by
  rw [map_one]
  exact (Complex.conj_eq_iff_im.2 (im_polylog_one n)).symm

/-- For every integer weight `n` and real `x ≤ 1`, `polylog n x` has zero imaginary part. -/
theorem im_polylog_of_le_one (n : ℤ) {x : ℝ} (hx : x ≤ 1) : (polylog n x).im = 0 := by
  rcases hx.lt_or_eq with hlt | rfl
  · exact im_polylog_of_lt_one n hlt
  · simp

/-- For every integer weight `n` and real `x ≤ 1`, `polylog n x` equals its real part coerced to
`ℂ`. -/
theorem ofReal_re_polylog_of_le_one (n : ℤ) {x : ℝ} (hx : x ≤ 1) :
    ((polylog n x).re : ℂ) = polylog n x := by
  simpa [Complex.ext_iff] using (im_polylog_of_le_one n hx).symm

/-- Weight zero is not continuous at its pole `z = 1`. -/
theorem not_continuousAt_polylog_zero_weight_one : ¬ ContinuousAt (polylog 0) 1 := by
  intro hc
  have hlim : Tendsto (fun z : ℂ ↦ (1 - z) * (1 + polylog 0 z)) (𝓝[≠] 1) (𝓝 0) := by
    have h0 : (0 : ℂ) = (1 - 1) * (1 + polylog 0 1) := by ring
    rw [h0]
    exact ((continuousAt_const.sub continuousAt_id).mul
      (continuousAt_const.add hc)).tendsto.mono_left nhdsWithin_le_nhds
  have hcongr : (fun z : ℂ ↦ (1 - z) * (1 + polylog 0 z)) =ᶠ[𝓝[≠] 1] fun _ ↦ (1 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hsub : 1 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    simp only [polylog_zero_weight]
    field_simp
    ring
  exact one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds.congr' hcongr.symm) hlim)

/-- In weight `1`, `‖polylog 1 z‖ → ∞` as `z → 1` through `z ≠ 1`. -/
theorem tendsto_norm_polylog_one_nhdsNE_one :
    Tendsto (fun z : ℂ ↦ ‖polylog 1 z‖) (𝓝[≠] 1) atTop := by
  have hsub : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous (fun z : ℂ ↦ 1 - z) := by fun_prop
      simpa using (hcont.continuousAt (x := 1)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.2 (Ne.symm hz)
  have hlog : Tendsto (fun z : ℂ ↦ -Real.log ‖1 - z‖) (𝓝[≠] 1) atTop :=
    tendsto_neg_atBot_atTop.comp
      (Real.tendsto_log_nhdsGT_zero.comp (tendsto_norm_nhdsNE_zero.comp hsub))
  refine tendsto_atTop_mono (fun z ↦ ?_) hlog
  rw [polylog_one, norm_neg]
  calc -Real.log ‖1 - z‖ ≤ |Real.log ‖1 - z‖| := neg_le_abs _
    _ = |(Complex.log (1 - z)).re| := by rw [Complex.log_re]
    _ ≤ ‖Complex.log (1 - z)‖ := Complex.abs_re_le_norm _

/-- Weight `1` is not continuous at its logarithmic branch point `z = 1`. -/
theorem not_continuousAt_polylog_one_one : ¬ ContinuousAt (polylog 1) 1 := by
  intro hc
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_norm_polylog_one_nhdsNE_one _
    (hc.norm.tendsto.mono_left nhdsWithin_le_nhds)

/-! ### Exact imaginary part on the branch cut `(1, ∞)` -/

/-- Pointwise imaginary part of the weight-`(k + 2)` radial integrand at a real argument `x`. -/
private lemma im_radialIntegrand_ofReal (k : ℕ) (x t : ℝ) :
    (((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * x)) / t).im =
      -((-Real.log t) ^ k * Complex.arg ((1 - t * x : ℝ) : ℂ) / t) := by
  set a : ℝ := (-Real.log t) ^ k
  set w : ℝ := 1 - t * x
  have ha : ((-Real.log t : ℝ) : ℂ) ^ k = (a : ℂ) := by simp [a]
  have hw : 1 - (t : ℂ) * x = (w : ℂ) := by simp [w]
  rw [ha, hw, div_eq_mul_inv, ← Complex.ofReal_inv, mul_right_comm, ← Complex.ofReal_mul,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.neg_im, Complex.log_im]
  ring

/-- Imaginary part of `polylog (k + 2) x` on the open branch cut `x > 1`. -/
private lemma im_polylog_nat_add_two_of_one_lt (k : ℕ) {x : ℝ} (hx : 1 < x) :
    (polylog (k + 2 : ℕ) x).im =
      -Real.pi * Real.log x ^ (k + 1) / (k + 1).factorial := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxinv0 : 0 < x⁻¹ := inv_pos.2 hx0
  have hxinv1 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx.le
  set f : ℝ → ℂ := fun t ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * x)) / t
    with hf_def
  have hf01 : IntervalIntegrable f volume 0 1 := intervalIntegrable_radialIntegrand k x
  have hmem01 : x⁻¹ ∈ uIcc (0 : ℝ) 1 := by rw [uIcc_of_le zero_le_one]; exact ⟨hxinv0.le, hxinv1⟩
  have hf1 : IntervalIntegrable f volume 0 x⁻¹ := hf01.mono_set (uIcc_subset_uIcc_left hmem01)
  have hf2 : IntervalIntegrable f volume x⁻¹ 1 := hf01.mono_set (uIcc_subset_uIcc_right hmem01)
  have him1 : ∫ t : ℝ in 0..x⁻¹, RCLike.im (f t) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le (g := fun _ ↦ 0) hxinv0.le fun t ht ↦ ?_,
      intervalIntegral.integral_zero]
    have htx : t * x ≤ 1 :=
      (mul_le_mul_of_nonneg_right ht.2.le hx0.le).trans_eq (inv_mul_cancel₀ hx0.ne')
    rw [RCLike.im_eq_complex_im, hf_def, im_radialIntegrand_ofReal,
      Complex.arg_ofReal_of_nonneg (by linarith)]
    ring
  have hderiv : ∀ t ∈ uIcc x⁻¹ 1,
      HasDerivAt (fun s ↦ -(-Real.log s) ^ (k + 1) / (k + 1)) ((-Real.log t) ^ k / t) t := by
    intro t ht; rw [uIcc_of_le hxinv1] at ht
    have ht0 : 0 < t := hxinv0.trans_le ht.1
    convert (((Real.hasDerivAt_log ht0.ne').neg.pow (k + 1)).neg).div_const ((k : ℝ) + 1) using 1
    dsimp only [Pi.neg_apply, Nat.add_sub_cancel]; push_cast
    have : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [ht0.ne']
  have hcont : ContinuousOn (fun t : ℝ ↦ (-Real.log t) ^ k / t) (uIcc x⁻¹ 1) := fun t ht ↦ by
    rw [uIcc_of_le hxinv1] at ht; have ht0 := (hxinv0.trans_le ht.1).ne'
    exact (((Real.continuousAt_log ht0).neg.pow k).div continuousAt_id ht0).continuousWithinAt
  have him2 : ∫ t : ℝ in x⁻¹..1, RCLike.im (f t) =
      -Real.pi * (Real.log x ^ (k + 1) / (k + 1)) := by
    rw [intervalIntegral.integral_congr_Ioo_of_le
      (g := fun t ↦ -Real.pi * ((-Real.log t) ^ k / t)) hxinv1 fun t ht ↦ ?_,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    · simp only [Real.log_one, neg_zero, zero_pow (Nat.succ_ne_zero k), zero_div, Real.log_inv,
        neg_neg, zero_sub]
      ring
    · have htx : 1 < t * x :=
        (inv_mul_cancel₀ hx0.ne').symm.trans_lt (mul_lt_mul_of_pos_right ht.1 hx0)
      rw [RCLike.im_eq_complex_im, hf_def, im_radialIntegrand_ofReal,
        Complex.arg_ofReal_of_neg (by linarith)]
      ring
  rw [polylog_nat_add_two, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    ← intervalIntegral.integral_add_adjacent_intervals hf1 hf2, Complex.add_im,
    ← RCLike.im_eq_complex_im,
    ← intervalIntegral.intervalIntegral_im hf1, ← intervalIntegral.intervalIntegral_im hf2,
    him1, him2, zero_add, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- On the open branch cut `(1, ∞)`, the principal polylogarithm of positive weight `n ≥ 1` selects
the lower boundary value, with imaginary part `-π * (log x) ^ (n - 1) / (n - 1)!`. -/
theorem im_polylog_of_one_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    (polylog n x).im = -Real.pi * Real.log x ^ (n - 1) / (n - 1).factorial := by
  rcases Nat.exists_eq_add_of_le' hn with ⟨m, rfl⟩
  rcases m with _ | k
  · simp only [zero_add, Nat.cast_one, Nat.sub_self, pow_zero, Nat.factorial_zero,
      polylog_one, Complex.neg_im, Complex.log_im]
    have hw : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by simp
    rw [hw, Complex.arg_ofReal_of_neg (sub_neg.2 hx)]
    ring
  · exact im_polylog_nat_add_two_of_one_lt k hx

/-- At `x = 3`, the principal dilogarithm has imaginary part `-π * log 3`. -/
theorem im_polylog_two_three : (polylog 2 (3 : ℂ)).im = -Real.pi * Real.log 3 := by
  simpa using im_polylog_of_one_lt (n := 2) (by omega) (x := 3) (by norm_num)

/-! ### Half-plane boundary limits and the principal jump across `(1, ∞)` -/

/-- Almost-everywhere convergence of `Log (1 - t z)` as `z → x > 1` in the closed lower half-plane
`{z : ℂ | z.im ≤ 0}`. -/
private lemma ae_tendsto_log_one_sub_mul_im_nonpos {x : ℝ} (hx : 1 < x) :
    ∀ᵐ (t : ℝ) ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun z : ℂ ↦ Complex.log (1 - (t : ℂ) * z))
        (𝓝[{z : ℂ | z.im ≤ 0}] x) (𝓝 (Complex.log (1 - (t : ℂ) * x))) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton x⁻¹))] with t ht htx
  have haff : Continuous (fun z : ℂ ↦ 1 - (t : ℂ) * z) := by fun_prop
  rcases lt_or_gt_of_ne htx with hlt | hgt
  · have hpos : 0 < 1 - t * x := by
      have : t * x < 1 := (mul_lt_mul_of_pos_right hlt hx0).trans_eq (inv_mul_cancel₀ hx0.ne')
      linarith
    have hmem : 1 - (t : ℂ) * x ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.2 (Or.inl (by simp [hpos]))
    exact ((continuousAt_clog hmem).tendsto.comp haff.continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  · have hre : (1 - (t : ℂ) * x).re < 0 := by
      have : 1 < t * x := (inv_mul_cancel₀ hx0.ne').symm.trans_lt (mul_lt_mul_of_pos_right hgt hx0)
      simpa using sub_neg.2 this
    have him : (1 - (t : ℂ) * x).im = 0 := by simp
    have hmaps : MapsTo (fun z : ℂ ↦ 1 - (t : ℂ) * z) {z : ℂ | z.im ≤ 0} {w : ℂ | 0 ≤ w.im} := by
      intro z hz
      dsimp only [mem_ofPred_eq] at hz ⊢
      simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, zero_sub, Left.nonneg_neg_iff]
      exact mul_nonpos_of_nonneg_of_nonpos ht.1.le hz
    exact (Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto.comp
      ((haff.continuousWithinAt (x := (x : ℂ))).tendsto_nhdsWithin hmaps)

/-- For every integer weight `n` and real `x > 1`, `polylog n` is continuous at `x` within the
closed lower half-plane `{z : ℂ | z.im ≤ 0}`: its totalised cut value agrees with the lower
half-plane boundary limit. -/
theorem continuousWithinAt_polylog_im_nonpos (n : ℤ) {x : ℝ} (hx : 1 < x) :
    ContinuousWithinAt (polylog n) {z : ℂ | z.im ≤ 0} x := by
  rcases le_or_gt n 0 with hn | hn
  · lift -n to ℕ using neg_nonneg.2 hn with r hr
    have hn' : n = -(r : ℤ) := by omega
    rw [hn']
    have hx1 : (x : ℂ) ≠ 1 := Complex.ofReal_ne_one.2 hx.ne'
    exact (analyticAt_polylog_neg_nat r hx1).continuousAt.continuousWithinAt
  · lift n to ℕ using hn.le with m
    rcases m with _ | _ | k
    · exact absurd rfl hn.ne'
    · have hfn : polylog ((0 + 1 : ℕ) : ℤ) = fun z : ℂ ↦ -Complex.log (1 - z) :=
        funext polylog_one
      rw [hfn, ContinuousWithinAt]
      have hre : (1 - (x : ℂ)).re < 0 := by simpa using sub_neg.2 hx
      have him : (1 - (x : ℂ)).im = 0 := by simp
      have hmaps : MapsTo (fun z : ℂ ↦ 1 - z) {z : ℂ | z.im ≤ 0} {w : ℂ | 0 ≤ w.im} := by
        intro z hz
        simpa using hz
      have hcont : Continuous (fun z : ℂ ↦ 1 - z) := by fun_prop
      exact ((Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto.comp
        ((hcont.continuousWithinAt (x := (x : ℂ))).tendsto_nhdsWithin hmaps)).neg
    · have hfn : polylog (↑(k + 1 + 1)) = fun z : ℂ ↦ (k.factorial : ℂ)⁻¹ *
          ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / t :=
        funext (polylog_nat_add_two k)
      rw [hfn, ContinuousWithinAt]
      refine tendsto_const_nhds.mul ?_
      simpa only [id_eq] using
        tendsto_integral_radialIntegrand_of_tendsto_ae k (φ := id)
          ⟨‖(x : ℂ)‖ + 1,
            (tendsto_norm.eventually (Iic_mem_nhds (lt_add_one _))).filter_mono nhdsWithin_le_nhds⟩
          (ae_tendsto_log_one_sub_mul_im_nonpos hx)

/-- Approaching a cut point `x > 1` from the open upper half-plane `{z : ℂ | 0 < z.im}`,
`polylog n z` tends to `conj (polylog n x)` in every integer weight `n`. -/
theorem tendsto_polylog_nhdsWithin_im_pos (n : ℤ) {x : ℝ} (hx : 1 < x) :
    Tendsto (polylog n) (𝓝[{z : ℂ | 0 < z.im}] x) (𝓝 (conj (polylog n x))) := by
  have hmaps : MapsTo conj {z : ℂ | 0 < z.im} {w : ℂ | w.im ≤ 0} := by
    intro z hz
    dsimp only [mem_ofPred_eq] at hz ⊢
    rw [Complex.conj_im, Left.neg_nonpos_iff]
    exact hz.le
  have hconj_tendsto : Tendsto conj (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝[{w : ℂ | w.im ≤ 0}] (x : ℂ)) := by
    have hcont : ContinuousWithinAt conj {z : ℂ | 0 < z.im} (x : ℂ) :=
      Complex.continuous_conj.continuousWithinAt
    simpa using hcont.tendsto_nhdsWithin hmaps
  have hlim : Tendsto (fun z : ℂ ↦ conj (polylog n (conj z)))
      (𝓝[{z : ℂ | 0 < z.im}] x) (𝓝 (conj (polylog n x))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp
      ((continuousWithinAt_polylog_im_nonpos n hx).tendsto.comp hconj_tendsto)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hmem : 1 - z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr (by simp [hz.ne']))
  rw [polylog_conj n hmem, RCLike.conj_conj]

/-- Lower vertical-ray boundary limit at `x > 1`: `polylog n (x - t * I) → polylog n x` as
`t → 0⁺` for every integer weight `n`. -/
theorem tendsto_polylog_sub_mul_I (n : ℤ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n ((x : ℂ) - t * Complex.I)) (𝓝[>] 0) (𝓝 (polylog n x)) := by
  have hcont : Continuous (fun t : ℝ ↦ (x : ℂ) - t * Complex.I) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ ↦ (x : ℂ) - t * Complex.I) (Ioi 0) {z : ℂ | z.im ≤ 0} := by
    intro t ht
    simp [ht.le]
  have hray : Tendsto (fun t : ℝ ↦ (x : ℂ) - t * Complex.I) (𝓝[>] 0)
      (𝓝[{z : ℂ | z.im ≤ 0}] x) := by
    simpa using (hcont.continuousWithinAt (x := (0 : ℝ))).tendsto_nhdsWithin hmaps
  exact (continuousWithinAt_polylog_im_nonpos n hx).tendsto.comp hray

/-- Upper vertical-ray boundary limit at `x > 1`: `polylog n (x + t * I) → conj (polylog n x)` as
`t → 0⁺` for every integer weight `n`. -/
theorem tendsto_polylog_add_mul_I (n : ℤ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n ((x : ℂ) + t * Complex.I)) (𝓝[>] 0)
      (𝓝 (conj (polylog n x))) := by
  have hcont : Continuous (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) (Ioi 0) {z : ℂ | 0 < z.im} := by
    intro t ht
    simpa using ht
  have hray : Tendsto (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 < z.im}] x) := by
    simpa using (hcont.continuousWithinAt (x := (0 : ℝ))).tendsto_nhdsWithin hmaps
  exact (tendsto_polylog_nhdsWithin_im_pos n hx).comp hray

/-- **The principal jump of the polylogarithm across `(1, ∞)`.** For every positive weight `n ≥ 1`
and real `x > 1`, `polylog n (x + t * I) - polylog n (x - t * I)` tends to
`2 * π * I * (log x) ^ (n - 1) / (n - 1)!` as `t → 0⁺`. -/
theorem tendsto_polylog_jump {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n ((x : ℂ) + t * Complex.I) -
        polylog n ((x : ℂ) - t * Complex.I))
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ))) := by
  have hsub := (tendsto_polylog_add_mul_I n hx).sub (tendsto_polylog_sub_mul_I n hx)
  have hval : conj (polylog n x) - polylog n x =
      2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) := by
    have hconj : ∀ w : ℂ, conj w - w = -2 * (w.im : ℂ) * Complex.I := by
      intro w
      apply Complex.ext <;> simp
      ring
    rw [hconj, im_polylog_of_one_lt hn hx]
    push_cast
    ring
  rwa [hval] at hsub

/-- In nonpositive weight `n ≤ 0`, the jump across `(1, ∞)` vanishes. -/
theorem tendsto_polylog_jump_of_nonpos {n : ℤ} (hn : n ≤ 0) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n ((x : ℂ) + t * Complex.I) -
        polylog n ((x : ℂ) - t * Complex.I))
      (𝓝[>] 0) (𝓝 0) := by
  have hsub := (tendsto_polylog_add_mul_I n hx).sub (tendsto_polylog_sub_mul_I n hx)
  have hval : conj (polylog n x) - polylog n x = 0 := by
    rw [Complex.conj_eq_iff_im.2 (im_polylog_of_nonpos hn x), sub_self]
  rwa [hval] at hsub

/-- For every integer weight `n ≥ 1` and real `x > 1`, `polylog n` is not continuous at `x`. -/
theorem not_continuousAt_polylog_of_one_lt {n : ℤ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    ¬ ContinuousAt (polylog n) x := by
  lift n to ℕ using (zero_le_one.trans hn) with m
  have hm : 1 ≤ m := Int.ofNat_le.1 hn
  intro hc
  have hadd_cont : Continuous (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) := by fun_prop
  have hadd : Tendsto (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) (𝓝[>] 0) (𝓝 x) := by
    simpa using (hadd_cont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have heq : conj (polylog m x) = polylog m x :=
    tendsto_nhds_unique (tendsto_polylog_add_mul_I m hx) (hc.tendsto.comp hadd)
  have him0 : (polylog m x).im = 0 := Complex.conj_eq_iff_im.1 heq
  rw [im_polylog_of_one_lt hm hx, neg_mul, neg_div] at him0
  have hpos : 0 < Real.pi * Real.log x ^ (m - 1) / (m - 1).factorial := by
    have : 0 < Real.log x := Real.log_pos hx
    positivity
  linarith

/-- At `x = 3`, the weight-`1` polylogarithm jumps by `2 * π * I`. -/
theorem tendsto_polylog_one_jump_three :
    Tendsto (fun t : ℝ ↦ polylog 1 (3 + t * Complex.I) - polylog 1 (3 - t * Complex.I))
      (𝓝[>] 0) (𝓝 (2 * Real.pi * Complex.I)) := by
  simpa using tendsto_polylog_jump (n := 1) le_rfl (x := 3) (by norm_num)

/-- At weight `2` and `x > 1`, the imaginary part of the upper-minus-lower cut jump is
`2 * π * log x`. -/
theorem tendsto_im_polylog_two_jump {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ (polylog 2 ((x : ℂ) + t * Complex.I) -
        polylog 2 ((x : ℂ) - t * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * Real.log x)) := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_polylog_jump (n := 2) (by omega) hx)
  have hj : (2 * (Real.pi : ℂ) * Complex.I * (Real.log x : ℂ) ^ (2 - 1) /
      ((2 - 1).factorial : ℂ)) = ((2 * Real.pi * Real.log x : ℝ) : ℂ) * Complex.I := by
    norm_num
    ring
  rw [hj] at h
  simpa [Function.comp_def] using h

end TauCeti.Polylog
