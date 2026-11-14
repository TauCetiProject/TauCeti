/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.UpperLogContinuity
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Conjugation
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Boundary continuity and the principal jump of integer-weight polylogarithms

In weights `n ≥ 2`, the logarithmic radial integral defining `TauCeti.Polylog.polylog n` is
uniformly integrable on `(0, 1]` over bounded complex parameter families. Combining uniform
integrability with almost-everywhere convergence of Mathlib's principal logarithm yields both
unrestricted continuity off the open cut `(1, ∞)` (including the branch point `z = 1` and the
entire closed unit disc) and one-sided continuity across `(1, ∞)`.

Specifically:
* Off `(1, ∞)` (i.e. when `z.im ≠ 0 ∨ z.re ≤ 1`), for every `t ∈ (0, 1)` the radial argument
  `1 - t z` lies in the open slit plane, so `polylog n` (`2 ≤ n`) is continuous at `z` for
  unrestricted complex approach.
* On the closed lower half-plane `{z | z.im ≤ 0}`, `1 - t z` lies in the closed upper half-plane,
  where Mathlib's principal logarithm is continuous away from `0` (including along the negative
  real axis). Since `1 - t z` vanishes at most once on `(0, 1]`, `polylog n` (`2 ≤ n`) is
  continuous on all of `{z | z.im ≤ 0}`, and `polylog n` for arbitrary `n : ℤ` is continuous
  within `{z | z.im ≤ 0}` at every `z ≠ 1`. Thus the total value `polylog n x` on `(1, ∞)` is the
  lower boundary limit `lim_{t → 0+} polylog n (x - t I)`.
* On `(1, ∞)` in positive weight `n ≥ 1`, splitting `(0, 1]` at `x⁻¹` evaluates the imaginary part
  `(polylog n x).im = -π (log x) ^ (n - 1) / (n - 1)!`. Conjugation symmetry off `(1, ∞)` relates
  the upper boundary limit `lim_{t → 0+} polylog n (x + t I)` to `conj (polylog n x)`, giving the
  principal jump `2 π i (log x) ^ (n - 1) / (n - 1)!`.
* In weight two, the `+2 π log x` jump of `(polylog 2 z).im` cancels the `-2 π log x` jump of
  `arg (1 - z) * log ‖z‖`, making `(polylog 2 z).im + arg (1 - z) * log ‖z‖` continuous on
  `ℂ ∖ {0}` (including `z = 1` and the cut `(1, ∞)`).

## Main declarations

* `TauCeti.Polylog.continuousAt_polylog_of_im_ne_zero_or_re_le_one`,
  `TauCeti.Polylog.continuousAt_polylog_one`, and `TauCeti.Polylog.continuousOn_polylog_closedBall`:
  unrestricted continuity of `polylog n` (`2 ≤ n`) off `(1, ∞)`, at `1`, and on the closed unit
  disc.
* `TauCeti.Polylog.continuousOn_polylog_im_nonpos` and
  `TauCeti.Polylog.continuousWithinAt_polylog_im_nonpos`: continuity on the closed lower
  half-plane.
* `TauCeti.Polylog.im_polylog_of_one_lt`: `(polylog n x).im = -π (log x) ^ (n - 1) / (n - 1)!` for
  `1 ≤ n` and `1 < x`.
* `TauCeti.Polylog.tendsto_polylog_sub_mul_I_nhdsGT_zero`,
  `TauCeti.Polylog.tendsto_polylog_add_mul_I_nhdsGT_zero`, and
  `TauCeti.Polylog.tendsto_polylog_add_mul_I_sub_nhdsGT_zero`: lower and upper boundary limits and
  the principal jump across `(1, ∞)`.
* `TauCeti.Polylog.not_exists_continuousOn_eqOn_polylog`: no continuous function on `ℂ ∖ {0, 1}`
  agrees with `polylog n` (`1 ≤ n`) on the doubly slit plane.
* `TauCeti.Polylog.continuousAt_im_polylog_two_add_arg_mul_log_norm` and
  `TauCeti.Polylog.continuousOn_im_polylog_two_add_arg_mul_log_norm`: continuity of
  `(polylog 2 z).im + (1 - z).arg * log ‖z‖` away from `0`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.3, (6), p. 51, §1.4, p. 51, and §2.2, (8), p. 53.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, §2, pp. 10–11.
-/

public section

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology

namespace TauCeti.Polylog

/-- Vitali convergence for the radial integral of `polylog (k + 2)` along a countably generated
filter when `Log (1 - t z)` converges almost everywhere on `(0, 1]`. -/
private lemma tendsto_polylog_nat_add_two_of_ae_tendsto {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (k : ℕ) {z : ι → ℂ} {z₀ : ℂ} (hz : Tendsto z l (𝓝 z₀))
    (hlog : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 1),
      Tendsto (fun i ↦ Complex.log (1 - (t : ℂ) * z i)) l
        (𝓝 (Complex.log (1 - (t : ℂ) * z₀)))) :
    Tendsto (fun i ↦ polylog (k + 2 : ℕ) (z i)) l (𝓝 (polylog (k + 2 : ℕ) z₀)) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  set w : ℕ → ℂ := z ∘ u
  have hw : Tendsto w atTop (𝓝 z₀) := hz.comp hu
  have hui :=
    (uniformIntegrable_radialIntegrand k (Metric.isBounded_range_of_tendsto w hw)).unifIntegrable
  set F : ℕ → ℝ → ℂ := fun m t ↦
    ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * w m)) / t
  set f : ℝ → ℂ := fun t ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z₀)) / t
  have hF_int : ∀ m, Integrable (F m) (volume.restrict (Ioc 0 1)) :=
    fun m ↦ (intervalIntegrable_radialIntegrand k (w m)).1
  have hf_mem : MemLp f 1 (volume.restrict (Ioc 0 1)) :=
    memLp_one_iff_integrable.mpr (intervalIntegrable_radialIntegrand k z₀).1
  have hae : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 1), Tendsto (fun m ↦ F m t) atTop (𝓝 (f t)) := by
    filter_upwards [hlog] with t ht
    exact (tendsto_const_nhds.mul (ht.comp hu).neg).div_const (t : ℂ)
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun m ↦ (hF_int m).aestronglyMeasurable) hf_mem hui hae
  have hint := tendsto_const_nhds (x := ((Nat.factorial k : ℂ)⁻¹)).mul
    (tendsto_integral_of_L1' f (Eventually.of_forall hF_int) hL1)
  simpa only [Function.comp_def, polylog_nat_add_two, intervalIntegral.integral_of_le zero_le_one,
    F, f, w] using hint

/-- For integer weight `n ≥ 2`, `polylog n` is continuous at every complex point off the open cut
`(1, ∞)` (that is, whenever `z.im ≠ 0 ∨ z.re ≤ 1`), including `z = 1`. -/
theorem continuousAt_polylog_of_im_ne_zero_or_re_le_one {n : ℤ} (hn : 2 ≤ n) {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re ≤ 1) : ContinuousAt (polylog n) z := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = ((k + 2 : ℕ) : ℤ) := ⟨(n - 2).toNat, by omega⟩
  refine tendsto_polylog_nat_add_two_of_ae_tendsto k tendsto_id ?_
  have hIoo : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 1), t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1) (μ := volume))] with t ht h
    exact h.mpr ht
  filter_upwards [hIoo] with t ht
  have hslit : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases hz with hzim | hzre
    · exact Or.inr (by simp [ht.1.ne', hzim])
    · exact Or.inl (by simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; nlinarith [ht.1, ht.2])
  exact (continuousAt_clog hslit).tendsto.comp
    ((by fun_prop : Continuous fun i : ℂ ↦ 1 - (t : ℂ) * i).tendsto z)

/-- For integer weight `n ≥ 2`, `polylog n` is continuous at `1` for unrestricted complex
approach. -/
theorem continuousAt_polylog_one {n : ℤ} (hn : 2 ≤ n) : ContinuousAt (polylog n) 1 :=
  continuousAt_polylog_of_im_ne_zero_or_re_le_one hn (Or.inr (by simp))

/-- For integer weight `n ≥ 2`, `polylog n` is continuous on the closed unit disc. -/
theorem continuousOn_polylog_closedBall {n : ℤ} (hn : 2 ≤ n) :
    ContinuousOn (polylog n) (Metric.closedBall 0 1) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  exact (continuousAt_polylog_of_im_ne_zero_or_re_le_one hn
    (Or.inr ((Complex.re_le_norm z).trans hz))).continuousWithinAt

/-- For integer weight `n ≥ 2`, `polylog n` is continuous on the entire closed lower half-plane
`{z | z.im ≤ 0}`, including `z = 1` and the cut `(1, ∞)`. -/
theorem continuousOn_polylog_im_nonpos {n : ℤ} (hn : 2 ≤ n) :
    ContinuousOn (polylog n) {z : ℂ | z.im ≤ 0} := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = ((k + 2 : ℕ) : ℤ) := ⟨(n - 2).toNat, by omega⟩
  intro z₀ hz₀
  rw [mem_ofPred_eq] at hz₀
  refine tendsto_polylog_nat_add_two_of_ae_tendsto k nhdsWithin_le_nhds ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (ae_one_sub_ofReal_mul_ne_zero z₀)] with t ht htz₀
  have hcont : Continuous fun w : ℂ ↦ 1 - (t : ℂ) * w := by fun_prop
  have him₀ : 0 ≤ (1 - (t : ℂ) * z₀).im := by
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_sub]
    nlinarith [ht.1, hz₀]
  have hmap : Tendsto (fun w : ℂ ↦ 1 - (t : ℂ) * w) (𝓝[{w : ℂ | w.im ≤ 0}] z₀)
      (𝓝[{u : ℂ | 0 ≤ u.im ∧ u ≠ 0}] (1 - (t : ℂ) * z₀)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hcont.continuousAt.eventually_ne htz₀)] with w hw hw_ne
    refine ⟨?_, hw_ne⟩
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_sub]
    nlinarith [ht.1, hw]
  exact (continuousOn_log_im_nonneg_ne_zero _ ⟨him₀, htz₀⟩).tendsto.comp hmap

/-- Every integer-weight polylogarithm is continuous within the closed lower half-plane
`{w | w.im ≤ 0}` at every point `z ≠ 1` with `z.im ≤ 0`. -/
theorem continuousWithinAt_polylog_im_nonpos (n : ℤ) {z : ℂ} (hz : z.im ≤ 0) (hz1 : z ≠ 1) :
    ContinuousWithinAt (polylog n) {w : ℂ | w.im ≤ 0} z := by
  cases n with
  | negSucc r =>
    rw [Int.negSucc_eq]
    exact (analyticAt_polylog_neg_nat (r + 1) hz1).continuousAt.continuousWithinAt
  | ofNat m =>
    rcases m with _ | _ | k
    · exact (analyticAt_polylog_neg_nat 0 hz1).continuousAt.continuousWithinAt
    · rw [Int.ofNat_eq_natCast, zero_add, Nat.cast_one,
        (funext polylog_one : polylog 1 = fun w ↦ -Complex.log (1 - w)), ContinuousWithinAt]
      have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
      have him : 0 ≤ (1 - z).im := by simp [hz]
      have hcont : Continuous fun w : ℂ ↦ 1 - w := by fun_prop
      have hmap : Tendsto (fun w : ℂ ↦ 1 - w) (𝓝[{w : ℂ | w.im ≤ 0}] z)
          (𝓝[{u : ℂ | 0 ≤ u.im ∧ u ≠ 0}] (1 - z)) := by
        refine tendsto_nhdsWithin_iff.mpr
          ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (hcont.continuousAt.eventually_ne h1z)] with w hw hw_ne
        exact ⟨by simp [hw], hw_ne⟩
      simpa only [Function.comp_def] using
        ((continuousOn_log_im_nonneg_ne_zero _ ⟨him, h1z⟩).tendsto.comp hmap).neg
    · rw [Int.ofNat_eq_natCast]
      exact continuousOn_polylog_im_nonpos (by omega) z hz

/-- On `(1, ∞)`, `polylog n x` is the limit of `polylog n z` as `z → x` from the open lower
half-plane `{z | z.im < 0}`. -/
theorem tendsto_polylog_nhdsWithin_im_neg (n : ℤ) {x : ℝ} (hx : 1 < x) :
    Tendsto (polylog n) (𝓝[{z : ℂ | z.im < 0}] x) (𝓝 (polylog n x)) :=
  (continuousWithinAt_polylog_im_nonpos n (by simp) (by exact_mod_cast hx.ne')).mono
    fun _ hz ↦ hz.out.le

/-- Lower boundary limit on `(1, ∞)`: for every integer weight `n` and real `x > 1`,
`polylog n (x - t * I) → polylog n x` as `t → 0+`. -/
theorem tendsto_polylog_sub_mul_I_nhdsGT_zero (n : ℤ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n (x - t * Complex.I)) (𝓝[>] 0) (𝓝 (polylog n x)) := by
  have hcont : Continuous fun t : ℝ ↦ (x : ℂ) - t * Complex.I := by fun_prop
  have hpath : Tendsto (fun t : ℝ ↦ (x : ℂ) - t * Complex.I) (𝓝[>] 0)
      (𝓝[{z : ℂ | z.im < 0}] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact (tendsto_polylog_nhdsWithin_im_neg n hx).comp hpath

/-- Auxiliary evaluation of `∫_{x⁻¹}^1 (-log t) ^ k / t dt` for `x > 1`. -/
private lemma integral_neg_log_pow_div_self (k : ℕ) {x : ℝ} (hx : 1 < x) :
    ∫ t : ℝ in x⁻¹..1, (-Real.log t) ^ k / t = Real.log x ^ (k + 1) / (k + 1 : ℝ) := by
  have hx_pos : 0 < x := zero_lt_one.trans hx
  have hx_inv_pos : 0 < x⁻¹ := inv_pos.mpr hx_pos
  have hx_inv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx.le
  set F : ℝ → ℝ := fun t ↦ -((-Real.log t) ^ (k + 1) / (k + 1 : ℝ))
  have hderiv : ∀ t ∈ uIcc x⁻¹ 1, HasDerivAt F ((-Real.log t) ^ k / t) t := by
    intro t ht
    rw [uIcc_of_le hx_inv_le] at ht
    have ht0 : t ≠ 0 := (hx_inv_pos.trans_le ht.1).ne'
    have hd := ((((Real.hasDerivAt_log ht0).neg).pow (k + 1)).div_const (k + 1 : ℝ)).neg
    refine hd.congr_deriv ?_
    dsimp only [Pi.neg_apply, Pi.pow_apply]
    have hk1 : (k + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ ↦ (-Real.log t) ^ k / t) volume x⁻¹ 1 := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx_inv_le] at ht
    have ht0 : t ≠ 0 := (hx_inv_pos.trans_le ht.1).ne'
    exact (((Real.continuousAt_log ht0).neg.pow k).div continuousAt_id ht0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [F, Real.log_one, neg_zero, zero_pow (Nat.succ_ne_zero k), zero_div, Real.log_inv,
    neg_neg, zero_sub]

/-- Imaginary part of the radial integral on `(1, ∞)` obtained by splitting `[0, 1]` at `x⁻¹`. -/
private lemma im_integral_radialIntegrand_of_one_lt (k : ℕ) {x : ℝ} (hx : 1 < x) :
    (∫ t : ℝ in (0 : ℝ)..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * x)) / t).im =
      -Real.pi * (Real.log x ^ (k + 1) / (k + 1 : ℝ)) := by
  have hx_inv_pos : 0 < x⁻¹ := inv_pos.mpr (zero_lt_one.trans hx)
  have hx_inv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx.le
  set g : ℝ → ℂ := fun t ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * x)) / t
  obtain ⟨hint₁, hint₂⟩ := (IntervalIntegrable.trans_iff
    (by rw [uIcc_of_le zero_le_one]; exact ⟨hx_inv_pos.le, hx_inv_le⟩)).mp
    (intervalIntegrable_radialIntegrand k x)
  have him_int (a b : ℝ) (hab : IntervalIntegrable g volume a b) :
      (∫ t in a..b, g t).im = ∫ t in a..b, (g t).im := by
    simpa using (Complex.imCLM.intervalIntegral_comp_comm hab).symm
  have h1 : ∫ t in (0 : ℝ)..x⁻¹, (g t).im = 0 := by
    rw [intervalIntegral.integral_of_le hx_inv_pos.le]
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ ?_
    have htx : t * x ≤ x⁻¹ * x := mul_le_mul_of_nonneg_right ht.2 (zero_lt_one.trans hx).le
    rw [inv_mul_cancel₀ (zero_lt_one.trans hx).ne'] at htx
    have harg : ((1 : ℂ) - (t : ℂ) * (x : ℂ)).arg = 0 := by
      simpa using Complex.arg_ofReal_of_nonneg (by linarith : 0 ≤ 1 - t * x)
    simp only [g, div_eq_mul_inv, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_zero, Complex.neg_im,
      Complex.log_im, harg, neg_zero]
  have h2 : ∫ t in x⁻¹..1, (g t).im = -Real.pi * ∫ t in x⁻¹..1, (-Real.log t) ^ k / t := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hx_inv_le,
      intervalIntegral.integral_of_le hx_inv_le]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have htx : x⁻¹ * x < t * x := mul_lt_mul_of_pos_right ht.1 (zero_lt_one.trans hx)
    rw [inv_mul_cancel₀ (zero_lt_one.trans hx).ne'] at htx
    have harg : ((1 : ℂ) - (t : ℂ) * (x : ℂ)).arg = Real.pi := by
      simpa using Complex.arg_ofReal_of_neg (by linarith : 1 - t * x < 0)
    simp only [g, div_eq_mul_inv, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_zero, Complex.neg_im,
      Complex.log_im, harg]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂, Complex.add_im,
    him_int _ _ hint₁, him_int _ _ hint₂, h1, zero_add, h2, integral_neg_log_pow_div_self k hx]

/-- On the cut `(1, ∞)`, the total value `polylog n x` (`1 ≤ n`) has imaginary part
`-π (log x) ^ (n - 1) / (n - 1)!`. -/
theorem im_polylog_of_one_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    (polylog n x).im = -Real.pi * Real.log x ^ (n - 1) / (n - 1).factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rcases m with _ | k
  · simp only [zero_add, Nat.cast_one, polylog_one, Nat.sub_self, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one, Complex.neg_im, Complex.log_im]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.arg_ofReal_of_neg (sub_neg.mpr hx)]
  · have hn_eq : k + 1 + 1 = k + 2 := rfl
    have hk2 : k + 2 - 1 = k + 1 := rfl
    rw [hn_eq, polylog_nat_add_two, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      im_integral_radialIntegrand_of_one_lt k hx, hk2, Nat.factorial_succ]
    push_cast
    field_simp

/-- On the cut at `3`, the dilogarithm has imaginary part `-π log 3`. -/
theorem im_polylog_two_three : (polylog 2 3).im = -Real.pi * Real.log 3 := by
  simpa using im_polylog_of_one_lt (n := 2) (by norm_num) (x := 3) (by norm_num)

/-- Approaching `x > 1` from the open upper half-plane `{z | 0 < z.im}`, `polylog n z` tends to
`conj (polylog n x)` for every integer weight `n`. -/
theorem tendsto_polylog_nhdsWithin_im_pos_conj (n : ℤ) {x : ℝ} (hx : 1 < x) :
    Tendsto (polylog n) (𝓝[{z : ℂ | 0 < z.im}] x) (𝓝 (conj (polylog n x))) := by
  have hconj_map : Tendsto (conj : ℂ → ℂ) (𝓝[{z : ℂ | 0 < z.im}] x)
      (𝓝[{w : ℂ | w.im < 0}] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (Complex.continuous_conj.tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have hlim := Complex.continuous_conj.continuousAt.tendsto.comp
    ((tendsto_polylog_nhdsWithin_im_neg n hx).comp hconj_map)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  dsimp only [Function.comp_def]
  rw [polylog_conj_of_im_ne_zero_or_re_le_one n (Or.inl hz.ne'), RingHomCompTriple.comp_apply,
    RingHom.id_apply]

/-- On `(1, ∞)` in positive weight `n ≥ 1`, `conj (polylog n x)` differs from `polylog n x` by
`2 π i (log x) ^ (n - 1) / (n - 1)!`. -/
theorem conj_polylog_of_one_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    conj (polylog n x) = polylog n x +
      2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) := by
  have h := Complex.sub_conj (polylog n x)
  rw [im_polylog_of_one_lt hn hx] at h
  push_cast at h
  linear_combination -h

/-- Approaching `x > 1` from the open upper half-plane `{z | 0 < z.im}` in positive weight
`n ≥ 1`, `polylog n z` tends to `polylog n x + 2 π i (log x) ^ (n - 1) / (n - 1)!`. -/
theorem tendsto_polylog_nhdsWithin_im_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    Tendsto (polylog n) (𝓝[{z : ℂ | 0 < z.im}] x)
      (𝓝 (polylog n x +
        2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ))) := by
  rw [← conj_polylog_of_one_lt hn hx]
  exact tendsto_polylog_nhdsWithin_im_pos_conj n hx

/-- Upper boundary limit on `(1, ∞)`: for natural `n ≥ 1` and real `x > 1`,
`polylog n (x + t * I) → polylog n x + 2 π i (log x) ^ (n - 1) / (n - 1)!` as `t → 0+`. -/
theorem tendsto_polylog_add_mul_I_nhdsGT_zero {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n (x + t * Complex.I)) (𝓝[>] 0)
      (𝓝 (polylog n x +
        2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ))) := by
  have hcont : Continuous fun t : ℝ ↦ (x : ℂ) + t * Complex.I := by fun_prop
  have hpath : Tendsto (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 < z.im}] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact (tendsto_polylog_nhdsWithin_im_pos hn hx).comp hpath

/-- Principal jump formula across `(1, ∞)`: for natural `n ≥ 1` and real `x > 1`,
`polylog n (x + t * I) - polylog n (x - t * I)` tends to
`2 π i (log x) ^ (n - 1) / (n - 1)!` as `t → 0+`. -/
theorem tendsto_polylog_add_mul_I_sub_nhdsGT_zero {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n (x + t * Complex.I) - polylog n (x - t * Complex.I)) (𝓝[>] 0)
      (𝓝 (2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ))) := by
  simpa using (tendsto_polylog_add_mul_I_nhdsGT_zero hn hx).sub
    (tendsto_polylog_sub_mul_I_nhdsGT_zero n hx)

/-- For natural `n ≥ 1`, no continuous function on `ℂ ∖ {0, 1}` agrees with the principal
polylogarithm `polylog n` on the doubly slit plane `{z | z ∈ slitPlane ∧ 1 - z ∈ slitPlane}`. -/
theorem not_exists_continuousOn_eqOn_polylog {n : ℕ} (hn : 1 ≤ n) :
    ¬ ∃ g : ℂ → ℂ, ContinuousOn g ({0, 1} : Set ℂ)ᶜ ∧
      EqOn g (polylog n) {z : ℂ | z ∈ Complex.slitPlane ∧ 1 - z ∈ Complex.slitPlane} := by
  rintro ⟨g, hg_cont, hg_eq⟩
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) :=
    (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have hg3 : ContinuousAt g 3 := hg_cont.continuousAt (hopen.mem_nhds (by norm_num))
  have hc_pos : Continuous fun t : ℝ ↦ (3 : ℂ) + t * Complex.I := by fun_prop
  have hc_neg : Continuous fun t : ℝ ↦ (3 : ℂ) - t * Complex.I := by fun_prop
  have hpath_pos : Tendsto (fun t : ℝ ↦ g (3 + t * Complex.I)) (𝓝[>] 0) (𝓝 (g 3)) :=
    (hg3.tendsto.comp (by simpa using hc_pos.tendsto 0)).mono_left nhdsWithin_le_nhds
  have hpath_neg : Tendsto (fun t : ℝ ↦ g (3 - t * Complex.I)) (𝓝[>] 0) (𝓝 (g 3)) :=
    (hg3.tendsto.comp (by simpa using hc_neg.tendsto 0)).mono_left nhdsWithin_le_nhds
  have hg_diff : Tendsto (fun t : ℝ ↦ g (3 + t * Complex.I) - g (3 - t * Complex.I))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hpath_pos.sub hpath_neg
  have heq : (fun t : ℝ ↦ g (3 + t * Complex.I) - g (3 - t * Complex.I)) =ᶠ[𝓝[>] 0]
      fun t : ℝ ↦ polylog n ((3 : ℝ) + t * Complex.I) - polylog n ((3 : ℝ) - t * Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hpos_mem : (3 : ℂ) + t * Complex.I ∈
        {z : ℂ | z ∈ Complex.slitPlane ∧ 1 - z ∈ Complex.slitPlane} :=
      ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [ht.ne'])),
        Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [ht.ne']))⟩
    have hneg_mem : (3 : ℂ) - t * Complex.I ∈
        {z : ℂ | z ∈ Complex.slitPlane ∧ 1 - z ∈ Complex.slitPlane} :=
      ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [ht.ne'])),
        Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [ht.ne']))⟩
    simp [hg_eq hpos_mem, hg_eq hneg_mem]
  have hzero := tendsto_nhds_unique (hg_diff.congr' heq)
    (tendsto_polylog_add_mul_I_sub_nhdsGT_zero hn (x := 3) (by norm_num))
  have hlog3 : (Real.log 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have hfac : (((n - 1).factorial : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
    (pow_ne_zero _ hlog3)) hfac hzero.symm

/-- Approaching `x > 1` from the open upper half-plane `{w | 0 < w.im}`, `(1 - w).arg` tends to
`-π`. -/
private lemma tendsto_arg_one_sub_nhdsWithin_im_pos {x : ℝ} (hx : 1 < x) :
    Tendsto (fun w : ℂ ↦ (1 - w).arg) (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)) (𝓝 (-Real.pi)) := by
  have hcont : Continuous fun w : ℂ ↦ 1 - w := by fun_prop
  have hmap : Tendsto (fun w : ℂ ↦ 1 - w) (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ))
      (𝓝[{u : ℂ | u.im < 0}] (1 - (x : ℂ))) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨(hcont.tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    simpa using hw
  exact (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (by simp [hx]) (by simp)).comp hmap

/-- Cancellation of jumps across `(1, ∞)` in weight two: `(polylog 2 w).im + (1 - w).arg * log ‖w‖`
is continuous at real `x > 1`. -/
private lemma continuousAt_im_polylog_two_add_arg_mul_log_norm_of_one_lt {x : ℝ} (hx : 1 < x) :
    ContinuousAt (fun w : ℂ ↦ (polylog 2 w).im + (1 - w).arg * Real.log ‖w‖) x := by
  set D : ℂ → ℝ := fun w ↦ (polylog 2 w).im + (1 - w).arg * Real.log ‖w‖
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
  have h1x : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx.ne)
  have hlog_norm : ContinuousAt (fun w : ℂ ↦ Real.log ‖w‖) x :=
    (Real.continuousAt_log (norm_ne_zero_iff.mpr hx0)).comp continuous_norm.continuousAt
  have him2 : (polylog 2 (x : ℂ)).im = -Real.pi * Real.log x := by
    simpa using im_polylog_of_one_lt (n := 2) (by norm_num) hx
  have hargx : (1 - (x : ℂ)).arg = Real.pi := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.arg_ofReal_of_neg (sub_neg.mpr hx)
  have hlogx : Real.log ‖(x : ℂ)‖ = Real.log x := by
    rw [Complex.norm_real, Real.norm_of_nonneg (zero_lt_one.trans hx).le]
  have hDx : D x = 0 := by
    simp only [D, him2, hargx, hlogx]
    ring
  have hunion : {w : ℂ | w.im ≤ 0} ∪ {w : ℂ | 0 < w.im} = univ := by
    ext w
    exact ⟨fun _ ↦ trivial, fun _ ↦ le_or_gt w.im 0⟩
  rw [ContinuousAt, ← nhdsWithin_univ, ← hunion, nhdsWithin_union, tendsto_sup]
  refine ⟨?_, ?_⟩
  · -- Lower closed half-plane: both terms are continuous within `{w | w.im ≤ 0}`.
    have hcont : Continuous fun w : ℂ ↦ 1 - w := by fun_prop
    have hmap : Tendsto (fun w : ℂ ↦ 1 - w) (𝓝[{w : ℂ | w.im ≤ 0}] (x : ℂ))
        (𝓝[{u : ℂ | 0 ≤ u.im ∧ u ≠ 0}] (1 - (x : ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr
        ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hcont.continuousAt.eventually_ne h1x)] with w hw hw_ne
      exact ⟨by simp [hw], hw_ne⟩
    have harg := (continuousOn_arg_im_nonneg_ne_zero _ ⟨by simp, h1x⟩).tendsto.comp hmap
    have hli := Complex.continuous_im.continuousAt.tendsto.comp
      (continuousOn_polylog_im_nonpos (n := 2) (by norm_num) (x : ℂ) (by simp)).tendsto
    exact hli.add (harg.mul (hlog_norm.tendsto.mono_left nhdsWithin_le_nhds))
  · -- Open upper half-plane: the `+π log x` and `-π log x` limits cancel to `0 = D x`.
    have hli : Tendsto (fun w : ℂ ↦ (polylog 2 w).im) (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ))
        (𝓝 (Real.pi * Real.log x)) := by
      have h := Complex.continuous_im.continuousAt.tendsto.comp
        (tendsto_polylog_nhdsWithin_im_pos_conj 2 hx)
      simpa [Function.comp_def, Complex.conj_im, him2] using h
    have hsum := hli.add ((tendsto_arg_one_sub_nhdsWithin_im_pos hx).mul
      (hlogx ▸ hlog_norm.tendsto.mono_left nhdsWithin_le_nhds))
    rw [hDx]
    simpa [mul_comm, neg_mul] using hsum

/-- The single-valued dilogarithm combination `(polylog 2 w).im + (1 - w).arg * log ‖w‖` is
continuous at every nonzero complex number `z ≠ 0` (including `z = 1` and the cut `(1, ∞)`). -/
theorem continuousAt_im_polylog_two_add_arg_mul_log_norm {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun w : ℂ ↦ (polylog 2 w).im + (1 - w).arg * Real.log ‖w‖) z := by
  have hlog_norm : ContinuousAt (fun w : ℂ ↦ Real.log ‖w‖) z :=
    (Real.continuousAt_log (norm_ne_zero_iff.mpr hz)).comp continuous_norm.continuousAt
  obtain rfl | hz1 := eq_or_ne z 1
  · -- At `z = 1`, `polylog 2` is continuous, `|(1 - w).arg| ≤ π`, and `log ‖w‖ → 0`.
    have hli : ContinuousAt (fun w : ℂ ↦ (polylog 2 w).im) 1 :=
      Complex.continuous_im.continuousAt.comp (continuousAt_polylog_one (by norm_num))
    have hupper : Tendsto (fun w : ℂ ↦ Real.pi * |Real.log ‖w‖|) (𝓝 1) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := Real.pi)).mul hlog_norm.abs.tendsto
    have hprod : Tendsto (fun w : ℂ ↦ (1 - w).arg * Real.log ‖w‖) (𝓝 1) (𝓝 0) :=
      squeeze_zero_norm
        (fun w ↦ by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi _) (abs_nonneg _))
        hupper
    simpa [ContinuousAt] using hli.tendsto.add hprod
  · by_cases hcut : z.im = 0 ∧ 1 < z.re
    · have hz_eq : z = (z.re : ℂ) := Complex.ext rfl (by simp [hcut.1])
      rw [hz_eq]
      exact continuousAt_im_polylog_two_add_arg_mul_log_norm_of_one_lt hcut.2
    · have hz_off : z.im ≠ 0 ∨ z.re ≤ 1 := by
        rcases ne_or_eq z.im 0 with him | him
        · exact Or.inl him
        · exact Or.inr (le_of_not_gt fun hgt ↦ hcut ⟨him, hgt⟩)
      have hslit : 1 - z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        rcases ne_or_eq z.im 0 with him | him
        · exact Or.inr (by simp [him])
        · refine Or.inl ?_
          have hlt : z.re < 1 := lt_of_le_of_ne (hz_off.resolve_left (not_not.mpr him))
            fun hre ↦ hz1 (Complex.ext hre him)
          simp [hlt]
      have hli : ContinuousAt (fun w : ℂ ↦ (polylog 2 w).im) z :=
        Complex.continuous_im.continuousAt.comp
          (continuousAt_polylog_of_im_ne_zero_or_re_le_one (by norm_num) hz_off)
      have harg : ContinuousAt (fun w : ℂ ↦ (1 - w).arg) z :=
        (Complex.continuousAt_arg hslit).comp (by fun_prop)
      exact hli.add (harg.mul hlog_norm)

/-- The single-valued dilogarithm combination `(polylog 2 w).im + (1 - w).arg * log ‖w‖` is
continuous on `ℂ ∖ {0}`. -/
theorem continuousOn_im_polylog_two_add_arg_mul_log_norm :
    ContinuousOn (fun w : ℂ ↦ (polylog 2 w).im + (1 - w).arg * Real.log ‖w‖) {z : ℂ | z ≠ 0} :=
  fun _ hz ↦ (continuousAt_im_polylog_two_add_arg_mul_log_norm hz).continuousWithinAt

end TauCeti.Polylog
