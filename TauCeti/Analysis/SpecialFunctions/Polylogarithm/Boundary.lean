/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Complex.UpperLogContinuity
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Conj
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Boundary continuity and the principal jump of integer-weight polylogarithms

In weights `n ≥ 2`, the logarithmic radial integral defining `TauCeti.Polylog.polylog n` is
uniformly integrable on `(0, 1]` over bounded complex parameter families. Combining uniform
integrability with almost-everywhere convergence of Mathlib's principal logarithm yields both
unrestricted continuity off the open cut `(1, ∞)` (including the branch point `z = 1` and the
entire closed unit disc) and one-sided continuity across `(1, ∞)`.

Specifically:
* Off `(1, ∞)` (i.e. when `z.im ≠ 0 ∨ z.re ≤ 1`), `polylog n` is continuous at `z` whenever
  `z ≠ 1 ∨ 2 ≤ n`: for `z ≠ 1` this follows immediately from holomorphy on the slit plane
  (`analyticAt_polylog`), and at `z = 1` in weights `n ≥ 2` every radial argument `1 - t` with
  `t ∈ (0, 1)` lies in the open slit plane.
* On the closed lower half-plane `{z | z.im ≤ 0}`, `1 - t z` lies in the closed upper half-plane,
  where Mathlib's principal logarithm is continuous away from `0` (including along the negative
  real axis). Since `1 - t z` vanishes at most once on `(0, 1]`, `polylog n` (`2 ≤ n`) is
  continuous on all of `{z | z.im ≤ 0}`, and `polylog n` for arbitrary `n : ℤ` is continuous
  within `{z | z.im ≤ 0}` whenever `z ≠ 1 ∨ 2 ≤ n`. Thus `polylog n x` is the lower boundary limit
  `lim_{t → 0+} polylog n (x - t I)` along `ℝ` (away from `x = 1` when `n ≤ 1`).
* On `(1, ∞)` in positive weight `n ≥ 1`, splitting `(0, 1]` at `x⁻¹` evaluates the imaginary part
  `(polylog n x).im = -π (log x) ^ (n - 1) / (n - 1)!`. Conjugation symmetry off `(1, ∞)` relates
  the upper boundary limit `lim_{t → 0+} polylog n (x + t I)` to `conj (polylog n x)`, giving the
  principal jump `2 π i (log x) ^ (n - 1) / (n - 1)!`, pointwise discontinuity along `(1, ∞)`, and
  the characterization `ContinuousAt (polylog n) z ↔ z.im ≠ 0 ∨ z.re ≤ 1` for `2 ≤ n`.

## Main declarations

* `TauCeti.Polylog.continuousAt_polylog_of_im_ne_zero_or_re_le_one` and
  `TauCeti.Polylog.continuousAt_polylog_iff`: unrestricted continuity off `(1, ∞)` (and its
  iff characterization for `2 ≤ n`).
* `TauCeti.Polylog.continuousWithinAt_polylog_im_nonpos`: continuity within the closed lower
  half-plane.
* `TauCeti.Polylog.polylog_ofReal_im_of_one_lt`:
  `(polylog n x).im = -π (log x) ^ (n - 1) / (n - 1)!` for `1 ≤ n` and `1 < x`.
* `TauCeti.Polylog.tendsto_polylog_nhdsWithin_im_neg`,
  `TauCeti.Polylog.tendsto_polylog_nhdsWithin_im_pos`,
  `TauCeti.Polylog.tendsto_polylog_sub_mul_I_nhdsGT_zero`,
  `TauCeti.Polylog.tendsto_polylog_nhdsWithin_im_pos_of_one_lt`,
  `TauCeti.Polylog.tendsto_polylog_add_mul_I_nhdsGT_zero_of_one_lt`, and
  `TauCeti.Polylog.tendsto_polylog_add_mul_I_sub_polylog_sub_mul_I_nhdsGT_zero_of_one_lt`: lower
  and upper boundary limits along `ℝ`, and upper boundary limit and principal jump across `(1, ∞)`.
* `TauCeti.Polylog.not_continuousAt_of_one_lt_of_eqOn_polylog`,
  `TauCeti.Polylog.not_continuousAt_polylog_of_one_lt`, and
  `TauCeti.Polylog.not_exists_continuousOn_eqOn_polylog`: cut discontinuity on `(1, ∞)` for
  `1 ≤ n` and non-existence of a continuous extension on `ℂ ∖ {0, 1}`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.3, (6), p. 51, §1.4, p. 51, and §2.2, (8), p. 53.
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

/-- Every integer-weight polylogarithm `polylog n` is continuous at any complex point `z` off the
open cut `(1, ∞)` (i.e. `z.im ≠ 0 ∨ z.re ≤ 1`) whenever `z ≠ 1 ∨ 2 ≤ n`. -/
theorem continuousAt_polylog_of_im_ne_zero_or_re_le_one {n : ℤ} {z : ℂ} (hn : z ≠ 1 ∨ 2 ≤ n)
    (hz : z.im ≠ 0 ∨ z.re ≤ 1) : ContinuousAt (polylog n) z := by
  by_cases hz1 : z = 1
  · subst hz1
    have hn2 : 2 ≤ n := hn.resolve_left (not_not.mpr rfl)
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k + 2 : ℕ) := ⟨(n - 2).toNat, by omega⟩
    refine tendsto_polylog_nat_add_two_of_ae_tendsto k tendsto_id ?_
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hslit : 1 - (t : ℂ) * 1 ∈ Complex.slitPlane := by
      rw [mul_one, Complex.mem_slitPlane_iff]
      exact Or.inl (by simp; linarith [ht.2])
    exact (continuousAt_clog hslit).tendsto.comp
      ((by fun_prop : Continuous fun i : ℂ ↦ 1 - (t : ℂ) * i).tendsto 1)
  · exact (analyticAt_polylog n (z.one_sub_mem_slitPlane_iff.mpr ⟨hz, hz1⟩)).continuousAt

/-- Every integer-weight polylogarithm is continuous within the closed lower half-plane
`{w | w.im ≤ 0}` at every point `z` with `z ≠ 1 ∨ 2 ≤ n`. -/
theorem continuousWithinAt_polylog_im_nonpos (n : ℤ) {z : ℂ} (hz : z ≠ 1 ∨ 2 ≤ n) :
    ContinuousWithinAt (polylog n) {w : ℂ | w.im ≤ 0} z := by
  cases n with
  | negSucc r =>
    rw [Int.negSucc_eq]
    exact (analyticAt_polylog_neg_nat (r + 1)
      (hz.resolve_right (by omega))).continuousAt.continuousWithinAt
  | ofNat m =>
    rcases m with _ | _ | k
    · exact (analyticAt_polylog_neg_nat 0
        (hz.resolve_right (by decide))).continuousAt.continuousWithinAt
    · have hz1 : z ≠ 1 := hz.resolve_right (by decide)
      rw [Int.ofNat_eq_natCast, zero_add, Nat.cast_one,
        (funext polylog_one : polylog 1 = fun w ↦ -Complex.log (1 - w))]
      simpa [Pi.neg_def] using (continuousWithinAt_log_one_sub_ofReal_mul_im_nonpos zero_le_one
        (z := z) (by simpa [sub_ne_zero] using hz1.symm)).neg
    · rw [Int.ofNat_eq_natCast]
      refine tendsto_polylog_nat_add_two_of_ae_tendsto k nhdsWithin_le_nhds ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        Complex.ae_one_sub_ofReal_mul_ne_zero z] with t ht htz
      exact (continuousWithinAt_log_one_sub_ofReal_mul_im_nonpos ht.1.le htz).tendsto

/-- At any real `x` with `x ≠ 1 ∨ 2 ≤ n`, `polylog n x` is the limit of `polylog n z` as `z → x`
from the open lower half-plane `{z | z.im < 0}`. -/
theorem tendsto_polylog_nhdsWithin_im_neg (n : ℤ) {x : ℝ} (hx : x ≠ 1 ∨ 2 ≤ n) :
    Tendsto (polylog n) (𝓝[{z : ℂ | z.im < 0}] x) (𝓝 (polylog n x)) := by
  have hx' : (x : ℂ) ≠ 1 ∨ 2 ≤ n := hx.imp (fun h h1 ↦ h (by exact_mod_cast h1)) id
  exact (continuousWithinAt_polylog_im_nonpos n hx').mono fun _ hz ↦ hz.out.le

/-- Lower boundary limit along `ℝ`: for integer weight `n` and real `x` with `x ≠ 1 ∨ 2 ≤ n`,
`polylog n (x - t * I) → polylog n x` as `t → 0+`. -/
theorem tendsto_polylog_sub_mul_I_nhdsGT_zero (n : ℤ) {x : ℝ} (hx : x ≠ 1 ∨ 2 ≤ n) :
    Tendsto (fun t : ℝ ↦ polylog n (x - t * Complex.I)) (𝓝[>] 0) (𝓝 (polylog n x)) :=
  (tendsto_polylog_nhdsWithin_im_neg n hx).comp
    (Real.tendsto_ofReal_sub_mul_I_nhdsWithin_im_neg x)

/-- Imaginary part of the radial integrand at a real parameter `x`. -/
private lemma im_radialIntegrand_ofReal (k : ℕ) (t x : ℝ) :
    (((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * (x : ℂ))) / (t : ℂ)).im =
      -((-Real.log t) ^ k / t) * ((1 : ℂ) - (t : ℂ) * (x : ℂ)).arg := by
  simp only [div_eq_mul_inv, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_zero, Complex.neg_im,
    Complex.log_im]
  ring

/-- Imaginary part of the radial integral on `(1, ∞)` obtained by splitting `[0, 1]` at `x⁻¹`. -/
private lemma im_integral_radialIntegrand_of_one_lt (k : ℕ) {x : ℝ} (hx : 1 < x) :
    (∫ t : ℝ in (0 : ℝ)..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * x)) / t).im =
      -Real.pi * (Real.log x ^ (k + 1) / (k + 1 : ℝ)) := by
  have hx_inv_pos : 0 < x⁻¹ := inv_pos.mpr (zero_lt_one.trans hx)
  have hx_inv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx.le
  have h0_notMem : (0 : ℝ) ∉ uIcc x⁻¹ 1 := by
    rw [uIcc_of_le hx_inv_le]
    intro h0
    linarith [h0.1]
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
    simp only [g, im_radialIntegrand_ofReal, harg, mul_zero]
  have h2 : ∫ t in x⁻¹..1, (g t).im = -Real.pi * ∫ t in x⁻¹..1, (-Real.log t) ^ k / t := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hx_inv_le,
      intervalIntegral.integral_of_le hx_inv_le]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have htx : x⁻¹ * x < t * x := mul_lt_mul_of_pos_right ht.1 (zero_lt_one.trans hx)
    rw [inv_mul_cancel₀ (zero_lt_one.trans hx).ne'] at htx
    have harg : ((1 : ℂ) - (t : ℂ) * (x : ℂ)).arg = Real.pi := by
      simpa using Complex.arg_ofReal_of_neg (by linarith : 1 - t * x < 0)
    simp only [g, im_radialIntegrand_ofReal, harg]
    ring
  have h_log_int : ∫ t in x⁻¹..1, (-Real.log t) ^ k / t = Real.log x ^ (k + 1) / (k + 1 : ℝ) := by
    simp_rw [neg_pow (Real.log _), mul_div_assoc]
    rw [intervalIntegral.integral_const_mul, TauCeti.integral_log_pow_div_self k h0_notMem]
    have hneg : (-1 : ℝ) ^ k * -((-1 : ℝ) ^ (k + 1)) = 1 := by
      rw [pow_succ, mul_neg_one, neg_neg, ← mul_pow]; norm_num
    simp only [Real.log_one, zero_pow (Nat.succ_ne_zero k), zero_sub, Real.log_inv,
      neg_pow (Real.log x)]
    linear_combination (Real.log x ^ (k + 1) / (k + 1 : ℝ)) * hneg
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂, Complex.add_im,
    him_int _ _ hint₁, him_int _ _ hint₂, h1, h2, h_log_int, zero_add]

/-- On the cut `(1, ∞)`, the total value `polylog n x` (`1 ≤ n`) has imaginary part
`-π (log x) ^ (n - 1) / (n - 1)!`. -/
theorem polylog_ofReal_im_of_one_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    (polylog n x).im = -Real.pi * Real.log x ^ (n - 1) / (n - 1).factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rcases m with _ | k
  · simp only [zero_add, Nat.cast_one, polylog_one, Nat.sub_self, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one, Complex.neg_im, Complex.log_im]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.arg_ofReal_of_neg (sub_neg.mpr hx)]
  · rw [Nat.add_sub_cancel, Nat.add_assoc, polylog_nat_add_two, Complex.mul_im,
      im_integral_radialIntegrand_of_one_lt k hx, Nat.factorial_succ]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

/-- Approaching real `x` (`x ≠ 1 ∨ 2 ≤ n`) from the open upper half-plane `{z | 0 < z.im}`,
`polylog n z` tends to `conj (polylog n x)`. -/
theorem tendsto_polylog_nhdsWithin_im_pos (n : ℤ) {x : ℝ} (hx : x ≠ 1 ∨ 2 ≤ n) :
    Tendsto (polylog n) (𝓝[{z : ℂ | 0 < z.im}] x) (𝓝 (conj (polylog n x))) := by
  have hlim := Complex.continuous_conj.continuousAt.tendsto.comp
    ((tendsto_polylog_nhdsWithin_im_neg n hx).comp
      (by simpa using Complex.tendsto_conj_nhdsWithin_im_pos (x : ℂ)))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  dsimp only [Function.comp_def]
  rw [polylog_conj n (Or.inl hz.ne'), Complex.conj_conj]

/-- On `(1, ∞)` in positive weight `n ≥ 1`, `conj (polylog n x)` differs from `polylog n x` by
`2 π i (log x) ^ (n - 1) / (n - 1)!`. -/
theorem conj_polylog_of_one_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    conj (polylog n x) = polylog n x +
      2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) := by
  have h := Complex.sub_conj (polylog n x)
  rw [polylog_ofReal_im_of_one_lt hn hx] at h
  push_cast at h
  linear_combination -h

/-- Approaching `x > 1` from the open upper half-plane `{z | 0 < z.im}` in positive weight
`n ≥ 1`, `polylog n z` tends to `polylog n x + 2 π i (log x) ^ (n - 1) / (n - 1)!`. -/
theorem tendsto_polylog_nhdsWithin_im_pos_of_one_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    Tendsto (polylog n) (𝓝[{z : ℂ | 0 < z.im}] x)
      (𝓝 (polylog n x +
        2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ))) := by
  rw [← conj_polylog_of_one_lt hn hx]
  exact tendsto_polylog_nhdsWithin_im_pos n (Or.inl hx.ne')

/-- Upper boundary limit on `(1, ∞)`: for natural `n ≥ 1` and real `x > 1`,
`polylog n (x + t * I) → polylog n x + 2 π i (log x) ^ (n - 1) / (n - 1)!` as `t → 0+`. -/
theorem tendsto_polylog_add_mul_I_nhdsGT_zero_of_one_lt {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n (x + t * Complex.I)) (𝓝[>] 0)
      (𝓝 (polylog n x +
        2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ))) :=
  (tendsto_polylog_nhdsWithin_im_pos_of_one_lt hn hx).comp
    (Real.tendsto_ofReal_add_mul_I_nhdsWithin_im_pos x)

/-- Principal jump formula across `(1, ∞)`: for natural `n ≥ 1` and real `x > 1`,
`polylog n (x + t * I) - polylog n (x - t * I)` tends to
`2 π i (log x) ^ (n - 1) / (n - 1)!` as `t → 0+`. -/
theorem tendsto_polylog_add_mul_I_sub_polylog_sub_mul_I_nhdsGT_zero_of_one_lt {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 1 < x) :
    Tendsto (fun t : ℝ ↦ polylog n (x + t * Complex.I) - polylog n (x - t * Complex.I)) (𝓝[>] 0)
      (𝓝 (2 * Real.pi * Complex.I * (Real.log x : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ))) := by
  simpa using (tendsto_polylog_add_mul_I_nhdsGT_zero_of_one_lt hn hx).sub
    (tendsto_polylog_sub_mul_I_nhdsGT_zero n (Or.inl hx.ne'))

/-- For integer weight `n ≥ 1` and real `x > 1`, no function agreeing with `polylog n` on the
doubly slit plane `{z | z ∈ slitPlane ∧ 1 - z ∈ slitPlane}` is continuous at `x`. -/
theorem not_continuousAt_of_one_lt_of_eqOn_polylog {n : ℤ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x)
    {g : ℂ → ℂ}
    (hg : EqOn g (polylog n) {z : ℂ | z ∈ Complex.slitPlane ∧ 1 - z ∈ Complex.slitPlane}) :
    ¬ ContinuousAt g x := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  have hm : 1 ≤ m := by omega
  intro hgx
  have hpath_pos : Tendsto (fun t : ℝ ↦ g (x + t * Complex.I)) (𝓝[>] 0) (𝓝 (g x)) :=
    (hgx.tendsto.mono_left nhdsWithin_le_nhds).comp
      (Real.tendsto_ofReal_add_mul_I_nhdsWithin_im_pos x)
  have hpath_neg : Tendsto (fun t : ℝ ↦ g (x - t * Complex.I)) (𝓝[>] 0) (𝓝 (g x)) :=
    (hgx.tendsto.mono_left nhdsWithin_le_nhds).comp
      (Real.tendsto_ofReal_sub_mul_I_nhdsWithin_im_neg x)
  have hg_diff : Tendsto (fun t : ℝ ↦ g (x + t * Complex.I) - g (x - t * Complex.I))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hpath_pos.sub hpath_neg
  have hmem {w : ℂ} (hw : w.im ≠ 0) :
      w ∈ {z : ℂ | z ∈ Complex.slitPlane ∧ 1 - z ∈ Complex.slitPlane} :=
    ⟨Complex.mem_slitPlane_iff.mpr (Or.inr hw),
      Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [hw]))⟩
  have heq : (fun t : ℝ ↦ g (x + t * Complex.I) - g (x - t * Complex.I)) =ᶠ[𝓝[>] 0]
      fun t : ℝ ↦ polylog m (x + t * Complex.I) - polylog m (x - t * Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [hg (hmem (w := x + t * Complex.I) (by simp [ht.ne'])),
      hg (hmem (w := x - t * Complex.I) (by simp [ht.ne']))]
  have hzero := tendsto_nhds_unique (hg_diff.congr' heq)
    (tendsto_polylog_add_mul_I_sub_polylog_sub_mul_I_nhdsGT_zero_of_one_lt hm hx)
  have hlogx : (Real.log x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hx).ne'
  have hfac : (((m - 1).factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
    (pow_ne_zero _ hlogx)) hfac hzero.symm

/-- In positive integer weight `n ≥ 1`, `polylog n` is discontinuous at every point `x > 1` of the
open cut `(1, ∞)`. -/
theorem not_continuousAt_polylog_of_one_lt {n : ℤ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    ¬ ContinuousAt (polylog n) x :=
  not_continuousAt_of_one_lt_of_eqOn_polylog hn hx (eqOn_refl _ _)

/-- For integer weight `n ≥ 2`, `polylog n` is continuous at `z` if and only if `z` does not lie on
the open cut `(1, ∞)`, i.e. `z.im ≠ 0 ∨ z.re ≤ 1`. -/
theorem continuousAt_polylog_iff {n : ℤ} (hn : 2 ≤ n) {z : ℂ} :
    ContinuousAt (polylog n) z ↔ z.im ≠ 0 ∨ z.re ≤ 1 := by
  refine ⟨fun hc ↦ ?_, continuousAt_polylog_of_im_ne_zero_or_re_le_one (Or.inr hn)⟩
  by_contra! h
  have hz_eq : z = (z.re : ℂ) := Complex.ext (Complex.ofReal_re _).symm (by simp [h.1])
  exact not_continuousAt_polylog_of_one_lt (by omega) h.2 (hz_eq ▸ hc)

/-- For integer weight `n ≥ 1`, no continuous function on `ℂ ∖ {0, 1}` agrees with the principal
polylogarithm `polylog n` on the doubly slit plane `{z | z ∈ slitPlane ∧ 1 - z ∈ slitPlane}`. -/
theorem not_exists_continuousOn_eqOn_polylog {n : ℤ} (hn : 1 ≤ n) :
    ¬ ∃ g : ℂ → ℂ, ContinuousOn g ({0, 1} : Set ℂ)ᶜ ∧
      EqOn g (polylog n) {z : ℂ | z ∈ Complex.slitPlane ∧ 1 - z ∈ Complex.slitPlane} := by
  rintro ⟨g, hg_cont, hg_eq⟩
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) :=
    (isClosed_singleton.union isClosed_singleton).isOpen_compl
  exact not_continuousAt_of_one_lt_of_eqOn_polylog hn (x := 3) (by norm_num) hg_eq
    (hg_cont.continuousAt (hopen.mem_nhds (by norm_num)))

end TauCeti.Polylog
