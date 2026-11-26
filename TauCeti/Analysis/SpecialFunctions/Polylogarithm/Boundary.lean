/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Conj
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Continuity
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Nonpositive
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Boundary continuity and the principal jump of integer-weight polylogarithms

In weights `n ≥ 2`, `TauCeti.Analysis.SpecialFunctions.Polylogarithm.Continuity` establishes both
unrestricted continuity of `polylog n` away from `(1, ∞)` (and away from `z = 1` when `n ≤ 1`,
since continuity at `z = 1` requires `2 ≤ n`) and continuity within the closed lower half-plane
`{w | w.im ≤ 0}` (again for `z ≠ 1 ∨ 2 ≤ n`). This file deduces the lower and upper boundary
limits along `ℝ`, evaluates the imaginary part and principal jump across the branch cut `(1, ∞)`,
and characterizes `ContinuousAt (polylog n) z` for every integer weight `n : ℤ`.

Specifically:
* From continuity within `{w | w.im ≤ 0}` (`continuousWithinAt_polylog_im_nonpos`), `polylog n x`
  is the lower boundary limit `lim_{t → 0+} polylog n (x - t I)` along `ℝ` whenever `x ≠ 1 ∨ 2 ≤ n`
  (again continuity at `x = 1` requires `2 ≤ n`).
* On `(1, ∞)` in positive weight `n ≥ 1`, weight `n = 1` evaluates `(polylog 1 x).im = -π`
  directly from `-Complex.log (1 - x)`, while weights `n ≥ 2` split `(0, 1]` at `x⁻¹` to obtain
  `(polylog n x).im = -π (log x) ^ (n - 1) / (n - 1)!`.
* Conjugation symmetry (`TauCeti.Polylog.polylog_conj`) relates the upper boundary limit
  `lim_{t → 0+} polylog n (x + t I)` to `conj (polylog n x)`, giving the principal jump
  `2 π i (log x) ^ (n - 1) / (n - 1)!`, pointwise discontinuity along `(1, ∞)`, and the complete
  characterization `ContinuousAt (polylog n) z ↔ (z ≠ 1 ∨ 2 ≤ n) ∧ (n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1)`
  for all `n : ℤ`.

## Main declarations

* `TauCeti.Polylog.polylog_ofReal_im_of_one_lt`:
  `(polylog n x).im = -π (log x) ^ (n - 1) / (n - 1)!` for `1 ≤ n` and `1 < x`.
* `TauCeti.Polylog.tendsto_polylog_nhdsWithin_im_neg`,
  `TauCeti.Polylog.tendsto_polylog_nhdsWithin_im_pos`,
  `TauCeti.Polylog.tendsto_polylog_sub_mul_I_nhdsGT_zero`,
  `TauCeti.Polylog.conj_polylog_of_one_lt`,
  `TauCeti.Polylog.tendsto_polylog_nhdsWithin_im_pos_of_one_lt`,
  `TauCeti.Polylog.tendsto_polylog_add_mul_I_nhdsGT_zero_of_one_lt`, and
  `TauCeti.Polylog.tendsto_polylog_add_mul_I_sub_polylog_sub_mul_I_nhdsGT_zero_of_one_lt`: lower
  and upper boundary limits along `ℝ`, and upper boundary limit and principal jump across `(1, ∞)`.
* `TauCeti.Polylog.not_continuousAt_of_one_lt_of_eventuallyEq_polylog`,
  `TauCeti.Polylog.not_continuousAt_polylog_of_one_lt`,
  `TauCeti.Polylog.continuousAt_polylog_iff`, and
  `TauCeti.Polylog.not_exists_continuousOn_eqOn_polylog`: cut discontinuity on `(1, ∞)` for
  `1 ≤ n`, full characterization of `ContinuousAt (polylog n) z` for all `n : ℤ`, and
  non-existence of a continuous extension on `ℂ ∖ {0, 1}`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.3, (6), p. 51, §1.4, p. 51, and §2.2, (8), p. 53.
-/

public section

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology

namespace TauCeti.Polylog

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
  rw [polylog_conj n (Or.inr (Or.inl hz.ne')), Complex.conj_conj]

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

/-- For integer weight `n ≥ 1` and real `x > 1`, no function eventually equal to `polylog n` on
`{z : ℂ | z.im ≠ 0}` near `x` is continuous at `x`. -/
theorem not_continuousAt_of_one_lt_of_eventuallyEq_polylog {n : ℤ} (hn : 1 ≤ n) {x : ℝ}
    (hx : 1 < x) {g : ℂ → ℂ} (hg : g =ᶠ[𝓝[{z : ℂ | z.im ≠ 0}] (x : ℂ)] polylog n) :
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
  have heq_pos : (fun t : ℝ ↦ g (x + t * Complex.I)) =ᶠ[𝓝[>] 0]
      fun t : ℝ ↦ polylog m (x + t * Complex.I) :=
    ((Real.tendsto_ofReal_add_mul_I_nhdsWithin_im_pos x).mono_right
      (nhdsWithin_mono _ fun _ hz ↦ hz.out.ne')).eventually hg
  have heq_neg : (fun t : ℝ ↦ g (x - t * Complex.I)) =ᶠ[𝓝[>] 0]
      fun t : ℝ ↦ polylog m (x - t * Complex.I) :=
    ((Real.tendsto_ofReal_sub_mul_I_nhdsWithin_im_neg x).mono_right
      (nhdsWithin_mono _ fun _ hz ↦ hz.out.ne)).eventually hg
  have hzero := tendsto_nhds_unique (hg_diff.congr' (heq_pos.sub heq_neg))
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
  not_continuousAt_of_one_lt_of_eventuallyEq_polylog hn hx EventuallyEq.rfl

/-- Every integer-weight polylogarithm `polylog n` is continuous at `z : ℂ` if and only if
`(z ≠ 1 ∨ 2 ≤ n) ∧ (n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1)`. -/
theorem continuousAt_polylog_iff {n : ℤ} {z : ℂ} :
    ContinuousAt (polylog n) z ↔ (z ≠ 1 ∨ 2 ≤ n) ∧ (n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1) := by
  refine ⟨fun hc ↦ ?_, fun ⟨hn, hz⟩ ↦ continuousAt_polylog hn hz⟩
  rcases le_or_gt n 0 with hn | hn
  · obtain ⟨r, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact ⟨Or.inl fun h ↦ not_continuousAt_polylog_neg_nat_one r (h ▸ hc), Or.inl hn⟩
  · obtain ⟨_ | _ | k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
    · exact absurd hn (lt_irrefl 0)
    · have h1 := (Complex.one_sub_mem_slitPlane_iff z).mp (continuousAt_polylog_one_iff.mp hc)
      exact ⟨Or.inl h1.2, Or.inr h1.1⟩
    · refine ⟨Or.inr (by omega), Or.inr ?_⟩
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
  have hev : g =ᶠ[𝓝[{z : ℂ | z.im ≠ 0}] (3 : ℂ)] polylog n := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hg_eq ⟨Complex.mem_slitPlane_iff.mpr (Or.inr hz),
      Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hz))⟩
  exact not_continuousAt_of_one_lt_of_eventuallyEq_polylog hn (x := 3) (by norm_num) hev
    (hg_cont.continuousAt (hopen.mem_nhds (by norm_num)))

end TauCeti.Polylog
