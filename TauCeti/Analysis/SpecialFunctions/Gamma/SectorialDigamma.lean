/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.GaussSeries
public import Mathlib.NumberTheory.AbelSummation
public import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
public import TauCeti.Analysis.Complex.SectorBounds
public import TauCeti.Analysis.Complex.SlitPlane
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Uniform sectorial digamma asymptotics

For `0 < δ < π`, uniformly on `|arg s| ≤ π - δ`,
`‖digamma s - log s‖ ≤ (1 + 4 / (1 - cos δ) ^ 2) / ‖s‖`.
In particular, the difference is `O(1 / ‖s‖)` along the cocompact filter on that sector.

The proof starts from Abel's finite summation formula for `(s + n)⁻¹`. Its remainder is an
integral of `fract t / (s + t)^2`. A sectorial denominator bound controls the integral uniformly
in the cutoff; Gauss' series identifies the limit. This gives the leading-order consequence of
[DLMF 5.11.2](https://dlmf.nist.gov/5.11.E2), with the explicit error bound above.

The finite summation identity is exposed separately for subsequent integral representations
and gamma asymptotics. All integral endpoints use Mathlib's oriented interval integral.
-/

public section

open Complex Real Filter Set Topology MeasureTheory intervalIntegral Asymptotics

namespace Complex

private theorem add_ofReal_mem_slitPlane {s : ℂ} (hs : s ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    s + t ∈ slitPlane := by
  simpa only [add_comm] using TauCeti.ofReal_add_mem_slitPlane hs ht

private theorem add_ofReal_ne_zero {s : ℂ} (hs : s ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    s + t ≠ 0 :=
  slitPlane_ne_zero (add_ofReal_mem_slitPlane hs ht)

private theorem add_natCast_ne_zero {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) : s + N ≠ 0 := by
  simpa only [ofReal_natCast] using add_ofReal_ne_zero hs (Nat.cast_nonneg N)

private theorem nonpole_of_mem_slitPlane {s : ℂ} (hs : s ∈ slitPlane) :
    ∀ n : ℕ, s ≠ -(n : ℂ) := by
  intro n hn
  rcases mem_slitPlane_iff.mp hs with h | h
  · rw [hn, neg_re, natCast_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · exact h (by simp [hn])

private theorem hasDerivAt_inv_add_ofReal {s : ℂ} {t : ℝ} (hs : s + t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ (s + (u : ℂ))⁻¹) (-1 / (s + t) ^ 2) t := by
  simpa using (((hasDerivAt_id (t : ℂ)).const_add s).inv hs).comp_ofReal

private theorem hasDerivAt_log_add_ofReal {s : ℂ} {t : ℝ} (hs : s + t ∈ slitPlane) :
    HasDerivAt (fun u : ℝ ↦ Complex.log (s + (u : ℂ))) ((s + t)⁻¹) t := by
  simpa using ((Complex.hasDerivAt_log hs).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_add s)).comp_ofReal

private theorem continuousOn_inv_add_ofReal_sq {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ContinuousOn (fun t : ℝ ↦ ((s + (t : ℂ)) ^ 2)⁻¹) (Icc 0 (N : ℝ)) :=
  ((continuousOn_const.add continuous_ofReal.continuousOn).pow 2).inv₀
    fun _ ht ↦ pow_ne_zero _ (add_ofReal_ne_zero hs ht.1)

private theorem continuousOn_add_one_div_add_sq {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ContinuousOn (fun t : ℝ ↦ ((t : ℂ) + 1) / (s + t) ^ 2) (Icc 0 (N : ℝ)) :=
  (continuous_ofReal.continuousOn.add continuousOn_const).div
    ((continuousOn_const.add continuous_ofReal.continuousOn).pow 2)
    fun _ ht ↦ pow_ne_zero _ (add_ofReal_ne_zero hs ht.1)

private theorem intervalIntegrable_fract_div_add_sq {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2) volume 0 N := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (Nat.cast_nonneg N)]
  simp only [div_eq_mul_inv]
  apply (continuousOn_inv_add_ofReal_sq hs N).integrableOn_Icc.bdd_mul
  · exact (continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
  · exact Eventually.of_forall fun t ↦ by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)] using
        (Int.fract_lt_one t).le

private theorem integral_add_one_div_add_sq {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ∫ t : ℝ in 0..(N : ℝ), ((t : ℂ) + 1) / (s + t) ^ 2 =
      Complex.log (s + N) + (s - 1) / (s + N) - (Complex.log s + (s - 1) / s) := by
  have hderiv (t : ℝ) (ht : t ∈ uIcc 0 (N : ℝ)) :
      HasDerivAt (fun u : ℝ ↦ Complex.log (s + (u : ℂ)) + (s - 1) / (s + u))
        (((t : ℂ) + 1) / (s + t) ^ 2) t := by
    rw [uIcc_of_le (Nat.cast_nonneg N)] at ht
    have h := (hasDerivAt_log_add_ofReal (add_ofReal_mem_slitPlane hs ht.1)).add
      ((hasDerivAt_inv_add_ofReal (add_ofReal_ne_zero hs ht.1)).const_mul (s - 1))
    convert h using 1
    · ext u
      simp only [div_eq_mul_inv, Pi.add_apply]
    · field_simp
      ring
  simpa only [Complex.ofReal_zero, add_zero, Complex.ofReal_natCast] using
    integral_eq_sub_of_hasDerivAt hderiv
      ((continuousOn_add_one_div_add_sq hs N).intervalIntegrable_of_Icc (Nat.cast_nonneg N))

/-- Abel summation with unit weights for `(s + k)⁻¹`, with the derivative of `(s + t)⁻¹` in the
remainder. -/
private theorem sum_inv_add_eq_sub_integral_floor {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ∑ k ∈ Finset.Icc 0 N, (s + k)⁻¹ = (s + N)⁻¹ * ((N : ℂ) + 1) -
      ∫ t in Ioc (0 : ℝ) N, -1 / (s + t) ^ 2 * ((⌊t⌋₊ : ℂ) + 1) := by
  let f : ℝ → ℂ := fun t ↦ (s + (t : ℂ))⁻¹
  have hd (t : ℝ) (ht : t ∈ Icc 0 (N : ℝ)) : HasDerivAt f (-1 / (s + t) ^ 2) t :=
    hasDerivAt_inv_add_ofReal (add_ofReal_ne_zero hs ht.1)
  have hc : ContinuousOn (fun t : ℝ ↦ -1 / (s + t) ^ 2) (Icc 0 (N : ℝ)) := by
    simpa only [div_eq_mul_inv] using (continuousOn_inv_add_ofReal_sq hs N).const_mul (-1)
  have hA := sum_mul_eq_sub_integral_mul' (fun _ : ℕ ↦ (1 : ℂ)) N
    (fun t ht ↦ (hd t ht).differentiableAt)
    (hc.integrableOn_Icc.congr_fun (fun t ht ↦ (hd t ht).deriv.symm) measurableSet_Icc)
  have hsum (m : ℕ) : ∑ k ∈ Finset.Icc 0 m, (1 : ℂ) = (m : ℂ) + 1 := by simp
  simp only [hsum, mul_one] at hA
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun t ht ↦ by rw [(hd t (Ioc_subset_Icc_self ht)).deriv])] at hA
  dsimp [f] at hA
  rw [hA]

/-- Splitting `⌊t⌋₊ + 1 = (t + 1) - fract t` separates the Abel remainder into a smooth kernel
and the fractional-part kernel. -/
private theorem integral_floor_eq_neg_add_integral_fract {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ∫ t in Ioc (0 : ℝ) N, -1 / (s + t) ^ 2 * ((⌊t⌋₊ : ℂ) + 1) =
      -(∫ t : ℝ in 0..(N : ℝ), ((t : ℂ) + 1) / (s + t) ^ 2) +
        ∫ t : ℝ in 0..(N : ℝ), ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2 := by
  rw [← integral_of_le (Nat.cast_nonneg N), ← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_add]
  · refine integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le (Nat.cast_nonneg N)] at ht
    have hfloor : (⌊t⌋₊ : ℂ) + ((Int.fract t : ℝ) : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_add]
      congr 1
      rw [natCast_floor_eq_intCast_floor ht.1, Int.floor_add_fract]
    linear_combination -((s + (t : ℂ)) ^ 2)⁻¹ * hfloor
  · exact ((continuousOn_add_one_div_add_sq hs N).intervalIntegrable_of_Icc
      (Nat.cast_nonneg N)).neg
  · exact intervalIntegrable_fract_div_add_sq hs N

/-- Abel summation for the reciprocal progression, with its exact fractional-part remainder.
The sum includes both endpoints; the integral ends at `N`. -/
theorem sum_inv_add_eq_log_sub_integral_fract {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ∑ k ∈ Finset.Icc 0 N, (s + k)⁻¹ = Complex.log (s + N) - Complex.log s + s⁻¹ -
      ∫ t : ℝ in 0..(N : ℝ), ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2 := by
  rw [sum_inv_add_eq_sub_integral_floor hs N, integral_floor_eq_neg_add_integral_fract hs N,
    integral_add_one_div_add_sq hs N]
  have hrat : (s + N)⁻¹ * (N + 1) + (s - 1) / (s + N) - (s - 1) / s = s⁻¹ := by
    field_simp [slitPlane_ne_zero hs, add_natCast_ne_zero hs N]
    ring
  linear_combination hrat

private theorem norm_integral_fract_div_add_sq_le {s : ℂ} (hs : s ∈ slitPlane) {c : ℝ}
    (hc : 0 < c) (hden : ∀ t : ℝ, 0 ≤ t → c * (‖s‖ + t) ≤ ‖s + t‖) (N : ℕ) :
    ‖∫ t : ℝ in 0..(N : ℝ), ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2‖ ≤
      1 / (c ^ 2 * ‖s‖) := by
  have hs0 : 0 < ‖s‖ := norm_pos_iff.mpr (slitPlane_ne_zero hs)
  have hg : ContinuousOn (fun t : ℝ ↦ 1 / (c ^ 2 * (‖s‖ + t) ^ 2))
      (Icc 0 (N : ℝ)) :=
    continuousOn_const.div (continuousOn_const.mul
      ((continuousOn_const.add continuousOn_id).pow 2))
      (fun t ht ↦ mul_ne_zero (pow_ne_zero _ hc.ne') (pow_ne_zero _ (by linarith [ht.1])))
  have hnorm (t : ℝ) (ht : 0 ≤ t) :
      ‖((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2‖ ≤ 1 / (c ^ 2 * (‖s‖ + t) ^ 2) := by
    rw [norm_div, norm_pow]
    have hn : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)] using
        (Int.fract_lt_one t).le
    have hpos : 0 < c ^ 2 * (‖s‖ + t) ^ 2 := by positivity
    have hsq : c ^ 2 * (‖s‖ + t) ^ 2 ≤ ‖s + t‖ ^ 2 := by
      nlinarith only [sq_le_sq₀ (by positivity : 0 ≤ c * (‖s‖ + t))
        (norm_nonneg (s + t)) |>.mpr (hden t ht)]
    exact (div_le_div_of_nonneg_right hn (sq_nonneg _)).trans
      (one_div_le_one_div_of_le hpos hsq)
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (Nat.cast_nonneg N)
    (Eventually.of_forall fun t ht ↦ hnorm t ht.1.le)
    (hg.intervalIntegrable_of_Icc (Nat.cast_nonneg N))
  refine hb.trans ?_
  have heq : (fun t : ℝ ↦ 1 / (c ^ 2 * (‖s‖ + t) ^ 2)) =
      fun t ↦ (c ^ 2)⁻¹ * (1 / (‖s‖ + t) ^ 2) := by
    funext t
    simp only [mul_inv_rev, one_div]
    ring
  rw [heq, intervalIntegral.integral_const_mul,
    Real.integral_one_div_add_sq hs0 (Nat.cast_nonneg N)]
  have hN : 0 ≤ (‖s‖ + (N : ℝ))⁻¹ := by positivity
  calc
    (c ^ 2)⁻¹ * (‖s‖⁻¹ - (‖s‖ + (N : ℝ))⁻¹) ≤ (c ^ 2)⁻¹ * ‖s‖⁻¹ := by
      gcongr
      exact sub_le_self _ hN
    _ = 1 / (c ^ 2 * ‖s‖) := by ring

private theorem tendsto_log_add_natCast_sub_log {s : ℂ} (hs : s ∈ slitPlane) :
    Tendsto (fun N : ℕ ↦ Complex.log (s + N) - (Real.log ((N : ℝ) + 2) : ℂ))
      atTop (𝓝 0) := by
  have hiR : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hi : Tendsto (fun N : ℕ ↦ ((N : ℂ) + 2)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_inv, ofReal_add, ofReal_natCast, ofReal_ofNat,
      ofReal_zero] using continuous_ofReal.continuousAt.tendsto.comp hiR
  let z : ℕ → ℂ := fun N ↦ 1 + (s - 2) * ((N : ℂ) + 2)⁻¹
  have hz : Tendsto z atTop (𝓝 (1 : ℂ)) := by
    simpa only [z, mul_zero, add_zero] using (hi.const_mul (s - 2)).const_add 1
  have hl := (Complex.hasDerivAt_log
    (by simp [mem_slitPlane_iff] : (1 : ℂ) ∈ slitPlane)).continuousAt.tendsto.comp hz
  have heq (N : ℕ) : s + N = z N * (((N : ℝ) + 2 : ℝ) : ℂ) := by
    dsimp [z]
    push_cast
    have hn : (N : ℂ) + 2 ≠ 0 := by
      intro hn
      have h := congrArg Complex.re hn
      norm_num at h
      linarith [Nat.cast_nonneg (α := ℝ) N]
    field_simp
    ring
  have hnz (N : ℕ) : z N ≠ 0 := by
    intro h
    exact add_natCast_ne_zero hs N ((heq N).trans (by rw [h, zero_mul]))
  convert hl using 1
  · ext N
    rw [heq N, Complex.log_mul_ofReal ((N : ℝ) + 2) (by positivity) (z N) (hnz N)]
    dsimp only [Function.comp_apply]
    ring
  · simp

private theorem tendsto_sum_Icc_gaussSeries {s : ℂ} (hs : s ∈ slitPlane) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 0 N, (1 / ((n : ℂ) + 1) - 1 / (s + n)))
      atTop (𝓝 (digamma s + Real.eulerMascheroniConstant)) := by
  have hreg := nonpole_of_mem_slitPlane hs
  have hsum : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (s + n)) =
      digamma s + Real.eulerMascheroniConstant := by
    linear_combination -(Complex.digamma_eq_gaussSeries hreg)
  have ht := (Complex.summable_gaussSeries s).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  rw [hsum] at ht
  simpa only [Function.comp_def, Nat.range_succ_eq_Icc_zero] using ht

private theorem tendsto_digamma_natCast_add_two_sub_log :
    Tendsto (fun N : ℕ ↦ digamma ((N : ℝ) + 2) - (Real.log ((N : ℝ) + 2) : ℂ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have h := (isBigO_digamma_ofReal_sub_log.trans_tendsto tendsto_inv_atTop_zero).comp hN
  convert h using 1
  ext N
  dsimp only [Function.comp_apply]
  rw [← ofReal_log (by positivity : 0 ≤ (N : ℝ) + 2)]
  push_cast
  rfl

/-- The finite Gauss sum telescopes against the digamma recurrence from `1` to `N + 2`. -/
private theorem sum_Icc_gaussSeries_eq (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 0 N, (1 / ((n : ℂ) + 1) - 1 / (s + n)) =
      digamma ((N : ℝ) + 2) + Real.eulerMascheroniConstant -
        ∑ k ∈ Finset.Icc 0 N, (s + k)⁻¹ := by
  have h := digamma_apply_add_nat (nonpole_of_mem_slitPlane one_mem_slitPlane) (N + 1)
  simp only [digamma_one, Nat.cast_add, Nat.cast_one] at h
  rw [show (1 : ℂ) + (N + 1) = (N : ℂ) + 2 by ring] at h
  simp only [Finset.sum_sub_distrib, ← Nat.range_succ_eq_Icc_zero, one_div]
  push_cast
  simp_rw [add_comm (1 : ℂ)] at h
  linear_combination -h

/-- `log (s + N) - ∑_{k ≤ N} (s + k)⁻¹ → ψ(s)`. By the telescoped Gauss sum, this sequence is
`G_N + (log (s + N) - log (N + 2)) - (ψ(N + 2) - log (N + 2)) - γ`, where the finite Gauss sum
`G_N` tends to `ψ(s) + γ` and the two logarithmic differences tend to `0`. -/
private theorem tendsto_log_add_sub_sum_inv_add {s : ℂ} (hs : s ∈ slitPlane) :
    Tendsto (fun N : ℕ ↦ Complex.log (s + N) - ∑ k ∈ Finset.Icc 0 N, (s + k)⁻¹)
      atTop (𝓝 (digamma s)) := by
  have h := ((((tendsto_sum_Icc_gaussSeries hs).add (tendsto_log_add_natCast_sub_log hs)).sub
    tendsto_digamma_natCast_add_two_sub_log).sub_const (Real.eulerMascheroniConstant : ℂ))
  convert h using 1
  · ext N
    rw [sum_Icc_gaussSeries_eq s N]
    ring
  · simp

private theorem norm_digamma_sub_log_le_of_mul_norm_add_le {s : ℂ} (hs : s ∈ slitPlane) {c : ℝ}
    (hc : 0 < c) (hden : ∀ t : ℝ, 0 ≤ t → c * (‖s‖ + t) ≤ ‖s + t‖) :
    ‖digamma s - Complex.log s‖ ≤ (1 + (c ^ 2)⁻¹) / ‖s‖ := by
  apply le_of_tendsto ((tendsto_log_add_sub_sum_inv_add hs).sub_const (Complex.log s)).norm
  apply Eventually.of_forall
  intro N
  rw [sum_inv_add_eq_log_sub_integral_fract hs N]
  have heq : Complex.log (s + N) -
      (Complex.log (s + N) - Complex.log s + s⁻¹ -
        ∫ t : ℝ in 0..(N : ℝ), ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2) - Complex.log s =
      (∫ t : ℝ in 0..(N : ℝ), ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2) - s⁻¹ := by ring
  rw [heq]
  calc
    _ ≤ ‖∫ t : ℝ in 0..(N : ℝ), ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2‖ + ‖s⁻¹‖ :=
      norm_sub_le _ _
    _ ≤ 1 / (c ^ 2 * ‖s‖) + ‖s⁻¹‖ := by
      exact _root_.add_le_add (norm_integral_fract_div_add_sq_le hs hc hden N) (le_refl ‖s⁻¹‖)
    _ = (1 + (c ^ 2)⁻¹) / ‖s‖ := by rw [norm_inv]; ring

/-- An explicit uniform digamma error on every closed sector avoiding the negative real axis. -/
theorem norm_digamma_sub_log_le_of_abs_arg_le {s : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi) (hs : |s.arg| ≤ Real.pi - δ) :
    ‖digamma s - Complex.log s‖ ≤ (1 + 4 / (1 - Real.cos δ) ^ 2) / ‖s‖ := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp [digamma_def, logDeriv_apply]
  have hslit : s ∈ slitPlane := mem_slitPlane_iff_arg.mpr ⟨by
    intro heq
    rw [heq, abs_of_pos Real.pi_pos] at hs
    linarith, hs0⟩
  have hcos : Real.cos δ < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hδπ.le hδ
    simpa using h
  have hc : 0 < (1 - Real.cos δ) / 2 := by linarith
  have h := norm_digamma_sub_log_le_of_mul_norm_add_le hslit hc
    (fun t ht ↦ mul_norm_add_le_norm_add_ofReal_of_abs_arg_le hδ hs ht)
  convert h using 1
  have heq : (((1 - Real.cos δ) / 2) ^ 2)⁻¹ = 4 / (1 - Real.cos δ) ^ 2 := by
    field_simp
    norm_num
  rw [heq]

/-- Digamma differs from the principal logarithm by `O(1 / ‖s‖)` uniformly on a closed sector
separated from the negative real axis. -/
theorem isBigO_digamma_sub_log_sector {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    (fun s : ℂ ↦ digamma s - Complex.log s)
      =O[cocompact ℂ ⊓ 𝓟 {s : ℂ | |s.arg| ≤ Real.pi - δ}] (fun s : ℂ ↦ ‖s‖⁻¹) := by
  apply IsBigO.of_bound (1 + 4 / (1 - Real.cos δ) ^ 2)
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro s hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg s)),
    div_eq_mul_inv] using norm_digamma_sub_log_le_of_abs_arg_le hδ hδπ hs

end Complex
