/-
Copyright (c) 2026 The Tau Ceti contributors and Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, Robby Sneiderman
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.GaussSeries
public import TauCeti.Analysis.SpecialFunctions.Complex.Log.Bounds
public import Mathlib.NumberTheory.AbelSummation
public import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
public import TauCeti.Analysis.Complex.SectorBounds
public import TauCeti.Analysis.Complex.SlitPlane
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Analysis.Calculus.Deriv.Fract
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.HalfAngle
public import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.SpecialFunctions.Integrals.PeriodicStieltjes

/-!
# Uniform sectorial digamma asymptotics

For `0 < δ < π`, uniformly on `|arg s| ≤ π - δ`,
`‖digamma s - log s‖ ≤ (1 + 4 / (1 - cos δ) ^ 2) / ‖s‖`.
In particular, the difference is `O(1 / ‖s‖)` along the cocompact filter on that sector.

The proof starts from Abel's finite summation formula for `(s + n)⁻¹`. Its remainder is an
integral of `fract t / (s + t)^2`. A sectorial denominator bound controls the integral uniformly
in the cutoff; Gauss' series identifies the limit (`Complex.tendsto_log_add_sub_sum_inv_add`). This
gives the leading-order consequence of [DLMF 5.11.2](https://dlmf.nist.gov/5.11.E2), with the
explicit error bound above.

Integrating the sawtooth `fract t - 1/2` in that remainder by parts against the periodic kernel
`P₂(t) = (fract t ^ 2 - fract t) / 2`, which vanishes at the integers and has `|P₂| ≤ 1/8`, gives
the exact improper-integral representation
`digamma s - log s + 1 / (2s) = -2 ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (s + t) ^ 3 dt`
(`Complex.digamma_sub_log_add_inv_two_mul_eq_integral`), Nemes's explicit slit-plane bound
`‖digamma z - log z + 1 / (2z)‖ ≤ 1 / (8 * cos (arg z / 2) ^ 3 * ‖z‖ ^ 2)`
(`Complex.norm_digamma_sub_log_add_inv_two_mul_le`), and the second-order sector bound
`‖digamma s - log s + 1 / (2s)‖ ≤ 1 / (8 * sin (δ / 2) ^ 3 * ‖s‖ ^ 2)` for `0 < δ`
(`Complex.norm_digamma_sub_log_add_inv_two_mul_le_of_abs_arg_le`). This is the input to Stirling's
formula on sectors and to the Stieltjes representation of the Stirling remainder, corresponding to
[DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1) and [DLMF 5.11.2](https://dlmf.nist.gov/5.11.E2).

The positive-strip estimate `Complex.exists_norm_digamma_le_log` supplies the logarithmic
growth needed in the archimedean term of explicit formulas. Its proof adapts Robby
Sneiderman’s strip argument from
[PrimeNumberTheoremAnd](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/83f85e91fccdeecc8248fe6d51c30edfb3a07d15/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/DigammaBounds.lean).

The finite summation identity is exposed separately for subsequent integral representations
and gamma asymptotics. All integral endpoints use Mathlib's oriented interval integral.
-/

public section

open Complex Real Filter Set Topology MeasureTheory intervalIntegral Asymptotics

namespace Complex

private theorem add_natCast_ne_zero {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) : s + N ≠ 0 := by
  simpa only [ofReal_natCast] using mem_slitPlane_iff_add_ofReal_ne_zero.mp hs _ (Nat.cast_nonneg N)

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
    fun _ ht ↦ pow_ne_zero _ (mem_slitPlane_iff_add_ofReal_ne_zero.mp hs _ ht.1)

private theorem continuousOn_add_one_div_add_sq {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ContinuousOn (fun t : ℝ ↦ ((t : ℂ) + 1) / (s + t) ^ 2) (Icc 0 (N : ℝ)) :=
  (continuous_ofReal.continuousOn.add continuousOn_const).div
    ((continuousOn_const.add continuous_ofReal.continuousOn).pow 2)
    fun _ ht ↦ pow_ne_zero _ (mem_slitPlane_iff_add_ofReal_ne_zero.mp hs _ ht.1)

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
    have h := (hasDerivAt_log_add_ofReal (TauCeti.add_ofReal_mem_slitPlane hs ht.1)).add
      ((hasDerivAt_inv_add_ofReal (mem_slitPlane_iff_add_ofReal_ne_zero.mp hs _ ht.1)).const_mul
        (s - 1))
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
    hasDerivAt_inv_add_ofReal (mem_slitPlane_iff_add_ofReal_ne_zero.mp hs _ ht.1)
  have hc : ContinuousOn (fun t : ℝ ↦ -1 / (s + t) ^ 2) (Icc 0 (N : ℝ)) := by
    simpa only [div_eq_mul_inv] using (continuousOn_inv_add_ofReal_sq hs N).const_mul (-1)
  have hA := sum_mul_eq_sub_integral_mul' (fun _ : ℕ ↦ (1 : ℂ)) N
    (fun t ht ↦ (hd t ht).differentiableAt)
    (hc.integrableOn_Icc.congr_fun (fun t ht ↦ (hd t ht).deriv.symm) measurableSet_Icc)
  have hsum (m : ℕ) : ∑ _ ∈ Finset.Icc 0 m, (1 : ℂ) = (m : ℂ) + 1 := by simp
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

private theorem norm_digamma_sub_log_le_of_mul_norm_add_le {s : ℂ} (hs : s ∈ slitPlane) {c : ℝ}
    (hc : 0 < c) (hden : ∀ t : ℝ, 0 ≤ t → c * (‖s‖ + t) ≤ ‖s + t‖) :
    ‖digamma s - Complex.log s‖ ≤ (1 + (c ^ 2)⁻¹) / ‖s‖ := by
  apply le_of_tendsto
    ((tendsto_log_add_sub_sum_inv_add (nonpole_of_mem_slitPlane hs)).sub_const (Complex.log s)).norm
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
  have hslit := mem_slitPlane_of_abs_arg_le hδ hs hs0
  have hc : 0 < (1 - Real.cos δ) / 2 :=
    half_pos (TauCeti.one_sub_cos_pos hδ (by linarith [Real.pi_pos]))
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

/-! ### The second-order sectorial digamma bound -/

private theorem integral_inv_add_sq {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ∫ t : ℝ in 0..(N : ℝ), ((s + (t : ℂ)) ^ 2)⁻¹ = s⁻¹ - (s + N)⁻¹ := by
  have hd (t : ℝ) (ht : t ∈ uIcc 0 (N : ℝ)) :
      HasDerivAt (fun u : ℝ ↦ -(s + (u : ℂ))⁻¹) (((s + (t : ℂ)) ^ 2)⁻¹) t := by
    rw [uIcc_of_le (Nat.cast_nonneg N)] at ht
    convert (hasDerivAt_inv_add_ofReal (mem_slitPlane_iff_add_ofReal_ne_zero.mp hs _ ht.1)).neg
      using 1
    ring
  rw [integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_inv_add_ofReal_sq hs N).intervalIntegrable_of_Icc (Nat.cast_nonneg N))]
  simp only [ofReal_natCast, ofReal_zero, add_zero]
  ring

/-- Integration by parts against `P₂`: the boundary terms vanish at the integers `0` and `N`. -/
private theorem integral_fract_sub_half_div_add_sq {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    ∫ t : ℝ in 0..(N : ℝ), ((Int.fract t - 1 / 2 : ℝ) : ℂ) / (s + t) ^ 2 =
      2 * ∫ t : ℝ in 0..(N : ℝ),
        (((Int.fract t ^ 2 - Int.fract t) / 2 : ℝ) : ℂ) / (s + t) ^ 3 := by
  let u : ℝ → ℂ := fun t ↦ (((Int.fract t ^ 2 - Int.fract t) / 2 : ℝ) : ℂ)
  let v : ℝ → ℂ := fun t ↦ ((s + (t : ℂ)) ^ 2)⁻¹
  have hN := Nat.cast_nonneg (α := ℝ) N
  have hvd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt v (-2 / (s + t) ^ 3) t := by
    have hne := mem_slitPlane_iff_add_ofReal_ne_zero.mp hs _ ht
    have h := (((hasDerivAt_id (t : ℂ)).const_add s).pow 2).inv (pow_ne_zero 2 hne)
    refine HasDerivAt.congr_deriv (f := v) h.comp_ofReal ?_
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  have hcont3 : ContinuousOn (fun t : ℝ ↦ -2 / (s + (t : ℂ)) ^ 3) (Icc 0 (N : ℝ)) :=
    continuousOn_const.div ((continuousOn_const.add continuous_ofReal.continuousOn).pow 3)
      fun _ ht ↦ pow_ne_zero _ (mem_slitPlane_iff_add_ofReal_ne_zero.mp hs _ ht.1)
  have hu'int : IntervalIntegrable (fun t : ℝ ↦ ((Int.fract t - 1 / 2 : ℝ) : ℂ)) volume 0 N := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hN).2 ?_
    refine Measure.integrableOn_of_bounded (μ := volume) (M := 1) measure_Icc_lt_top.ne
      ((continuous_ofReal.measurable.comp
        (measurable_fract.sub measurable_const)).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun t ↦ ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]
  have hibp := integral_deriv_mul_eq_sub_of_hasDeriv_right (u := u) (v := v)
    (u' := fun t ↦ ((Int.fract t - 1 / 2 : ℝ) : ℂ)) (v' := fun t ↦ -2 / (s + t) ^ 3)
    (continuous_ofReal.comp (Int.continuous_fract_sq_sub_fract.div_const 2)).continuousOn
    (fun t ht ↦ by
      rw [uIcc_of_le hN] at ht
      exact (hvd t ht.1).continuousAt.continuousWithinAt)
    (fun t _ ↦ ((Int.hasDerivWithinAt_fract_sq_sub_fract t).div_const 2).ofReal_comp.congr_deriv
      (by push_cast; ring))
    (fun t ht ↦ by
      rw [min_eq_left hN] at ht
      exact (hvd t ht.1.le).hasDerivWithinAt)
    hu'int (hcont3.intervalIntegrable_of_Icc hN)
  have hu0 : u 0 = 0 := by simp [u]
  have huN : u N = 0 := by simp [u]
  rw [hu0, huN, zero_mul, zero_mul, sub_zero, intervalIntegral.integral_add] at hibp
  · have hrw : ∫ t : ℝ in 0..(N : ℝ), u t * (-2 / (s + t) ^ 3) =
        -2 * ∫ t : ℝ in 0..(N : ℝ), u t / (s + t) ^ 3 := by
      rw [← intervalIntegral.integral_const_mul]
      refine integral_congr fun t _ ↦ ?_
      ring
    rw [hrw] at hibp
    have hl : ∫ t : ℝ in 0..(N : ℝ), ((Int.fract t - 1 / 2 : ℝ) : ℂ) / (s + t) ^ 2 =
        ∫ t : ℝ in 0..(N : ℝ), ((Int.fract t - 1 / 2 : ℝ) : ℂ) * v t := by
      refine integral_congr fun t _ ↦ ?_
      simp only [v, div_eq_mul_inv]
    rw [hl]
    linear_combination hibp
  · exact hu'int.mul_continuousOn (fun t ht ↦ by
      rw [uIcc_of_le hN] at ht
      exact (hvd t ht.1).continuousAt.continuousWithinAt)
  · exact (hcont3.intervalIntegrable_of_Icc hN).continuousOn_mul
      (continuous_ofReal.comp (Int.continuous_fract_sq_sub_fract.div_const 2)).continuousOn

/-- The fractional-part remainder minus its mean `1 / (2s)` is the `P₂` remainder up to the
boundary term `-1 / (2 (s + N))`. -/
private theorem integral_fract_div_add_sq_sub_inv_two_mul {s : ℂ} (hs : s ∈ slitPlane) (N : ℕ) :
    (∫ t : ℝ in 0..(N : ℝ), ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2) - (2 * s)⁻¹ =
      -(2 * (s + N))⁻¹ + 2 * ∫ t : ℝ in 0..(N : ℝ),
        (((Int.fract t ^ 2 - Int.fract t) / 2 : ℝ) : ℂ) / (s + t) ^ 3 := by
  have hN := Nat.cast_nonneg (α := ℝ) N
  have hsplit : ∫ t : ℝ in 0..(N : ℝ), ((Int.fract t : ℝ) : ℂ) / (s + t) ^ 2 =
      (∫ t : ℝ in 0..(N : ℝ), ((Int.fract t - 1 / 2 : ℝ) : ℂ) / (s + t) ^ 2) +
        (1 / 2 : ℂ) * ∫ t : ℝ in 0..(N : ℝ), ((s + (t : ℂ)) ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · refine integral_congr fun t _ ↦ ?_
      push_cast
      ring
    · have h := intervalIntegrable_fract_div_add_sq hs N
      have h2 := ((continuousOn_inv_add_ofReal_sq hs N).intervalIntegrable_of_Icc (μ := volume)
        hN).const_mul (1 / 2 : ℂ)
      refine (h.sub h2).congr fun t _ ↦ ?_
      push_cast
      ring
    · exact ((continuousOn_inv_add_ofReal_sq hs N).intervalIntegrable_of_Icc (μ := volume)
        hN).const_mul _
  rw [hsplit, integral_fract_sub_half_div_add_sq hs N, integral_inv_add_sq hs N]
  field_simp [slitPlane_ne_zero hs, add_natCast_ne_zero hs N]
  ring

/-- Exact `P₂` Stieltjes integral representation of `ψ(s) - log s + 1 / (2s)` for
`s ∈ slitPlane ∪ {0}`:
`digamma s - log s + (2 * s)⁻¹ = -2 * ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (s + t) ^ 3 dt`
(at `s = 0` the integrand is not integrable and both sides vanish). -/
theorem digamma_sub_log_add_inv_two_mul_eq_integral {s : ℂ} (hs : s ∈ slitPlane ∪ {0}) :
    digamma s - Complex.log s + (2 * s)⁻¹ =
      -2 * ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (s + t) ^ 3 := by
  rcases hs with hs | rfl
  · obtain ⟨c, hc, hden⟩ := TauCeti.exists_pos_mul_one_add_le_norm_ofReal_add hs
    have hlim1 := (((tendsto_log_add_sub_sum_inv_add (nonpole_of_mem_slitPlane hs)).sub_const
      (Complex.log s)).add_const (2 * s)⁻¹)
    have hinv : Tendsto (fun N : ℕ ↦ -(2 * (s + (N : ℂ)))⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (g := fun N : ℕ ↦ (2 * (c * (1 + (N : ℝ))))⁻¹)
        (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) ?_
      · have hN := hden N (Nat.cast_nonneg N)
        rw [ofReal_natCast, add_comm (N : ℂ) s] at hN
        rw [norm_neg, norm_inv, norm_mul, Complex.norm_two]
        exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hN zero_le_two)
      · refine tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop zero_lt_two ?_)
        exact Tendsto.const_mul_atTop hc
          (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
    have hlim2 : Tendsto (fun N : ℕ ↦ -(2 * (s + (N : ℂ)))⁻¹ + (-2) *
        ∫ t : ℝ in 0..(N : ℝ), (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (s + t) ^ 3)
        atTop (𝓝 (-2 * ∫ t : ℝ in Ioi 0,
          (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (s + t) ^ 3)) := by
      simpa using hinv.add ((intervalIntegral_tendsto_integral_Ioi 0
        ((TauCeti.integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff (j := 1)).mpr hs)
        tendsto_natCast_atTop_atTop).const_mul (-2))
    refine tendsto_nhds_unique hlim1 (hlim2.congr fun N ↦ ?_)
    rw [sum_inv_add_eq_log_sub_integral_fract hs N]
    have hker := integral_fract_div_add_sq_sub_inv_two_mul hs N
    have hneg : ∫ t : ℝ in 0..(N : ℝ),
        (((Int.fract t ^ 2 - Int.fract t) / 2 : ℝ) : ℂ) / (s + t) ^ 3 =
        -(∫ t : ℝ in 0..(N : ℝ),
          (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (s + t) ^ 3) := by
      rw [← intervalIntegral.integral_neg]
      refine integral_congr fun t _ ↦ ?_
      push_cast
      ring
    rw [hneg] at hker
    linear_combination -hker
  · have hlhs : digamma 0 - Complex.log 0 + (2 * (0 : ℂ))⁻¹ = 0 := by
      simp [digamma_def, logDeriv_apply]
    rw [hlhs, integral_undef
      (mt (TauCeti.integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff (z := 0) (j := 1)).mp
        (by simp)), mul_zero]

/-- Nemes's explicit bound for `ψ(z) - log z + 1 / (2z)` on `slitPlane ∪ {0}` (`j = 1` of the
periodic-quadratic Stieltjes bound; at `z = 0` both sides vanish):
`‖digamma z - log z + 1 / (2z)‖ ≤ 1 / (8 * cos (arg z / 2) ^ 3 * ‖z‖ ^ 2)`. -/
theorem norm_digamma_sub_log_add_inv_two_mul_le {z : ℂ} (hz : z ∈ slitPlane ∪ {0}) :
    ‖digamma z - Complex.log z + (2 * z)⁻¹‖ ≤
      1 / (8 * Real.cos (z.arg / 2) ^ 3 * ‖z‖ ^ 2) := by
  rw [digamma_sub_log_add_inv_two_mul_eq_integral hz, norm_mul, norm_neg, Complex.norm_two]
  refine (mul_le_mul_of_nonneg_left
    (TauCeti.norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le 1 z) zero_le_two).trans_eq ?_
  norm_num [one_div, mul_inv]
  ring

/-- The second-order sectorial digamma bound: for `0 < δ` and `|arg s| ≤ π - δ`,
`‖ψ(s) - log s + 1 / (2s)‖ ≤ 1 / (8 * sin (δ / 2) ^ 3 * ‖s‖ ^ 2)`. -/
theorem norm_digamma_sub_log_add_inv_two_mul_le_of_abs_arg_le {s : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hs : |s.arg| ≤ Real.pi - δ) :
    ‖digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ 1 / (8 * Real.sin (δ / 2) ^ 3 * ‖s‖ ^ 2) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp [digamma_def, logDeriv_apply]
  have hδπ : δ ≤ Real.pi := by linarith [abs_nonneg s.arg]
  have : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (half_pos hδ) (by linarith [Real.pi_pos])
  have : Real.sin (δ / 2) ≤ Real.cos (s.arg / 2) :=
    sin_half_le_cos_half_arg_of_abs_arg_le hδ.le hs
  have : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  exact (norm_digamma_sub_log_add_inv_two_mul_le
    (Or.inl (mem_slitPlane_of_abs_arg_le hδ hs hs0))).trans (by gcongr)

/-! ### Logarithmic growth on positive vertical strips -/

/-- Digamma has logarithmic norm growth at every height on each positive vertical strip.

The constant is uniform in the real part, and strips with `b < a` are allowed. This estimate
controls the gamma logarithmic derivative in archimedean explicit-formula integrals. -/
theorem exists_norm_digamma_le_log {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc a b →
      ‖digamma s‖ ≤ C * Real.log (|s.im| + 2) := by
  let D := 5 / a + |Real.log a| + Real.log (|b| + 1) + Real.pi / 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 ≤ D := by
    have hb := Real.log_nonneg (by linarith [abs_nonneg b] : 1 ≤ |b| + 1)
    dsimp [D]
    positivity
  refine ⟨D / Real.log 2 + 1, by positivity, fun s hs ↦ ?_⟩
  have hre : 0 < s.re := ha.trans_le hs.1
  have herr : ‖digamma s - Complex.log s‖ ≤ 5 / a := by
    have h := norm_digamma_sub_log_le_of_abs_arg_le (s := s) (δ := Real.pi / 2)
      (by positivity) (by linarith [Real.pi_pos])
      (by linarith [abs_arg_le_pi_div_two_iff.mpr hre.le])
    simp only [Real.cos_pi_div_two] at h
    norm_num at h
    exact h.trans (div_le_div_of_nonneg_left (by norm_num) ha (hs.1.trans (re_le_norm s)))
  have hbound : ‖digamma s‖ ≤ D + Real.log (|s.im| + 2) := by
    have h := norm_add_le (digamma s - Complex.log s) (Complex.log s)
    rw [sub_add_cancel] at h
    have hlog := norm_log_le_of_re_mem_Icc ha hs
    dsimp [D]
    linarith
  have hL : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have h := mul_le_mul_of_nonneg_left hL (div_nonneg hD hlog2.le)
  have hcancel : D / Real.log 2 * Real.log 2 = D := by field_simp
  rw [hcancel] at h
  nlinarith

end Complex
