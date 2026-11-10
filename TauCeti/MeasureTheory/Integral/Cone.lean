/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Weighted square integrals over cones

Let `Γ` be an open subset of a finite-dimensional real normed space `E` which is closed under
multiplication by positive reals, such as an open cone of frequencies in microlocal analysis.
This file collects the integral estimates over such cones behind Sobolev versions of microlocal
regularity, in which the rapid decay of a function in `Γ` is replaced by the finiteness of the
weighted square integral `∫_Γ ⟨η⟩ ^ (2 s) ‖F η‖ ^ 2`, with `⟨η⟩ = (1 + ‖η‖ ^ 2) ^ (1 / 2)`.

* `TauCeti.lintegral_ofReal_mul_one_add_norm_rpow_neg_sq_lt_top`: functions bounded by
  `C (1 + ‖η‖) ^ (-r)` with `r > dim E` are square integrable.
* `TauCeti.lintegral_tsum_mul_comp_sub_sq_le`: for a measurable `g ≥ 0` and coefficients
  `b i ≥ 0`, the superposition of translates `η ↦ ∑ i, b i g (η - v i)` has square integral at most
  `(∑ i, b i) ^ 2 ∫ g ^ 2`, by the Cauchy–Schwarz inequality and translation invariance.
* `TauCeti.setLIntegral_ofReal_one_add_norm_sq_rpow_mul_norm_sq_lt_top_of_hasSum`: the square
  integral version of `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum`. A superposition
  `∑ i, a i • F (η - v i)` of translates of a function `F` of polynomial growth, with
  coefficients `a i` rapidly decreasing in `‖v i‖`, has finite weighted square integral on every
  set `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)` lie in `Γ`, if `F` has finite weighted
  square integral on `Γ`. The shifts with `‖v i‖ ≤ c ‖η‖` stay in `Γ` and are controlled by Peetre's
  inequality and the first estimate; the remaining shifts are controlled by the polynomial growth
  of `F` and the decay of the coefficients.
* `TauCeti.setLIntegral_ofReal_one_add_norm_sq_rpow_eq_top`: a nonempty open cone `Γ` in
  dimension `n` has `∫_Γ ⟨η⟩ ^ (2 s) = ∞` when `-n ≤ 2 s`. Its intersections with the dyadic
  shells `2 ^ j < ‖η‖ ≤ 2 ^ (j + 1)` are dilates of each other, with measures `2 ^ (j n)` times
  that of the first one. Conversely `∫ ⟨η⟩ ^ (2 s)` is finite on all of `E` when `2 s < -n`
  (`integrable_rpow_neg_one_add_norm_sq`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Lemma 8.1.1, and §8.2.
-/

public section

open Function MeasureTheory Metric Set Module
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- **Square integrals of superpositions of translates.** For a measurable `g ≥ 0` on an additive
group with a right invariant measure, and coefficients `b i ≥ 0`, the superposition
`η ↦ ∑ i, b i g (η - v i)` has square integral at most `(∑ i, b i) ^ 2 ∫ g ^ 2`. -/
theorem lintegral_tsum_mul_comp_sub_sq_le [MeasurableSpace E] [MeasurableAdd E] [MeasurableNeg E]
    {μ : Measure E} [μ.IsAddRightInvariant] {ι : Type*} [Countable ι] {g : E → ℝ≥0∞}
    (hg : Measurable g)
    (b : ι → ℝ≥0∞) (v : ι → E) :
    ∫⁻ η, (∑' i, b i * g (η - v i)) ^ 2 ∂μ ≤ (∑' i, b i) ^ 2 * ∫⁻ η, g η ^ 2 ∂μ := by
  have hgv (i : ι) : Measurable fun η ↦ g (η - v i) := hg.comp (measurable_sub_const _)
  -- Each product of two translates integrates to at most `∫ g ^ 2`.
  have hcs (i j : ι) : ∫⁻ η, g (η - v i) * g (η - v j) ∂μ ≤ ∫⁻ η, g η ^ 2 ∂μ := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      (hgv i).aemeasurable (hgv j).aemeasurable
    have htr (w : E) : ∫⁻ η, g (η - w) ^ (2 : ℝ) ∂μ = ∫⁻ η, g η ^ 2 ∂μ := by
      simp_rw [ENNReal.rpow_two]
      exact lintegral_sub_right_eq_self (fun η ↦ g η ^ 2) w
    simp only [Pi.mul_apply, htr] at h
    refine h.trans_eq ?_
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc ∫⁻ η, (∑' i, b i * g (η - v i)) ^ 2 ∂μ
      = ∫⁻ η, ∑' i, ∑' j, b i * b j * (g (η - v i) * g (η - v j)) ∂μ := by
        refine lintegral_congr fun η ↦ ?_
        rw [sq, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun i ↦ ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun j ↦ by ring
    _ = ∑' i, ∑' j, b i * b j * ∫⁻ η, g (η - v i) * g (η - v j) ∂μ := by
        have hm (i j : ι) : Measurable fun η ↦ b i * b j * (g (η - v i) * g (η - v j)) :=
          measurable_const.mul ((hgv i).mul (hgv j))
        rw [lintegral_tsum fun i ↦ (Measurable.tsum (hm i)).aemeasurable]
        refine tsum_congr fun i ↦ ?_
        rw [lintegral_tsum fun j ↦ (hm i j).aemeasurable]
        exact tsum_congr fun j ↦ lintegral_const_mul _ ((hgv i).mul (hgv j))
    _ ≤ ∑' i, ∑' j, b i * b j * ∫⁻ η, g η ^ 2 ∂μ :=
        tsum_le_tsum fun i ↦ tsum_le_tsum fun j ↦ mul_le_mul_right (hcs i j) _
    _ = (∑' i, b i) ^ 2 * ∫⁻ η, g η ^ 2 ∂μ := by
        rw [sq, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun i ↦ ?_
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]

/-- The weight `⟨η⟩ ^ s` is at most `(1 + ‖η‖) ^ ⌈|s|⌉₊`. -/
private theorem one_add_norm_sq_rpow_le_one_add_norm_pow_ceil (s : ℝ) (η : E) :
    (1 + ‖η‖ ^ 2) ^ (s / 2) ≤ (1 + ‖η‖) ^ ⌈|s|⌉₊ :=
  calc (1 + ‖η‖ ^ 2) ^ (s / 2) ≤ (1 + ‖η‖ ^ 2) ^ ((⌈|s|⌉₊ : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [norm_nonneg η])
          (by linarith [le_abs_self s, Nat.le_ceil |s|])
    _ ≤ (1 + ‖η‖) ^ ⌈|s|⌉₊ := one_add_norm_sq_rpow_le_one_add_norm_pow η _

/-- The pointwise estimate behind the square integral localization: a translate
`a • F (η - v)` with `η ∈ Γ'` is controlled near `η` by `F` on `Γ` (Peetre's inequality), and far
from `η` by the polynomial growth of `F`, with an integrable weight in `η`. -/
private theorem norm_smul_comp_sub_le {𝕜 G : Type*} [NormedField 𝕜] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {F : E → G} {C₀ : ℝ} {k : ℕ} (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k)
    {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) (s r : ℝ)
    (hr : 0 ≤ r) {η : E} (hη : η ∈ Γ') (a : 𝕜) (v : E) :
    (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖a • F (η - v)‖ ≤
      2 ^ (|s| / 2) * (1 + ‖v‖ ^ 2) ^ (|s| / 2) * ‖a‖ *
          Γ.indicator (fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖F ζ‖) (η - v) +
        (1 + ‖v‖) ^ (((⌈|s|⌉₊ + 2 * k : ℕ) : ℝ) + r) * ‖a‖ *
          (C₀ * (1 + c⁻¹) ^ (((⌈|s|⌉₊ + k : ℕ) : ℝ) + r) * (1 + ‖η‖) ^ (-r)) := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  have hc' : 0 ≤ 1 + c⁻¹ := by linarith [inv_pos.2 hc]
  set N := ⌈|s|⌉₊
  set t := 1 + ‖η‖
  have ht : 1 ≤ t := le_add_of_nonneg_right (norm_nonneg η)
  have hv1 : 1 ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
  rw [norm_smul]
  by_cases hv : ‖v‖ ≤ c * ‖η‖
  · -- Near shifts stay in `Γ`; use Peetre's inequality
    -- `⟨η⟩ ^ s ≤ 2 ^ (|s| / 2) ⟨v⟩ ^ |s| ⟨η - v⟩ ^ s`.
    have hmem : η - v ∈ Γ := hΓ' η hη (by simpa [dist_eq_norm] using hv)
    have hP := one_add_norm_sq_rpow_le_mul_sub s η (η - v)
    rw [sub_sub_cancel] at hP
    refine le_add_of_le_of_nonneg ?_ (mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg hc' _)) (by positivity)))
    rw [indicator_of_mem hmem]
    calc (1 + ‖η‖ ^ 2) ^ (s / 2) * (‖a‖ * ‖F (η - v)‖)
        ≤ 2 ^ (|s| / 2) * (1 + ‖v‖ ^ 2) ^ (|s| / 2) * (1 + ‖η - v‖ ^ 2) ^ (s / 2) *
            (‖a‖ * ‖F (η - v)‖) := by gcongr
      _ = _ := by ring
  · -- Far shifts have `1 + ‖η‖ ≤ (1 + c⁻¹) (1 + ‖v‖)`: use the polynomial growth of `F`.
    push Not at hv
    refine le_add_of_nonneg_of_le
      (mul_nonneg (by positivity) (indicator_nonneg (fun _ _ ↦ by positivity) _)) ?_
    have htv : t ≤ (1 + c⁻¹) * (1 + ‖v‖) := by
      have : ‖η‖ ≤ c⁻¹ * ‖v‖ := by rw [le_inv_mul_iff₀ hc]; exact hv.le
      nlinarith [norm_nonneg v, inv_pos.2 hc]
    have hFle : ‖F (η - v)‖ ≤ C₀ * (t ^ k * (1 + ‖v‖) ^ k) := by
      refine (hF _).trans ?_
      rw [← mul_pow]
      gcongr
      nlinarith [norm_sub_le η v, norm_nonneg η, norm_nonneg v]
    have hw : (1 + ‖η‖ ^ 2) ^ (s / 2) ≤ t ^ N := one_add_norm_sq_rpow_le_one_add_norm_pow_ceil s η
    have hsplit : t ^ (N + k) = t ^ ((N + k : ℕ) + r) * t ^ (-r) := by
      rw [← Real.rpow_add (by positivity), add_neg_cancel_right, Real.rpow_natCast]
    have hrpow : t ^ ((N + k : ℕ) + r) ≤
        (1 + c⁻¹) ^ ((N + k : ℕ) + r) * (1 + ‖v‖) ^ ((N + k : ℕ) + r) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) htv (by positivity)
    have hvv : (1 + ‖v‖) ^ ((N + k : ℕ) + r) * (1 + ‖v‖) ^ k =
        (1 + ‖v‖) ^ ((N + 2 * k : ℕ) + r) := by
      rw [← Real.rpow_natCast (1 + ‖v‖) k, ← Real.rpow_add (by positivity)]
      congr 1
      push_cast
      ring
    calc (1 + ‖η‖ ^ 2) ^ (s / 2) * (‖a‖ * ‖F (η - v)‖)
        ≤ t ^ N * (‖a‖ * (C₀ * (t ^ k * (1 + ‖v‖) ^ k))) := by gcongr
      _ = ‖a‖ * C₀ * (t ^ (N + k) * (1 + ‖v‖) ^ k) := by ring
      _ = ‖a‖ * C₀ * (t ^ ((N + k : ℕ) + r) * (1 + ‖v‖) ^ k * t ^ (-r)) := by
        rw [hsplit]; ring
      _ ≤ ‖a‖ * C₀ * ((1 + c⁻¹) ^ ((N + k : ℕ) + r) * (1 + ‖v‖) ^ ((N + k : ℕ) + r) *
            (1 + ‖v‖) ^ k * t ^ (-r)) := by gcongr
      _ = (1 + ‖v‖) ^ ((N + 2 * k : ℕ) + r) * ‖a‖ *
            (C₀ * (1 + c⁻¹) ^ ((N + k : ℕ) + r) * t ^ (-r)) := by
        rw [mul_assoc ((1 + c⁻¹) ^ _), hvv]; ring

/-- The pointwise bound behind the square integral localization: summing the estimates of
`norm_smul_comp_sub_le` over the translates. -/
private theorem ofReal_mul_norm_le_of_hasSum {ι 𝕜 G : Type*} [NormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {v : ι → E} {a : ι → 𝕜} {F : E → G} {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) (s r : ℝ) (hr : 0 ≤ r) {η : E} (hη : η ∈ Γ')
    {H : G} (hH : HasSum (fun i ↦ a i • F (η - v i)) H) :
    ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖H‖) ≤
      ∑' i, ENNReal.ofReal (2 ^ (|s| / 2) * (1 + ‖v i‖ ^ 2) ^ (|s| / 2) * ‖a i‖) *
          ENNReal.ofReal (Γ.indicator (fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖F ζ‖) (η - v i)) +
        (∑' i, ENNReal.ofReal ((1 + ‖v i‖) ^ (((⌈|s|⌉₊ + 2 * k : ℕ) : ℝ) + r) * ‖a i‖)) *
          ENNReal.ofReal (C₀ * (1 + c⁻¹) ^ (((⌈|s|⌉₊ + k : ℕ) : ℝ) + r) * (1 + ‖η‖) ^ (-r)) := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  have hc' : 0 ≤ 1 + c⁻¹ := by linarith [inv_pos.2 hc]
  rw [← hH.tsum_eq, ← ENNReal.tsum_mul_right, ← tsum_add]
  calc ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖∑' i, a i • F (η - v i)‖)
      = ‖((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ)‖ₑ * ‖∑' i, a i • F (η - v i)‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
          Real.norm_of_nonneg (by positivity)]
    _ ≤ ‖((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ)‖ₑ * ∑' i, ‖a i • F (η - v i)‖ₑ := by
        gcongr
        exact enorm_tsum_le_tsum_enorm
    _ = ∑' i, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖a i • F (η - v i)‖) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun i ↦ ?_
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
          Real.norm_of_nonneg (by positivity)]
    _ ≤ _ := by
        refine tsum_le_tsum fun i ↦ ?_
        refine (ENNReal.ofReal_le_ofReal (norm_smul_comp_sub_le hF hc hΓ' s r hr hη (a i)
          (v i))).trans ?_
        have hb0 : 0 ≤ 2 ^ (|s| / 2) * (1 + ‖v i‖ ^ 2) ^ (|s| / 2) * ‖a i‖ := by positivity
        have he0 : 0 ≤ (1 + ‖v i‖) ^ (((⌈|s|⌉₊ + 2 * k : ℕ) : ℝ) + r) * ‖a i‖ := by positivity
        rw [ENNReal.ofReal_add (mul_nonneg hb0 (indicator_nonneg (fun _ _ ↦ by positivity) _))
          (mul_nonneg he0 (mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg hc' _)) (by positivity)))]
        exact add_le_add (ENNReal.ofReal_mul hb0).le (ENNReal.ofReal_mul he0).le

/-- The summability of the coefficient sums in the square integral localization. -/
private theorem tsum_ofReal_ne_top {ι : Type*} {f : ι → ℝ} (hf : Summable f)
    (hf0 : ∀ i, 0 ≤ f i) : ∑' i, ENNReal.ofReal (f i) ≠ ∞ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hf]
  exact ENNReal.ofReal_ne_top

variable [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A square integrable majorant: `η ↦ (C (1 + ‖η‖) ^ (-r)) ^ 2` has finite integral for
`r > dim E` and `C ≥ 0`. -/
theorem lintegral_ofReal_mul_one_add_norm_rpow_neg_sq_lt_top {C : ℝ} (hC : 0 ≤ C) {r : ℝ}
    (hr : (finrank ℝ E : ℝ) < r) :
    ∫⁻ η, ENNReal.ofReal (C * (1 + ‖η‖) ^ (-r)) ^ 2 ∂μ < ∞ := by
  have hr0 : 0 < r := lt_of_le_of_lt (Nat.cast_nonneg _) hr
  refine lt_of_le_of_lt (lintegral_mono fun η ↦ ?_)
    (Integrable.lintegral_lt_top ((integrable_one_add_norm (μ := μ) hr).const_mul (C ^ 2)))
  have h1 : (1 + ‖η‖) ^ (-r) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg η]) (by linarith)
  have h0 : 0 ≤ (1 + ‖η‖) ^ (-r) := by positivity
  rw [← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [sq_nonneg C, mul_le_mul_of_nonneg_left h1 h0]

/-- The square integral localization for a countable index type. -/
private theorem setLIntegral_ofReal_one_add_norm_sq_rpow_mul_norm_sq_lt_top_of_hasSum_of_countable
    {ι 𝕜 G : Type*} [Countable ι] [NormedField 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {v : ι → E} {a : ι → 𝕜} (ha : ∀ j : ℕ, Summable fun i ↦ (1 + ‖v i‖) ^ j * ‖a i‖) {F : E → G}
    (hFm : Measurable fun ζ ↦ ‖F ζ‖) {C₀ : ℝ} {k : ℕ} (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k)
    {Γ Γ' : Set E} (hΓ : MeasurableSet Γ) {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) (s : ℝ)
    (hL2 : ∫⁻ η in Γ, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖F η‖) ^ 2 ∂μ < ∞) {H : E → G}
    (hH : ∀ η ∈ Γ', HasSum (fun i ↦ a i • F (η - v i)) (H η)) :
    ∫⁻ η in Γ', ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖H η‖) ^ 2 ∂μ < ∞ := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  have hc' : 0 ≤ 1 + c⁻¹ := by linarith [inv_pos.2 hc]
  set N := ⌈|s|⌉₊
  set r : ℝ := ((finrank ℝ E + 1 : ℕ) : ℝ)
  set D := C₀ * (1 + c⁻¹) ^ ((N + k : ℕ) + r)
  have hD : 0 ≤ D := mul_nonneg hC₀ (Real.rpow_nonneg hc' _)
  -- The near part `g`, the coefficients `b` and `e`, and the far part `h`.
  set g : E → ℝ≥0∞ := fun ζ ↦
    ENNReal.ofReal (Γ.indicator (fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖F ζ‖) ζ)
  set b : ι → ℝ≥0∞ := fun i ↦ ENNReal.ofReal (2 ^ (|s| / 2) * (1 + ‖v i‖ ^ 2) ^ (|s| / 2) * ‖a i‖)
  set e : ι → ℝ≥0∞ := fun i ↦ ENNReal.ofReal ((1 + ‖v i‖) ^ ((N + 2 * k : ℕ) + r) * ‖a i‖)
  set h : E → ℝ≥0∞ := fun η ↦ ENNReal.ofReal (D * (1 + ‖η‖) ^ (-r))
  have hw : Continuous fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ (s / 2) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const fun x ↦
      Or.inl (by positivity : (1 : ℝ) + ‖x‖ ^ 2 ≠ 0)
  have hg : Measurable g := ((hw.measurable.mul hFm).indicator hΓ).ennreal_ofReal
  have hh : Measurable h := by fun_prop
  have hb : ∑' i, b i ≠ ∞ := by
    refine tsum_ofReal_ne_top (((ha N).mul_left (2 ^ (|s| / 2))).of_nonneg_of_le
      (fun i ↦ by positivity) fun i ↦ ?_) fun i ↦ by positivity
    rw [mul_assoc]
    gcongr
    calc _ ≤ (1 + ‖v i‖) ^ ⌈|(|s|)|⌉₊ := one_add_norm_sq_rpow_le_one_add_norm_pow_ceil |s| (v i)
      _ = (1 + ‖v i‖) ^ N := by rw [abs_abs]
  have he : ∑' i, e i ≠ ∞ := by
    refine tsum_ofReal_ne_top ((ha (N + 2 * k + (finrank ℝ E + 1))).congr fun i ↦ ?_)
      fun i ↦ by positivity
    rw [← Real.rpow_natCast]
    congr 2
    push_cast [r]
    ring
  have hg2 : ∫⁻ η, g η ^ 2 ∂μ < ∞ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hL2
    rw [← lintegral_indicator hΓ]
    refine lintegral_congr fun ζ ↦ ?_
    by_cases hζ : ζ ∈ Γ <;> simp [g, hζ]
  -- The pointwise bound by the near and far parts.
  have hpt : ∀ η ∈ Γ', ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖H η‖) ≤
      ∑' i, b i * g (η - v i) + (∑' i, e i) * h η := fun η hη ↦
    ofReal_mul_norm_le_of_hasSum hF hc hΓ' s r (by positivity) hη (hH η hη)
  -- Both parts are square integrable.
  set X : E → ℝ≥0∞ := fun η ↦ ∑' i, b i * g (η - v i)
  have hX : Measurable X :=
    Measurable.tsum fun i ↦ measurable_const.mul (hg.comp (measurable_sub_const _))
  have hX2 : ∫⁻ η, X η ^ 2 ∂μ < ∞ := (lintegral_tsum_mul_comp_sub_sq_le hg b v).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top hb.lt_top) hg2)
  have hh2 : ∫⁻ η, ((∑' i, e i) * h η) ^ 2 ∂μ < ∞ := by
    simp_rw [mul_pow]
    rw [lintegral_const_mul _ (hh.pow_const 2)]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top he.lt_top)
      (lintegral_ofReal_mul_one_add_norm_rpow_neg_sq_lt_top hD (by simp [r]))
  calc ∫⁻ η in Γ', ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖H η‖) ^ 2 ∂μ
      ≤ ∫⁻ η in Γ', (X η + (∑' i, e i) * h η) ^ 2 ∂μ :=
        setLIntegral_mono ((hX.add (measurable_const.mul hh)).pow_const 2) fun η hη ↦
          pow_le_pow_left' (hpt η hη) 2
    _ ≤ ∫⁻ η, (X η + (∑' i, e i) * h η) ^ 2 ∂μ := setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ η, 2 * (X η ^ 2 + ((∑' i, e i) * h η) ^ 2) ∂μ :=
        lintegral_mono fun η ↦ ENNReal.add_sq_le _ _
    _ = 2 * (∫⁻ η, X η ^ 2 ∂μ + ∫⁻ η, ((∑' i, e i) * h η) ^ 2 ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_add_left (hX.pow_const 2)]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofNat_lt_top (ENNReal.add_lt_top.2 ⟨hX2, hh2⟩)

/-- **Square integrable decay of a discrete convolution on a smaller cone.** A superposition
`H η = ∑ i, a i • F (η - v i)` of translates of a function `F` of polynomial growth, with
coefficients `a i` rapidly decreasing in `‖v i‖`, has finite weighted square integral
`∫_Γ' ⟨η⟩ ^ (2 s) ‖H η‖ ^ 2` on every set `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)`,
`c > 0`, lie in a measurable set `Γ` on which `∫_Γ ⟨η⟩ ^ (2 s) ‖F η‖ ^ 2` is finite. -/
theorem setLIntegral_ofReal_one_add_norm_sq_rpow_mul_norm_sq_lt_top_of_hasSum {ι 𝕜 G : Type*}
    [NormedField 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {v : ι → E}
    {a : ι → 𝕜} (ha : ∀ j : ℕ, Summable fun i ↦ (1 + ‖v i‖) ^ j * ‖a i‖) {F : E → G}
    (hFm : Measurable fun ζ ↦ ‖F ζ‖) {C₀ : ℝ} {k : ℕ} (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k)
    {Γ Γ' : Set E} (hΓ : MeasurableSet Γ) {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) (s : ℝ)
    (hL2 : ∫⁻ η in Γ, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖F η‖) ^ 2 ∂μ < ∞) {H : E → G}
    (hH : ∀ η ∈ Γ', HasSum (fun i ↦ a i • F (η - v i)) (H η)) :
    ∫⁻ η in Γ', ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖H η‖) ^ 2 ∂μ < ∞ := by
  -- Only the countably many indices with `a i ≠ 0` contribute.
  set S := support a
  have hS : S.Countable := by
    have h := (ha 0).countable_support
    simp only [pow_zero, one_mul] at h
    exact h.mono fun i hi ↦ norm_ne_zero_iff.2 hi
  have := hS.to_subtype
  refine setLIntegral_ofReal_one_add_norm_sq_rpow_mul_norm_sq_lt_top_of_hasSum_of_countable
    (v := fun i : S ↦ v i) (a := fun i : S ↦ a i) (fun j ↦ (ha j).subtype (· ∈ S)) hFm hF hΓ hc
    hΓ' s hL2 fun η hη ↦ (hasSum_subtype_iff_of_support_subset fun i hi ↦ ?_).2 (hH η hη)
  by_contra hiS
  exact hi (by simp [show a i = 0 from not_not.1 hiS])

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- On the ball of radius `R u` with `R ≥ 1`, the weight `⟨η⟩ ^ (2 s)` with `-n ≤ 2 s` is at least
`(R (1 + u)) ^ (-n)`. -/
private theorem rpow_neg_finrank_le_one_add_norm_sq_rpow {s : ℝ}
    (hs : -(finrank ℝ E : ℝ) ≤ 2 * s) {R u : ℝ} (hR : 1 ≤ R) (hu : 0 ≤ u) {η : E}
    (hη : ‖η‖ ≤ R * u) :
    (R * (1 + u)) ^ (-(finrank ℝ E : ℝ)) ≤ (1 + ‖η‖ ^ 2) ^ s := by
  have h1 : 1 ≤ 1 + ‖η‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have hle : 1 + ‖η‖ ^ 2 ≤ (R * (1 + u)) ^ 2 := by nlinarith [norm_nonneg η]
  calc (R * (1 + u)) ^ (-(finrank ℝ E : ℝ))
      = ((R * (1 + u)) ^ 2) ^ (-(finrank ℝ E : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
    _ ≤ (1 + ‖η‖ ^ 2) ^ (-(finrank ℝ E : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by
          have := (finrank ℝ E).cast_nonneg (α := ℝ)
          linarith)
    _ ≤ (1 + ‖η‖ ^ 2) ^ s := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- **Divergence of the weight over a cone.** An open set `Γ`, closed under multiplication by
positive reals and containing a nonzero point, has `∫_Γ ⟨η⟩ ^ (2 s) = ∞` when `-dim E ≤ 2 s`. -/
theorem setLIntegral_ofReal_one_add_norm_sq_rpow_eq_top {Γ : Set E} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {ξ : E} (hξ : ξ ∈ Γ) (hξ0 : ξ ≠ 0) {s : ℝ}
    (hs : -(finrank ℝ E : ℝ) ≤ 2 * s) :
    ∫⁻ η in Γ, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ s) ∂μ = ∞ := by
  set u := ‖ξ‖
  have hu : 0 < u := norm_pos_iff.2 hξ0
  set n := finrank ℝ E
  -- The part `A` of `Γ` in the shell `u < ‖η‖ < 2 u` is open and nonempty, and its dilates
  -- `A j = 2 ^ j • A` are disjoint subsets of `Γ`.
  set A : Set E := Γ ∩ {η | u < ‖η‖ ∧ ‖η‖ < 2 * u}
  have hAo : IsOpen A := hΓ.inter ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const))
  have hA : μ A ≠ 0 := by
    refine (hAo.measure_pos μ ⟨(3 / 2 : ℝ) • ξ, hcone _ (by norm_num) ξ hξ, ?_⟩).ne'
    simp only [mem_ofPred_eq, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2), u]
    constructor <;> linarith
  set B : ℕ → Set E := fun j ↦ (2 ^ j : ℝ) • A
  have hBm (j : ℕ) : MeasurableSet (B j) := (hAo.smul₀ (by positivity)).measurableSet
  have hBnorm {j : ℕ} {η : E} (hη : η ∈ B j) : 2 ^ j * u < ‖η‖ ∧ ‖η‖ < 2 ^ (j + 1) * u := by
    obtain ⟨ζ, ⟨-, hζ1, hζ2⟩, rfl⟩ := Set.mem_smul_set.1 hη
    rw [norm_smul, Real.norm_of_nonneg (by positivity), pow_succ]
    constructor <;> nlinarith [pow_pos (two_pos (α := ℝ)) j]
  have hBΓ : (⋃ j, B j) ⊆ Γ := iUnion_subset fun j η hη ↦ by
    obtain ⟨ζ, ⟨hζ, -⟩, rfl⟩ := Set.mem_smul_set.1 hη
    exact hcone _ (by positivity) ζ hζ
  have hBd : Pairwise (Disjoint on B) := by
    refine (pairwise_disjoint_on B).2 fun i j hij ↦ Set.disjoint_left.2 fun η hi hj ↦ ?_
    have h2 : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j := pow_le_pow_right₀ one_le_two hij
    nlinarith [(hBnorm hi).2, (hBnorm hj).1]
  -- Each dilate contributes at least `(2 (1 + u)) ^ (-n) μ A`.
  set κ : ℝ≥0∞ := ENNReal.ofReal ((2 * (1 + u)) ^ (-(n : ℝ))) * μ A
  have hκ : κ ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hA
  have hBκ (j : ℕ) : κ ≤ ∫⁻ η in B j, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ s) ∂μ := by
    have hbound : ∀ η ∈ B j, ENNReal.ofReal ((2 ^ (j + 1) * (1 + u)) ^ (-(n : ℝ))) ≤
        ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ s) := fun η hη ↦
      ENNReal.ofReal_le_ofReal (rpow_neg_finrank_le_one_add_norm_sq_rpow hs
        (one_le_pow₀ one_le_two) hu.le (hBnorm hη).2.le)
    refine le_trans (le_of_eq ?_) ((setLIntegral_const _ _).symm.trans_le
      (setLIntegral_mono (by fun_prop) hbound))
    rw [Measure.addHaar_smul, abs_of_pos (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    rw [pow_succ, mul_assoc, Real.mul_rpow (by positivity) (by positivity), mul_right_comm,
      Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_cancel₀ (by positivity), one_mul]
  refine eq_top_iff.2 ?_
  calc ∞ = ∑' _ : ℕ, κ := (ENNReal.tsum_const_eq_top_of_ne_zero hκ).symm
    _ ≤ ∑' j, ∫⁻ η in B j, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ s) ∂μ := tsum_le_tsum hBκ
    _ = ∫⁻ η in ⋃ j, B j, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ s) ∂μ := (lintegral_iUnion hBm hBd _).symm
    _ ≤ _ := lintegral_mono_set hBΓ

end TauCeti
