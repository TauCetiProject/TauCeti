/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.LaplaceTransform.Mellin
import TauCeti.Analysis.MellinTransform.UpperTail

/-!
# Mellin transforms of first Riesz sums

When `LSeriesSummable a s` holds at `s : ℂ` with `1 < s.re`, the Mellin integrand
`y ↦ TauCeti.rieszSum a y * y ^ (-s - 1)` is integrable on `(1, ∞)` with integral
`LSeries a s / (s * (s - 1))`.

The proof decomposes `TauCeti.rieszSum a y` as a countable sum of individual ramp terms and
interchanges summation with Lebesgue and Bochner integration using
`TauCeti.integrableOn_ramp_mul_cpow` and `TauCeti.integral_ramp_mul_cpow`.

## Main results

* `TauCeti.integrableOn_rieszSum_mul_cpow`: integrability of `y ↦ rieszSum a y * y ^ (-s - 1)` on
  `(1, ∞)` for `1 < s.re` and `LSeriesSummable a s`.
* `TauCeti.integral_rieszSum_mul_cpow`: evaluation
  `∫ y in Set.Ioi 1, rieszSum a y * y ^ (-s - 1) = LSeries a s / (s * (s - 1))`.
* `Meromorphic.integrableOn_and_integral_rieszSum_add_mul_cpow_eq_rieszRemainderMellin`: when
  `LSeries a = -L′/L` at `s`, the Riesz sum corrected by the main term read off from the order
  and finite part of `L′/L` at `1` has Mellin transform `TauCeti.rieszRemainderMellin L s`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 5.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12 and §9.
* L. Alpöge's formalization of the generalized Riemann hypothesis (`Deduction.mellin_ramp`).
-/

public section

open Complex MeasureTheory

namespace TauCeti

private noncomputable def rampTerm (a : ℕ → ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  if 1 ≤ n then (Set.Ici (n : ℝ)).indicator (fun t : ℝ ↦ a n * ((t : ℂ) / n - 1)) y else 0

private theorem tsum_rampTerm_eq_rieszSum (a : ℕ → ℂ) (y : ℝ) :
    ∑' n : ℕ, rampTerm a n y = rieszSum a y := by
  calc ∑' n : ℕ, rampTerm a n y
      = ∑' n : ℕ, (if 1 ≤ n ∧ (n : ℝ) ≤ y then a n * ((y : ℂ) / n - 1) else 0) := by
          refine tsum_congr fun n ↦ ?_
          by_cases hn1 : 1 ≤ n
          · by_cases hny : (n : ℝ) ≤ y <;> simp [rampTerm, hn1, hny]
          · simp [rampTerm, hn1]
    _ = rieszSum a y := tsum_ite_mul_div_sub_one_eq_rieszSum a y

private theorem rampTerm_mul_cpow_ae_eq (a : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    (fun y : ℝ ↦ rampTerm a n y * (y : ℂ) ^ (-s - 1)) =ᵐ[volume.restrict (Set.Ioi 1)]
      (Set.Ioi (n : ℝ)).indicator (fun y : ℝ ↦
        if 1 ≤ n then a n * (((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1)) else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [rampTerm]
  · have hn1 : 1 ≤ n := hn0
    refine ae_restrict_of_ae ?_
    filter_upwards [Measure.ae_ne volume (n : ℝ)] with y hy
    by_cases hyn : (n : ℝ) < y
    · simp [rampTerm, hn1, hyn.le, hyn, mul_assoc]
    · have hnotle : ¬ (n : ℝ) ≤ y := fun h ↦ hy (le_antisymm (not_lt.mp hyn) h)
      simp [rampTerm, hn1, hyn, hnotle]

private theorem lintegral_norm_rampTerm_mul_cpow_le (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ∫⁻ y in Set.Ioi (1 : ℝ), ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ ≤
      ENNReal.ofReal (‖LSeries.term a s n‖ / (s.re * (s.re - 1))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [rampTerm]
  · have hn1 : 1 ≤ n := hn0
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hsub : Set.Ioi (n : ℝ) ⊆ Set.Ioi (1 : ℝ) :=
      Set.Ioi_subset_Ioi (by exact_mod_cast hn1)
    have hint := integrableOn_ramp_mul_rpow hnpos hs
    have heq : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi 1),
        ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ =
          (Set.Ioi (n : ℝ)).indicator (fun y : ℝ ↦
            ENNReal.ofReal (‖a n‖ * ((y / n - 1) * y ^ (-s.re - 1)))) y := by
      filter_upwards [rampTerm_mul_cpow_ae_eq a n s] with y hy
      rw [hy]
      by_cases hyn : (n : ℝ) < y
      · have hypos : 0 < y := hnpos.trans hyn
        have hyn1 : 1 ≤ y / n := (one_le_div hnpos).mpr hyn.le
        rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hyn),
          Set.indicator_of_mem (Set.mem_Ioi.mpr hyn)]
        simp only [hn1, ↓reduceIte]
        rw [← ofReal_norm, norm_mul, norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
          Complex.norm_ofReal_sub_one hyn1,
          Complex.norm_cpow_eq_rpow_re_of_pos hypos, sub_re, neg_re, one_re]
      · simp [Set.indicator_of_notMem (Set.notMem_Ioi.mpr (not_lt.mp hyn))]
    have hnonneg : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi (n : ℝ)),
        0 ≤ ‖a n‖ * ((y / n - 1) * y ^ (-s.re - 1)) :=
      ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦
        mul_nonneg (norm_nonneg _) (mul_nonneg
          (sub_nonneg.mpr ((one_le_div hnpos).mpr hy.le))
          (Real.rpow_nonneg (hnpos.trans hy).le _))
    rw [lintegral_congr_ae heq, lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Set.inter_eq_left.mpr hsub,
      ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) hnonneg, integral_const_mul,
      integral_ramp_mul_rpow hnpos hs]
    refine (congrArg ENNReal.ofReal ?_).le
    simp only [LSeries.norm_term_eq, hn0.ne', ↓reduceIte, Real.rpow_neg hnpos.le]
    ring

private theorem integrableOn_rampTerm_mul_cpow (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ rampTerm a n y * (y : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
  refine Integrable.congr ?_ (rampTerm_mul_cpow_ae_eq a n s).symm
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  · have hn1 : 1 ≤ n := hn0
    have hint : IntegrableOn (fun y : ℝ ↦ a n * (((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1)))
        (Set.Ioi (n : ℝ)) :=
      (integrableOn_ramp_mul_cpow (Nat.cast_pos.mpr hn1) hs).const_mul _
    have hind : IntegrableOn ((Set.Ioi (n : ℝ)).indicator
        (fun y : ℝ ↦ a n * (((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1)))) (Set.Ioi 1) :=
      (integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
        (hint.mono_set Set.inter_subset_left)
    refine hind.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
    by_cases hyn : (n : ℝ) < y <;> simp [hn1, hyn]

private theorem tsum_lintegral_norm_rampTerm_ne_top {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (h : LSeriesSummable a s) :
    ∑' n : ℕ, ∫⁻ y in Set.Ioi (1 : ℝ), ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (tsum_le_tsum fun n ↦
    lintegral_norm_rampTerm_mul_cpow_le a n hs) ?_)
  have hsum : Summable fun n : ℕ ↦ ‖LSeries.term a s n‖ / (s.re * (s.re - 1)) :=
    h.norm.div_const _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ div_nonneg (norm_nonneg _) (by positivity)) hsum]
  exact ENNReal.ofReal_lt_top

/-- **Mellin integrability of Riesz sums**: if `1 < s.re` and `LSeriesSummable a s`,
then `y ↦ rieszSum a y * y ^ (-s - 1)` is integrable on `(1, ∞)`. -/
theorem integrableOn_rieszSum_mul_cpow {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (h : LSeriesSummable a s) :
    IntegrableOn (fun y : ℝ ↦ rieszSum a y * (y : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
  have hae : AEStronglyMeasurable (fun y : ℝ ↦ rieszSum a y * (y : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ioi 1)) := by
    have hcont : ContinuousOn (fun y : ℝ ↦ rieszSum a y * (y : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
      refine (continuous_rieszSum a).continuousOn.mul ?_
      refine ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun y hy ↦ Or.inl ?_
      have : (0 : ℝ) < y := zero_lt_one.trans hy
      simpa using this
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  refine ⟨hae, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  have hle : ∀ y : ℝ, ‖rieszSum a y * (y : ℂ) ^ (-s - 1)‖ₑ ≤
      ∑' n : ℕ, ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ := by
    intro y
    have hsum : rieszSum a y * (y : ℂ) ^ (-s - 1) =
        ∑' n : ℕ, rampTerm a n y * (y : ℂ) ^ (-s - 1) := by
      rw [← tsum_rampTerm_eq_rieszSum, tsum_mul_right]
    rw [hsum]
    exact eNorm_tsum_le_tsum_eNorm
  calc ∫⁻ y in Set.Ioi (1 : ℝ), ‖rieszSum a y * (y : ℂ) ^ (-s - 1)‖ₑ
      ≤ ∫⁻ y in Set.Ioi (1 : ℝ), ∑' n : ℕ, ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ :=
        lintegral_mono hle
    _ = ∑' n : ℕ, ∫⁻ y in Set.Ioi (1 : ℝ), ‖rampTerm a n y * (y : ℂ) ^ (-s - 1)‖ₑ :=
        lintegral_tsum fun n ↦ (integrableOn_rampTerm_mul_cpow a n hs).1.eNorm
    _ < ⊤ := (tsum_lintegral_norm_rampTerm_ne_top hs h).lt_top

/-- **Mellin transform of Riesz sums**: if `1 < s.re` and `LSeriesSummable a s`,
then `∫ y in Set.Ioi 1, rieszSum a y * y ^ (-s - 1) = LSeries a s / (s * (s - 1))`. -/
theorem integral_rieszSum_mul_cpow {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (h : LSeriesSummable a s) :
    ∫ y in Set.Ioi (1 : ℝ), rieszSum a y * (y : ℂ) ^ (-s - 1) =
      LSeries a s / (s * (s - 1)) := by
  have heq : (fun y : ℝ ↦ rieszSum a y * (y : ℂ) ^ (-s - 1)) =
      fun y : ℝ ↦ ∑' n : ℕ, rampTerm a n y * (y : ℂ) ^ (-s - 1) := by
    ext y
    rw [← tsum_rampTerm_eq_rieszSum, tsum_mul_right]
  rw [heq, MeasureTheory.integral_tsum (fun n ↦ (integrableOn_rampTerm_mul_cpow a n hs).1)
    (tsum_lintegral_norm_rampTerm_ne_top hs h)]
  have hterm : ∀ n : ℕ, ∫ y in Set.Ioi (1 : ℝ), rampTerm a n y * (y : ℂ) ^ (-s - 1) =
      LSeries.term a s n / (s * (s - 1)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [rampTerm]
    · have hn1 : 1 ≤ n := hn0
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      have hsub : Set.Ioi (n : ℝ) ⊆ Set.Ioi (1 : ℝ) :=
        Set.Ioi_subset_Ioi (by exact_mod_cast hn1)
      have hint_if : (fun y : ℝ ↦
            if 1 ≤ n then a n * (((y : ℂ) / n - 1) * (y : ℂ) ^ (-s - 1)) else 0) =
          fun y : ℝ ↦ a n * (((y : ℂ) / ((n : ℝ) : ℂ) - 1) * (y : ℂ) ^ (-s - 1)) := by
        ext y
        simp [hn1]
      rw [integral_congr_ae (rampTerm_mul_cpow_ae_eq a n s), integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, Set.inter_eq_left.mpr hsub, hint_if,
        integral_const_mul, integral_ramp_mul_cpow hnpos hs, Complex.ofReal_natCast,
        LSeries.term_of_ne_zero hn0.ne', Complex.cpow_neg]
      ring
  simp_rw [hterm]
  rw [tsum_div_const, LSeries]

/-- **Mellin transform of a first Riesz remainder.** Let `L` be meromorphic, analytic and
nonzero at `s` with `1 < s.re`, and let `LSeries a s = -logDeriv L s`. Write `m` for the order
of `L` at `1` and `c` for the finite part of `L′/L` there. Then the first Riesz sum of `a`
plus the main term `(c - m) y + m y log y` has absolutely convergent upper Mellin transform
`rieszRemainderMellin L s`. -/
theorem _root_.Meromorphic.integrableOn_and_integral_rieszSum_add_mul_cpow_eq_rieszRemainderMellin
    {a : ℕ → ℂ} {L : ℂ → ℂ} (hL : Meromorphic L) {s : ℂ} (hs : 1 < s.re)
    (hsum : LSeriesSummable a s) (hLS : LSeries a s = -logDeriv L s) (ha : AnalyticAt ℂ L s)
    (hne : L s ≠ 0) :
    IntegrableOn (fun y : ℝ ↦ (rieszSum a y +
      ((logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀) * y +
        (meromorphicOrderAt L 1).untop₀ * y * Real.log y)) * (y : ℂ) ^ (-s - 1)) (Set.Ioi 1) ∧
    ∫ y in Set.Ioi (1 : ℝ), (rieszSum a y +
      ((logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀) * y +
        (meromorphicOrderAt L 1).untop₀ * y * Real.log y)) * (y : ℂ) ^ (-s - 1) =
      rieszRemainderMellin L s := by
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; norm_num at hs
  have hR := integrableOn_rieszSum_mul_cpow hs hsum
  obtain ⟨hM, hval⟩ := integrableOn_and_integral_mul_add_mul_log_mul_cpow
    (logDerivFinitePart L 1 - (meromorphicOrderAt L 1).untop₀)
    ((meromorphicOrderAt L 1).untop₀ : ℂ) hs
  -- Split the transform into the Riesz sum and the main-term correction.
  conv in (occs := *) (rieszSum _ _ + _) * _ => rw [add_mul]
  refine ⟨hR.add hM, ?_⟩
  rw [integral_add hR hM, integral_rieszSum_mul_cpow hs hsum, hLS, hval,
    (hL.rieszRemainderMellin_eq_and_analyticAt h₀ h₁ ha hne).1]
  field_simp [h₀, sub_ne_zero.mpr h₁]
  ring

end TauCeti
