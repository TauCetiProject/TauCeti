/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import TauCeti.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.ArithmeticFunction.Moebius

/-!
# El Marraki's identities and conversion inequalities

Following Ramaré (2013, Lemma 9.1 and Corollary 1.2), substituting `u = D / t` in
`∫_1^D ⌊D / t⌋ M(t) / t dt` and integrating `⌊u⌋ / u` by Abel summation yields El Marraki's
integral identity:

`∫_1^D ⌊D / t⌋ M(t) / t dt = log D` for `D ≥ 1`.

Combining this with Abel summation `m(D) = M(D) / D + ∫_1^D M(t) / t² dt` gives El Marraki's
identity for `m(D) = ∑_{n ≤ D} μ(n) / n`:

`m(D) = M(D) / D + (1 / D) ∫_1^D (D / t - ⌊D / t⌋) M(t) / t dt + (log D) / D`,

and hence El Marraki's conversion inequality and two-range bound estimating `|m(D)|` in terms of
`|M(D)|` and `∫_1^D |M(t)| / t dt`.

## Main declarations

* `TauCeti.integral_natFloor_div_mul_moebiusSum_div`: El Marraki's integral identity
  `∫_1^D ⌊D / t⌋ M(t) / t dt = log D`.
* `TauCeti.moebiusDivSum_eq_elMarraki`: El Marraki's identity for `m(D)`.
* `TauCeti.abs_moebiusDivSum_le_elMarraki`: El Marraki's conversion inequality.
* `TauCeti.abs_moebiusDivSum_le_elMarraki_of_le_mul`: El Marraki's two-range conversion bound.

## References

* O. Ramaré, *From explicit estimates for primes to explicit estimates for the Möbius function*,
  Acta Arith. 157 (2013), 365–379, Lemma 9.1 and Corollary 1.2.
-/

public section

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- Pointwise change-of-variables identity for `u = D / t` in El Marraki's integral. -/
private theorem div_sq_smul_moebiusSum_div_natFloor_div {D t : ℝ} (hD0 : D ≠ 0) (ht0 : t ≠ 0) :
    (D / t ^ 2) • (moebiusSum (D / (D / t)) * ((⌊D / t⌋₊ : ℝ) / (D / t))) =
      (⌊D / t⌋₊ : ℝ) * moebiusSum t / t := by
  rw [smul_eq_mul, div_div_eq_mul_div, mul_div_cancel_left₀ t hD0]
  field_simp

/-- Integrability of the three El Marraki integrands on `1..D`. -/
private theorem intervalIntegrable_elMarraki_pieces {D : ℝ} (hD : 1 ≤ D) :
    IntervalIntegrable (fun t ↦ moebiusSum t / t ^ 2) volume 1 D ∧
      IntervalIntegrable (fun t ↦ (⌊D / t⌋₊ : ℝ) * moebiusSum t / t) volume 1 D ∧
      IntervalIntegrable (fun t ↦ (D / t - ⌊D / t⌋₊) * moebiusSum t / t) volume 1 D := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have h1 : IntervalIntegrable (fun t ↦ moebiusSum t / t ^ 2) volume 1 D :=
    intervalIntegrable_moebiusSum_div_sq 1 D
  have hsub := (TauCeti.intervalIntegral.intervalIntegrable_div_sq_smul_comp_div_iff (c := D)
    (by rw [Set.uIcc_of_le hD]; rintro ⟨h, -⟩; linarith)
    (fun u ↦ moebiusSum (D / u) * ((⌊u⌋₊ : ℝ) / u))).mpr <| by
      rw [div_self hD0.ne', div_one]
      exact intervalIntegrable_moebiusSum_div_mul hD (intervalIntegrable_natFloor_div 1 D)
  have h2 :
      IntervalIntegrable (fun t ↦ (⌊D / t⌋₊ : ℝ) * moebiusSum t / t) volume 1 D := by
    refine (intervalIntegrable_congr fun t ht ↦ ?_).mp hsub
    have ht1 : 1 ≤ t := (Set.uIcc_of_le hD ▸ Set.uIoc_subset_uIcc ht).1
    exact div_sq_smul_moebiusSum_div_natFloor_div hD0.ne' (zero_lt_one.trans_le ht1).ne'
  have h3 :
      IntervalIntegrable (fun t ↦ (D / t - ⌊D / t⌋₊) * moebiusSum t / t) volume 1 D := by
    refine (intervalIntegrable_congr fun t ht ↦ ?_).mp ((h1.const_mul D).sub h2)
    have ht1 : 1 ≤ t := (Set.uIcc_of_le hD ▸ Set.uIoc_subset_uIcc ht).1
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht1).ne'
    field_simp
  exact ⟨h1, h2, h3⟩

/-- **El Marraki's integral identity**: for every real `D ≥ 1`,
`∫_1^D ⌊D / t⌋ M(t) / t dt = log D`. -/
theorem integral_natFloor_div_mul_moebiusSum_div {D : ℝ} (hD : 1 ≤ D) :
    ∫ t in (1 : ℝ)..D, (⌊D / t⌋₊ : ℝ) * moebiusSum t / t = Real.log D := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  -- Change variables `u = D / t` and swap the integral with the sum defining `M(D / u)`.
  have hsub := TauCeti.intervalIntegral.integral_div_sq_smul_comp_div (c := D)
    (by rw [Set.uIcc_of_le hD]; rintro ⟨h, -⟩; linarith)
    (fun u ↦ moebiusSum (D / u) * ((⌊u⌋₊ : ℝ) / u))
  rw [div_self hD0.ne', div_one] at hsub
  have hcongr :
      ∫ t in (1 : ℝ)..D, (⌊D / t⌋₊ : ℝ) * moebiusSum t / t =
        ∫ t in (1 : ℝ)..D,
          (D / t ^ 2) • (moebiusSum (D / (D / t)) * ((⌊D / t⌋₊ : ℝ) / (D / t))) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hD] at ht
    exact (div_sq_smul_moebiusSum_div_natFloor_div hD0.ne'
      (zero_lt_one.trans_le ht.1).ne').symm
  rw [hcongr, hsub, integral_moebiusSum_div_mul hD (intervalIntegrable_natFloor_div 1 D)]
  -- Evaluate the inner integral `∫_1^{D/n} ⌊u⌋₊ / u du` and apply Meissel & hyperbola inversion.
  have hlog :
      ∑ n ∈ Icc 1 ⌊D⌋₊, (μ n : ℝ) * ∫ u in (1 : ℝ)..(D / n), (⌊u⌋₊ : ℝ) / u =
        (∑ n ∈ Icc 1 ⌊D⌋₊, (μ n : ℝ) * ⌊D / n⌋₊) * Real.log D -
          ∑ n ∈ Icc 1 ⌊D⌋₊, μ n •
            ∑ m ∈ Icc 1 (⌊D⌋₊ / n), Real.log ((n * m : ℕ) : ℝ) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [integral_natFloor_div (D / (n : ℝ)), Nat.floor_div_natCast,
      Real.log_div hD0.ne' hn0.ne', zsmul_eq_mul]
    have hsplit :
        ∑ m ∈ Icc 1 (⌊D⌋₊ / n), Real.log ((n * m : ℕ) : ℝ) =
          (⌊D⌋₊ / n : ℕ) * Real.log n + ∑ m ∈ Icc 1 (⌊D⌋₊ / n), Real.log m := by
      have hterm (m : ℕ) (hm : m ∈ Icc 1 (⌊D⌋₊ / n)) :
          Real.log ((n * m : ℕ) : ℝ) = Real.log n + Real.log m := by
        have hm0 : (m : ℝ) ≠ 0 := by
          exact_mod_cast Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hm).1
        rw [Nat.cast_mul, Real.log_mul hn0.ne' hm0]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul]
    rw [hsplit]
    ring
  rw [hlog, sum_moebius_mul_natFloor_div hD, one_mul,
    ArithmeticFunction.sum_moebius_smul_sum_div ⌊D⌋₊ (fun k ↦ Real.log k)]
  simp

/-- **El Marraki's identity**: for every real `D ≥ 1`,
`m(D) = M(D) / D + (1 / D) ∫_1^D (D / t - ⌊D / t⌋) M(t) / t dt + (log D) / D`. -/
theorem moebiusDivSum_eq_elMarraki {D : ℝ} (hD : 1 ≤ D) :
    moebiusDivSum D =
      moebiusSum D / D +
        (1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t) +
        Real.log D / D := by
  have habel := moebiusDivSum_eq_div_add_integral D
  obtain ⟨_, h2, hrem⟩ := intervalIntegrable_elMarraki_pieces hD
  have hsplit :
      (1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t) +
          (1 / D) * (∫ t in (1 : ℝ)..D, (⌊D / t⌋₊ : ℝ) * moebiusSum t / t) =
        ∫ t in (1 : ℝ)..D, moebiusSum t / t ^ 2 := by
    rw [← mul_add, ← intervalIntegral.integral_add hrem h2,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hD] at ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    field_simp
    ring
  rw [integral_natFloor_div_mul_moebiusSum_div hD] at hsplit
  rw [habel, ← hsplit]
  ring

/-- **El Marraki's conversion inequality** (Ramaré 2013, Lemma 9.1): for every real `D ≥ 1`,
`|m(D)| ≤ |M(D)| / D + (1 / D) ∫_1^D |M(t)| / t dt + (log D) / D`. -/
theorem abs_moebiusDivSum_le_elMarraki {D : ℝ} (hD : 1 ≤ D) :
    |moebiusDivSum D| ≤
      |moebiusSum D| / D + (1 / D) * (∫ t in (1 : ℝ)..D, |moebiusSum t| / t) +
        Real.log D / D := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlog : 0 ≤ Real.log D / D := div_nonneg (Real.log_nonneg hD) hD0.le
  have habs_int := intervalIntegrable_abs_moebiusSum_div 1 D
  have hrem := (intervalIntegrable_elMarraki_pieces hD).2.2
  have hle_int :
      |∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t| ≤
        ∫ t in (1 : ℝ)..D, |moebiusSum t| / t := by
    refine (intervalIntegral.abs_integral_le_integral_abs hD).trans ?_
    refine intervalIntegral.integral_mono_on hD hrem.abs habs_int fun t ht ↦ ?_
    have ht0 : 0 < t := zero_lt_one.trans_le ht.1
    have hfr0 : 0 ≤ D / t - ⌊D / t⌋₊ :=
      sub_nonneg.mpr (Nat.floor_le (div_nonneg hD0.le ht0.le))
    have hfr1 : D / t - ⌊D / t⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one (D / t)]
    rw [abs_div, abs_mul, abs_of_nonneg hfr0, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hfr1) ht0.le
  calc |moebiusDivSum D|
      = |moebiusSum D / D +
          (1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t) +
          Real.log D / D| := by rw [moebiusDivSum_eq_elMarraki hD]
    _ ≤ |moebiusSum D / D +
          (1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t)| +
          |Real.log D / D| := abs_add_le _ _
    _ ≤ (|moebiusSum D / D| +
          |(1 / D) * (∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t)|) +
          |Real.log D / D| := add_le_add (abs_add_le _ _) le_rfl
    _ = |moebiusSum D| / D +
          (1 / D) * |∫ t in (1 : ℝ)..D, (D / t - ⌊D / t⌋₊) * moebiusSum t / t| +
          Real.log D / D := by
        rw [abs_div, abs_of_pos hD0, abs_mul, abs_of_pos (one_div_pos.mpr hD0),
          abs_of_nonneg hlog]
    _ ≤ |moebiusSum D| / D + (1 / D) * (∫ t in (1 : ℝ)..D, |moebiusSum t| / t) +
          Real.log D / D := by gcongr

/-- **El Marraki's two-range conversion bound** (Ramaré 2013, Corollary 1.2):
if `1 ≤ t₀ ≤ D`, `|M(t)| ≤ ε(t) t` on `[t₀, D]`, and `ε` is interval integrable on `t₀..D`,
then
`|m(D)| ≤ ε(D) + (1 / D) (∫_1^{t₀} |M(t)| / t dt + ∫_{t₀}^D ε(t) dt) + (log D) / D`. -/
theorem abs_moebiusDivSum_le_elMarraki_of_le_mul {t₀ D : ℝ} (ht₀ : 1 ≤ t₀)
    (hD : t₀ ≤ D) {ε : ℝ → ℝ} (hε : IntervalIntegrable ε volume t₀ D)
    (hM : ∀ t ∈ Set.Icc t₀ D, |moebiusSum t| ≤ ε t * t) :
    |moebiusDivSum D| ≤
      ε D + (1 / D) * ((∫ t in (1 : ℝ)..t₀, |moebiusSum t| / t) + ∫ t in t₀..D, ε t) +
        Real.log D / D := by
  have h1D : 1 ≤ D := ht₀.trans hD
  have hD0 : 0 < D := zero_lt_one.trans_le h1D
  have hsplit :
      ∫ t in (1 : ℝ)..D, |moebiusSum t| / t =
        (∫ t in (1 : ℝ)..t₀, |moebiusSum t| / t) + ∫ t in t₀..D, |moebiusSum t| / t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_abs_moebiusSum_div 1 t₀)
      (intervalIntegrable_abs_moebiusSum_div t₀ D)).symm
  have htail : ∫ t in t₀..D, |moebiusSum t| / t ≤ ∫ t in t₀..D, ε t := by
    refine intervalIntegral.integral_mono_on hD
      (intervalIntegrable_abs_moebiusSum_div t₀ D) hε fun t ht ↦ ?_
    have ht0 : 0 < t := zero_lt_one.trans_le (ht₀.trans ht.1)
    exact (div_le_iff₀ ht0).mpr (hM t ht)
  have hM_D : |moebiusSum D| / D ≤ ε D :=
    (div_le_iff₀ hD0).mpr (hM D ⟨hD, le_rfl⟩)
  refine (abs_moebiusDivSum_le_elMarraki h1D).trans ?_
  rw [hsplit]
  gcongr

end TauCeti
