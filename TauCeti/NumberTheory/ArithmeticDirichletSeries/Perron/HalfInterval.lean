/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Formula
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.NumberTheory.LSeries.Continuity
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.VonMangoldt

/-!
# Truncated Perron bounds on half intervals

For coefficients dominated by the von Mangoldt function, truncating the Perron integral for
`(k/2, k]` on the line `c = 1 + 1/log k` incurs an error of order `k log² k / T + log k`.
The two endpoints use the same line of integration, so their kernels can be subtracted before
shifting the contour. The `log k` term covers the possible half weights at the endpoints.

The split into indices near and far from a cutoff is the finite Perron argument of
Davenport, *Multiplicative Number Theory*, Chapter 17.
-/

public section

namespace TauCeti

open Complex Finset ArithmeticFunction
open scoped Real LSeries.notation

private theorem sum_inv_half_grid_le (m : ℕ) :
    ∑ n ∈ Icc 1 m, (((m - 2 * n : ℕ) : ℝ)⁻¹ + ((2 * n - m : ℕ) : ℝ)⁻¹)
      ≤ 2 * (1 + Real.log m) := by
  have h (d : ℕ → ℕ) (hd : ∀ n ∈ Icc 1 m, d n ≤ m)
      (hi : Set.InjOn d ↑((Icc 1 m).filter (fun n ↦ 0 < d n))) :
      (∑ n ∈ Icc 1 m, (d n : ℝ)⁻¹) ≤ 1 + Real.log m := by
    rw [← sum_filter_add_sum_filter_not _ (fun n ↦ 0 < d n)]
    have hz : (∑ n ∈ (Icc 1 m).filter (fun n ↦ ¬0 < d n), (d n : ℝ)⁻¹) = 0 := by
      apply sum_eq_zero
      intro n hn
      simp [Nat.eq_zero_of_not_pos (mem_filter.mp hn).2]
    rw [hz, add_zero, ← sum_image (f := fun j : ℕ ↦ (j : ℝ)⁻¹) hi]
    refine (sum_le_sum_of_subset_of_nonneg (t := Icc 1 m) ?_ (fun n _ _ ↦ by positivity)).trans ?_
    · intro j hj
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hj
      exact mem_Icc.mpr ⟨(mem_filter.mp hn).2, hd n (mem_filter.mp hn).1⟩
    · simpa only [harmonic_eq_sum_Icc (n := m), Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log m
  rw [sum_add_distrib, two_mul]
  apply add_le_add
  · apply h (fun n ↦ m - 2 * n) (fun n _ ↦ Nat.sub_le ..)
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
    dsimp only at hab
    omega
  · apply h (fun n ↦ 2 * n - m) (fun n hn ↦ by have := (mem_Icc.mp hn).2; omega)
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
    dsimp only at hab
    omega

private theorem half_grid_log_inv_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m) :
    |Real.log ((m : ℝ) / 2 / n)|⁻¹ ≤
      2 * m * (((m - 2 * n : ℕ) : ℝ)⁻¹ + ((2 * n - m : ℕ) : ℝ)⁻¹) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  rcases lt_trichotomy m (2 * n) with h | h | h
  · have h' : (m : ℝ) < 2 * n := by exact_mod_cast h
    have hratio : 0 < (m : ℝ) / 2 / n := by positivity
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hlt : (m : ℝ) / 2 / n < 1 := (div_lt_one hn').mpr (by linarith)
    rw [abs_of_neg (Real.log_neg hratio hlt), Nat.sub_eq_zero_of_le h.le, Nat.cast_zero,
      inv_zero, zero_add, Nat.cast_sub h.le, Nat.cast_mul, Nat.cast_two]
    refine (inv_anti₀ (b := (2 * (n : ℝ) - m) / (2 * n)) (by positivity) ?_).trans ?_
    · rw [div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))]
      have hh : (Real.log ((m : ℝ) / 2 / n) + 1) * n ≤ (m : ℝ) / 2 :=
        (le_div_iff₀ hn').mp (by linarith)
      nlinarith only [hh]
    · rw [inv_div, div_eq_mul_inv]
      gcongr
  · simp [h, hn'.ne']
  · have h' : 2 * (n : ℝ) < m := by exact_mod_cast h
    have hratio : 0 < (m : ℝ) / 2 / n := by positivity
    have hlt : 1 < (m : ℝ) / 2 / n := (one_lt_div hn').mpr (by linarith)
    rw [abs_of_pos (Real.log_pos hlt), Nat.sub_eq_zero_of_le h.le, Nat.cast_zero,
      inv_zero, add_zero, Nat.cast_sub h.le, Nat.cast_mul, Nat.cast_two]
    refine (inv_anti₀ (b := ((m : ℝ) - 2 * n) / m) (by positivity) ?_).trans ?_
    · have hh := Real.one_sub_inv_le_log_of_pos hratio
      convert hh using 1
      field_simp
    · rw [inv_div, div_eq_mul_inv]
      gcongr
      linarith

private theorem perron_error_near_le {m n : ℕ} {c T : ℝ} (hm : 0 < m)
    (hn : 0 < n) (hnm : n ≤ m) (hl : (m : ℝ) / 4 ≤ n) (hc : 0 ≤ c) (hT : 0 < T) :
    Λ n * (((m : ℝ) / 2 / n) ^ c / (π * T * |Real.log ((m : ℝ) / 2 / n)|)) ≤
      (Real.log m * 2 ^ c * (2 * m) / (π * T)) *
        (((m - 2 * n : ℕ) : ℝ)⁻¹ + ((2 * n - m : ℕ) : ℝ)⁻¹) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hRatio : (m : ℝ) / 2 / n ≤ 2 := (div_le_iff₀ hn').mpr (by linarith)
  have hlog := vonMangoldt_le_log (n := n) |>.trans
    (Real.log_le_log hn' (Nat.cast_le.mpr hnm))
  have hpow := Real.rpow_le_rpow (by positivity) hRatio hc
  have hinv := half_grid_log_inv_le hm hn hnm
  rw [← div_div, div_eq_mul_inv (_ / _)]
  calc
    _ ≤ Real.log m * (2 ^ c / (π * T) *
          (2 * m * (((m - 2 * n : ℕ) : ℝ)⁻¹ + ((2 * n - m : ℕ) : ℝ)⁻¹))) := by gcongr
    _ = _ := by ring

/-- Outside the central range, `|log (x/n)| ≥ log 2`, so the original Dirichlet series
majorizes the error. -/
private theorem perron_error_far_le {x c T : ℝ} (hx : 0 < x) (hT : 0 < T) {n : ℕ}
    (hn : 0 < n) (h : (n : ℝ) < x / 2 ∨ 2 * x < n) :
    Λ n * ((x / n) ^ c / (π * T * |Real.log (x / n)|)) ≤
      x ^ c / (π * T * Real.log 2) * ‖LSeries.term (↗Λ) (c : ℂ) n‖ := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : Real.log 2 ≤ |Real.log (x / n)| := by
    rcases h with h | h
    · exact (Real.log_le_log two_pos ((le_div_iff₀ hn').mpr (by linarith))).trans (le_abs_self _)
    · have hlog := Real.log_le_log (div_pos hx hn') (show x / n ≤ 2⁻¹ by
        rw [div_le_iff₀ hn']; linarith)
      rw [Real.log_inv] at hlog
      exact (neg_neg (Real.log 2) ▸ (neg_le_neg hlog)).trans (neg_le_abs _)
  calc
    _ ≤ Λ n * ((x / n) ^ c / (π * T * Real.log 2)) := by gcongr
    _ = _ := by
      simp only [LSeries.norm_term_eq, hn.ne', ite_false, ofReal_re, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (vonMangoldt_nonneg : 0 ≤ Λ n), Real.div_rpow hx.le hn'.le]
      ring

private theorem perron_error_series_le {m : ℕ} (hm : 0 < m) {c T : ℝ} (hc : 1 < c)
    (hT : 0 < T) {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ Λ n) :
    (∑' n : ℕ, ‖f n‖ * (((m : ℝ) / 2 / n) ^ c /
        (π * T * |Real.log ((m : ℝ) / 2 / n)|))) ≤
      ((m : ℝ) / 2) ^ c / (π * T * Real.log 2) *
        (-(logDeriv riemannZeta (c : ℂ)).re) +
        (Real.log m * 2 ^ c * (2 * m) / (π * T)) * (2 * (1 + Real.log m)) := by
  have hc' : 1 < (c : ℂ).re := by simpa using hc
  let A := ((m : ℝ) / 2) ^ c / (π * T * Real.log 2)
  let B := Real.log m * 2 ^ c * (2 * m) / (π * T)
  let w (n : ℕ) := ‖LSeries.term (↗Λ) (c : ℂ) n‖
  let v (n : ℕ) := if n ∈ Icc 1 m then
      (((m - 2 * n : ℕ) : ℝ)⁻¹ + ((2 * n - m : ℕ) : ℝ)⁻¹) else 0
  have hw := (LSeriesSummable_vonMangoldt hc').norm
  have hv0 : ∀ n ∉ Icc 1 m, v n = 0 := fun n hn ↦ ite_eq_right hn
  have hv : Summable v := summable_of_ne_finset_zero hv0
  have hdom (n : ℕ) : ‖f n‖ * (((m : ℝ) / 2 / n) ^ c /
      (π * T * |Real.log ((m : ℝ) / 2 / n)|)) ≤ A * w n + B * v n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [w, v]
    by_cases hnear : n ≤ m ∧ (m : ℝ) / 4 ≤ n
    · have hvn : n ∈ Icc 1 m := mem_Icc.mpr ⟨hn, hnear.1⟩
      refine (mul_le_mul_of_nonneg_right (hf n) (by positivity)).trans ?_
      refine (perron_error_near_le hm hn hnear.1 hnear.2 (zero_le_one.trans hc.le) hT).trans ?_
      simp only [B, v, ite_eq_left hvn]
      apply le_add_of_nonneg_left
      dsimp [A, w]; positivity
    · have hfar : (n : ℝ) < ((m : ℝ) / 2) / 2 ∨ 2 * ((m : ℝ) / 2) < n := by
        by_cases hnm : n ≤ m
        · left; linarith [lt_of_not_ge (fun hh ↦ hnear ⟨hnm, hh⟩)]
        · have hh : (m : ℝ) < n := Nat.cast_lt.mpr (lt_of_not_ge hnm)
          right; linarith
      refine (mul_le_mul_of_nonneg_right (hf n) (by positivity)).trans ?_
      exact (perron_error_far_le (by positivity) hT hn hfar).trans
        (le_add_of_nonneg_right (by dsimp [B, v]; split_ifs <;> positivity))
  have hmajor : Summable (fun n ↦ A * w n + B * v n) := (hw.mul_left A).add (hv.mul_left B)
  refine (Summable.tsum_le_tsum hdom (Summable.of_nonneg_of_le (fun _ ↦ by positivity) hdom hmajor)
    hmajor).trans ?_
  rw [(hw.mul_left A).tsum_add (hv.mul_left B), tsum_mul_left, tsum_mul_left]
  have hwval : ∑' n, w n = -(logDeriv riemannZeta (c : ℂ)).re :=
    (TauCeti.LSeries.hasSum_norm_term_vonMangoldt hc).tsum_eq
  rw [hwval]
  gcongr
  rw [tsum_eq_sum hv0]
  simp only [v]
  exact (sum_congr rfl fun n hn ↦ ite_eq_left hn).le.trans (sum_inv_half_grid_le m)

/-- Truncated Perron at a positive half-integer for coefficients bounded by von Mangoldt. The
`log(max 1 (m/2))/2` term pays for the integer endpoint, if there is one. -/
theorem norm_truncatedPerron_sub_tsum_step_halfNat_le {m : ℕ} (hm : 0 < m) {c T : ℝ}
    (hc : 1 < c) (hT : 0 < T) {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ Λ n) :
    let x : ℝ := m / 2
    ‖(((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t)
        - ∑' n : ℕ, f n * perronStep (x / n)‖ ≤
      x ^ c / (π * T * Real.log 2) * (-(logDeriv riemannZeta (c : ℂ)).re) +
        Real.log m * 2 ^ c * (2 * m) / (π * T) * (2 * (1 + Real.log m)) +
        Real.log (max 1 x) / 2 := by
  intro x
  have hx : 0 < x := by dsimp [x]; positivity
  have hc' : 1 < (c : ℂ).re := by simpa using hc
  have hF : LSeriesSummable f (c : ℂ) :=
    .of_norm <| Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ LSeries.norm_term_le _ (by
        simpa only [norm_real, Real.norm_of_nonneg vonMangoldt_nonneg] using hf n))
      (LSeriesSummable_vonMangoldt hc').norm
  refine (norm_truncatedPerron_LSeries_sub_tsum_step_le hx (zero_lt_one.trans hc) hT hF).trans ?_
  apply add_le_add (perron_error_series_le hm hc hT hf)
  split_ifs with h
  · refine div_le_div_of_nonneg_right ((hf _).trans (vonMangoldt_le_log.trans ?_)) (by norm_num)
    rw [← h]
    exact Real.log_le_log hx (le_max_right ..)
  · exact div_nonneg (Real.log_nonneg (le_max_left ..)) (by norm_num)

private theorem log_scale_of_four_le {k : ℕ} (hk : 4 ≤ k) : 1 ≤ Real.log (k : ℝ) := by
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  exact (by linarith [Real.log_two_gt_d9] : 1 ≤ Real.log 4).trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hk))

private theorem half_grid_bound_at_perron_line {D T : ℝ} (hD : 0 ≤ D) (hT : 0 < T)
    {k m : ℕ} (hk : 4 ≤ k) (hm₀ : 0 < m) (hm : m ≤ 2 * k)
    (hζ : -(logDeriv riemannZeta (1 + ((Real.log k)⁻¹ : ℝ) : ℂ)).re ≤ Real.log k + D) :
    let c := 1 + (Real.log k)⁻¹
    let x : ℝ := m / 2
    x ^ c / (π * T * Real.log 2) * (-(logDeriv riemannZeta (c : ℂ)).re) +
        Real.log m * 2 ^ c * (2 * m) / (π * T) * (2 * (1 + Real.log m)) +
        Real.log (max 1 x) / 2 ≤
      (Real.exp 1 * (1 + D) / (π * Real.log 2) + 192 / π) * k * (Real.log k) ^ 2 / T +
        Real.log k / 2 := by
  intro c x
  have hl := log_scale_of_four_le hk
  have hl' := zero_lt_one.trans_le hl
  have hk₄ : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk' : (0 : ℝ) < k := by linarith
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm₀
  have hm'' : (m : ℝ) ≤ 2 * k := by exact_mod_cast hm
  have hlogm : Real.log m ≤ 2 * Real.log k := by
    have h := Real.log_le_log hm' hm''
    rw [Real.log_mul two_ne_zero hk'.ne'] at h
    linarith [Real.log_le_log two_pos (by linarith : (2 : ℝ) ≤ k)]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc₂ : c ≤ 2 := by linarith [inv_le_one_of_one_le₀ hl]
  have hx : 0 < x := by dsimp [x]; positivity
  have hxk : x ≤ k := by dsimp [x]; linarith
  have hpow : x ^ c ≤ (k : ℝ) * Real.exp 1 := by
    refine (Real.rpow_le_rpow hx.le hxk hc).trans_eq ?_
    dsimp only [c]
    rw [Real.rpow_add hk', Real.rpow_one, Real.rpow_def_of_pos hk',
      mul_inv_cancel₀ hl'.ne']
  have hc₁ : 1 < c := lt_add_of_pos_right _ (inv_pos.mpr hl')
  have hneg : 0 ≤ -(logDeriv riemannZeta (c : ℂ)).re := by
    rw [← (TauCeti.LSeries.hasSum_norm_term_vonMangoldt hc₁).tsum_eq]
    exact tsum_nonneg (fun _ ↦ norm_nonneg _)
  have hζ' : -(logDeriv riemannZeta (c : ℂ)).re ≤ (1 + D) * (Real.log k) ^ 2 := by
    have h : -(logDeriv riemannZeta (c : ℂ)).re ≤ Real.log k + D := by
      simpa only [c, ofReal_add, ofReal_one] using hζ
    have hs : Real.log k ≤ (Real.log k) ^ 2 := by nlinarith
    nlinarith only [h, hs, mul_nonneg hD (show 0 ≤ (Real.log k)^2 - 1 by nlinarith)]
  have htwo : (2 : ℝ) ^ c ≤ 4 := by
    simpa only [Real.rpow_two, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc₂
  have hsum : 1 + Real.log m ≤ 3 * Real.log k := by linarith
  have hmax : max 1 x ≤ k := max_le (by linarith) hxk
  calc
    _ ≤ ((k : ℝ) * Real.exp 1) / (π * T * Real.log 2) * ((1 + D) * (Real.log k) ^ 2) +
          (2 * Real.log k) * 4 * (2 * (2 * k)) / (π * T) * (2 * (3 * Real.log k)) +
          Real.log k / 2 := by gcongr
    _ = _ := by ring

/-- The half-weighted sum on `(k/2, k]` differs from its truncated Perron integral on
`c = 1 + 1/log k` by `O(k log² k / T) + log k`. Both cutoffs use the same line, and the
constant is independent of the coefficients provided their norms are bounded by von Mangoldt. -/
theorem exists_norm_truncatedPerron_halfInterval_sub_le :
    ∃ C > (0 : ℝ), ∀ {k : ℕ}, 4 ≤ k → ∀ {T : ℝ}, 0 < T →
      ∀ {f : ℕ → ℂ}, (∀ n, ‖f n‖ ≤ Λ n) →
      let c := 1 + (Real.log k)⁻¹
      ‖(((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) *
          (perronIntegrand k c t - perronIntegrand ((k : ℝ) / 2) c t)) -
          ∑' n : ℕ, f n * (perronStep ((k : ℝ) / n) - perronStep ((k : ℝ) / 2 / n))‖ ≤
        C * k * (Real.log k) ^ 2 / T + Real.log k := by
  obtain ⟨D, hD, hP⟩ := exists_neg_re_logDeriv_riemannZeta_one_add_le
  let A := Real.exp 1 * (1 + D) / (π * Real.log 2) + 192 / π
  refine ⟨2 * A, by dsimp [A]; positivity, ?_⟩
  intro k hk T hT f hf c
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hl := log_scale_of_four_le hk
  have hη : 0 < (Real.log k)⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hl)
  have hc : 1 < c := by dsimp [c]; linarith
  have hP' := hP hη (inv_le_one_of_one_le₀ hl)
  rw [inv_inv] at hP'
  have hEndpoint (m : ℕ) (hm₀ : 0 < m) (hm : m ≤ 2 * k) :=
    (norm_truncatedPerron_sub_tsum_step_halfNat_le hm₀ hc hT hf).trans
      (half_grid_bound_at_perron_line hD hT hk hm₀ hm hP')
  have h₁ := hEndpoint (2 * k) (by omega) le_rfl
  rw [show ((2 * k : ℕ) : ℝ) / 2 = k by push_cast; ring] at h₁
  have h₂ := hEndpoint k (by omega) (by omega)
  have hF := TauCeti.LSeries.continuous_vertical f (c : ℂ)
  have hI (x : ℝ) (hx : 0 < x) : IntervalIntegrable
      (fun t ↦ LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t) MeasureTheory.volume (-T) T :=
    (hF.mul (continuous_perronIntegrand hx.ne' (zero_lt_one.trans hc).ne')).intervalIntegrable _ _
  have hS := summable_mul_perronStep_div f
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (hI _ hk') (hI _ (by positivity)), mul_sub,
    (hS k).tsum_sub (hS ((k : ℝ) / 2))]
  convert norm_sub_le_of_le h₁ h₂ using 1
  · congr 1
    abel
  · dsimp only [A]
    ring

end TauCeti
