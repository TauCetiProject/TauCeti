/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Van der Corput's inequality and correlation lemma

* `TauCeti.vanDerCorput_inequality`: bounds `H² ‖∑_{n < N} b n‖²` in terms of `∑_{n < N} ‖b n‖²`
  and the positive-lag correlations `∑_{n < N - h} b (n + h) conj (b n)` (`1 ≤ h < H`).
* `TauCeti.tendsto_cesaro_zero_of_forall_correlation`: if `b : ℕ → ℂ` is bounded and all its
  positive-lag correlation averages tend to `0`, then the Cesàro averages of `b` tend to `0`.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Lemma 1.1.6, Corollary 1.1.7).
-/

public section

open Filter Finset Topology

namespace TauCeti

/-- Shifted-sum identity for van der Corput's inequality. -/
private theorem vanDerCorput_sum_shift {N H : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H) (b : ℕ → ℂ) :
    ∑ m ∈ range (N + H - 1),
        ∑ h ∈ range H, (if h ≤ m then (if m - h < N then b (m - h) else 0) else 0) =
      (H : ℂ) * ∑ n ∈ range N, b n := by
  rw [sum_comm]; refine (sum_congr rfl (g := fun _ ↦ ∑ n ∈ range N, b n) fun h hh ↦ ?_).trans
    (by simp [nsmul_eq_mul])
  have hhH : h < H := mem_range.mp hh
  rw [← sum_range_add_sum_Ico _ (by omega : h ≤ N + H - 1),
    sum_eq_zero fun m hm ↦ by simp [(mem_range.mp hm).not_ge], zero_add, sum_Ico_eq_sum_range,
    ← sum_range_add_sum_Ico _ (by omega : N ≤ N + H - 1 - h),
    sum_eq_zero (s := Ico N (N + H - 1 - h)) fun n hn ↦ by simp [not_lt.mpr (mem_Ico.mp hn).1],
    add_zero]
  exact sum_congr rfl fun n hn ↦ by simp [mem_range.mp hn]

/-- Inner correlation identity for two shifts `h₁ ≤ h₂ < H` in van der Corput's inequality. -/
private theorem vanDerCorput_inner_corr {N H : ℕ} (hN : 1 ≤ N) (b : ℕ → ℂ)
    {h₁ h₂ : ℕ} (h12 : h₁ ≤ h₂) (h2H : h₂ < H) :
    ∑ m ∈ range (N + H - 1),
        (if h₁ ≤ m then (if m - h₁ < N then b (m - h₁) else 0) else 0) *
          starRingEnd ℂ (if h₂ ≤ m then (if m - h₂ < N then b (m - h₂) else 0) else 0) =
      ∑ n ∈ range (N - (h₂ - h₁)), b (n + (h₂ - h₁)) * starRingEnd ℂ (b n) := by
  rw [← sum_range_add_sum_Ico _ (by omega : h₂ ≤ N + H - 1),
    sum_eq_zero fun m hm ↦ by simp [(mem_range.mp hm).not_ge], zero_add, sum_Ico_eq_sum_range,
    ← sum_range_add_sum_Ico _ (by omega : N - (h₂ - h₁) ≤ N + H - 1 - h₂),
    sum_eq_zero (s := Ico (N - (h₂ - h₁)) (N + H - 1 - h₂)) fun n hn ↦ by
      have hge := (mem_Ico.mp hn).1
      rw [ite_eq_right_iff.mpr fun _ ↦ ite_eq_right_iff.mpr fun _ ↦ False.elim (by omega),
        zero_mul],
    add_zero]
  refine sum_congr rfl fun n hn ↦ ?_; have hlt := mem_range.mp hn
  simp [(by omega : h₂ + n - h₁ = n + (h₂ - h₁)), (by omega : n + (h₂ - h₁) < N),
    (by omega : n < N), (by omega : h₁ ≤ h₂ + n)]

/-- Expanding the squared norm sum of the shifted window sums in van der Corput's inequality. -/
private theorem vanDerCorput_expand_sq {N H : ℕ} (hN : 1 ≤ N) (b : ℕ → ℂ) :
    ∑ m ∈ range (N + H - 1),
        ‖∑ h ∈ range H, (if h ≤ m then (if m - h < N then b (m - h) else 0) else 0)‖ ^ 2 ≤
      (H : ℝ) * ∑ n ∈ range N, ‖b n‖ ^ 2 +
        2 * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
          ‖∑ n ∈ range (N - h), b (n + h) * starRingEnd ℂ (b n)‖ := by
  let a : ℕ → ℕ → ℂ := fun m h ↦ if h ≤ m then (if m - h < N then b (m - h) else 0) else 0
  let S : ℕ → ℕ → ℂ := fun h₁ h₂ ↦ ∑ m ∈ range (N + H - 1), a m h₁ * starRingEnd ℂ (a m h₂)
  let C : ℕ → ℂ := fun h ↦ ∑ n ∈ range (N - h), b (n + h) * starRingEnd ℂ (b n)
  have hexpand : ((∑ m ∈ range (N + H - 1), ‖∑ h ∈ range H, a m h‖ ^ 2 : ℝ) : ℂ) =
      ∑ h₁ ∈ range H, ∑ h₂ ∈ range H, S h₁ h₂ := by
    have hcm (m : ℕ) : ((‖∑ h ∈ range H, a m h‖ ^ 2 : ℝ) : ℂ) =
        ∑ h₁ ∈ range H, ∑ h₂ ∈ range H, a m h₁ * starRingEnd ℂ (a m h₂) := by
      push_cast; rw [← Complex.mul_conj', map_sum, sum_mul]
      exact sum_congr rfl fun _ _ ↦ mul_sum _ _ _
    rw [Complex.ofReal_sum]; simp_rw [hcm]; rw [sum_comm]; exact sum_congr rfl fun _ _ ↦ sum_comm
  have hsplit := sum_range_hermitian_split H S fun h₁ h₂ ↦ by
    simp only [S, map_sum, map_mul, starRingEnd_self_apply, mul_comm, Complex.star_def]
  have hdiag : (∑ h₁ ∈ range H, S h₁ h₁).re = (H : ℝ) * ∑ n ∈ range N, ‖b n‖ ^ 2 := by
    rw [sum_congr rfl fun h₁ hh₁ ↦ (by
        simpa only [S, a, Nat.sub_self, Nat.sub_zero, add_zero, Complex.mul_conj',
          Complex.ofReal_sum, Complex.ofReal_pow] using
          vanDerCorput_inner_corr hN b le_rfl (mem_range.mp hh₁) :
        S h₁ h₁ = ((∑ n ∈ range N, ‖b n‖ ^ 2 : ℝ) : ℂ)),
      sum_const, card_range, nsmul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hoff : (∑ h₁ ∈ range H, ∑ h₂ ∈ Ico (h₁ + 1) H, (S h₁ h₂ + star (S h₁ h₂))).re ≤
      2 * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) * ‖C h‖ := by
    rw [(by rw [← sum_range_sum_Ico_sub H (fun h ↦ C h + star (C h))]
            refine sum_congr rfl fun h₁ _ ↦ sum_congr rfl fun h₂ hh₂ ↦ ?_
            dsimp only [S, a, C]
            rw [vanDerCorput_inner_corr hN b (by have := (mem_Ico.mp hh₂).1; omega)
              (mem_Ico.mp hh₂).2] :
        ∑ h₁ ∈ range H, ∑ h₂ ∈ Ico (h₁ + 1) H, (S h₁ h₂ + star (S h₁ h₂)) =
          ∑ h ∈ Ico 1 H, (H - h) • (C h + star (C h))), Complex.re_sum, mul_sum]
    refine sum_le_sum fun h _ ↦ ?_
    simp only [nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
      sub_zero, Complex.add_re, Complex.star_def, Complex.conj_re]
    nlinarith [Complex.re_le_norm (C h), Nat.cast_nonneg (α := ℝ) (H - h)]
  have hre := congrArg Complex.re (hexpand.trans hsplit)
  rw [Complex.ofReal_re, Complex.add_re, hdiag] at hre; linarith

/-- **Van der Corput's finite lag inequality**: for any `N H : ℕ` and any complex sequence
`b : ℕ → ℂ`,
`H² ‖∑_{n < N} b n‖² ≤ (N + H - 1) (H ∑_{n < N} ‖b n‖² + 2 ∑_{1 ≤ h < H} (H - h) ‖C(h)‖)`,
where `C(h) = ∑_{n < N - h} b (n + h) conj (b n)`. -/
theorem vanDerCorput_inequality (N H : ℕ) (b : ℕ → ℂ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ range N, b n‖ ^ 2 ≤
      ((N + H - 1 : ℕ) : ℝ) *
        ((H : ℝ) * ∑ n ∈ range N, ‖b n‖ ^ 2 +
          2 * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
            ‖∑ n ∈ range (N - h), b (n + h) * starRingEnd ℂ (b n)‖) := by
  rcases eq_or_ne H 0 with rfl | hH0; · simp
  rcases eq_or_ne N 0 with rfl | hN0; · simp
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  let c : ℕ → ℂ := fun m ↦
    ∑ h ∈ range H, (if h ≤ m then (if m - h < N then b (m - h) else 0) else 0)
  have hnorm : (H : ℝ) * ‖∑ n ∈ range N, b n‖ ≤ ∑ m ∈ range (N + H - 1), ‖c m‖ := by
    rw [← Complex.norm_natCast, ← norm_mul,
      ← vanDerCorput_sum_shift hN (Nat.one_le_iff_ne_zero.mpr hH0) b]; exact norm_sum_le _ _
  have hCS : (H : ℝ) ^ 2 * ‖∑ n ∈ range N, b n‖ ^ 2 ≤
      ((N + H - 1 : ℕ) : ℝ) * ∑ m ∈ range (N + H - 1), ‖c m‖ ^ 2 := by
    rw [← mul_pow]
    exact (pow_le_pow_left₀ (by positivity) hnorm 2).trans (by
      simpa using sum_mul_sq_le_sq_mul_sq (range (N + H - 1)) (fun _ ↦ (1 : ℝ)) (fun m ↦ ‖c m‖))
  exact hCS.trans (mul_le_mul_of_nonneg_left (vanDerCorput_expand_sq hN b) (Nat.cast_nonneg _))

/-- Truncating a bounded lag-`h` correlation sum keeps its normalized norm tending to `0`. -/
private theorem tendsto_vanDerCorput_lag {b : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖b n‖ ≤ C) {h : ℕ}
    (hcorr : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦
        ‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := (norm_nonneg (b 0)).trans (hC 0)
  have hfull : Tendsto (fun n : ℕ ↦
      ‖∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    by simpa only [norm_mul, norm_inv, Complex.norm_natCast, norm_zero, inv_mul_eq_div] using
      hcorr.norm.congr fun n ↦ by rw [inv_mul_eq_div, norm_div, Complex.norm_natCast]
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_ (by
    simpa only [mul_zero, add_zero] using hfull.add (hinv.const_mul ((h : ℝ) * C ^ 2)))
  filter_upwards [eventually_ge_atTop h] with n hn
  have hdiff_le : ‖∑ i ∈ Ico (n + 1 - h) (n + 1), b (i + h) * starRingEnd ℂ (b i)‖ ≤
      (h : ℝ) * C ^ 2 := by
    refine (norm_sum_le _ _).trans ((sum_le_sum (g := fun _ ↦ C ^ 2) fun i _ ↦ ?_).trans
      (by simp [(by omega : n + 1 - (n + 1 - h) = h)]))
    rw [norm_mul, Complex.norm_conj, sq]; exact mul_le_mul (hC _) (hC _) (norm_nonneg _) hC0
  rw [(by rw [← sum_range_add_sum_Ico _ (by omega : n + 1 - h ≤ n + 1), add_sub_cancel_right] :
    ∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i) =
      (∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)) -
        ∑ i ∈ Ico (n + 1 - h) (n + 1), b (i + h) * starRingEnd ℂ (b i)),
    ← div_eq_mul_inv, ← add_div]
  gcongr; exact (norm_sub_le _ _).trans (by gcongr)

/-- Normalized form of van der Corput's inequality for a `C`-bounded sequence `b : ℕ → ℂ`. -/
private theorem vanDerCorput_avg_sq_le {b : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖b n‖ ≤ C)
    {H : ℕ} (hH : 0 < H) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), b i‖ ^ 2 ≤
      (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * (C ^ 2 / (H : ℝ) + (2 / (H : ℝ) ^ 2) *
        ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
          (‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ))) := by
  have hHreal : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hsumC : ∑ i ∈ range (n + 1), ‖b i‖ ^ 2 ≤ ((n + 1 : ℕ) : ℝ) * C ^ 2 :=
    (sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hC i) 2).trans (by simp)
  rw [(by rw [norm_mul, norm_inv, Complex.norm_natCast]; field_simp [hHreal.ne'] :
    ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), b i‖ ^ 2 =
      ((H : ℝ) ^ 2 * ‖∑ i ∈ range (n + 1), b i‖ ^ 2) / ((H : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2)),
    div_le_iff₀ (by positivity : (0 : ℝ) < (H : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2)]
  refine (vanDerCorput_inequality (n + 1) H b).trans ?_
  refine (mul_le_mul_of_nonneg_left (add_le_add
    ((mul_le_mul_of_nonneg_left hsumC hHreal.le).trans_eq (mul_assoc _ _ _).symm) le_rfl)
    (Nat.cast_nonneg _)).trans_eq ?_
  simp_rw [mul_div_assoc', ← sum_div]; field_simp [hHreal.ne', hn1]

/-- **Van der Corput's lemma for bounded complex sequences**: if `b : ℕ → ℂ` is bounded and all
its positive-lag correlation averages `n ↦ (n + 1)⁻¹ ∑_{i ≤ n} b (i + h) conj (b i)` tend to `0`,
then the Cesàro averages of `b` tend to `0`. -/
theorem tendsto_cesaro_zero_of_forall_correlation {b : ℕ → ℂ} (hb : ∃ C : ℝ, ∀ n, ‖b n‖ ≤ C)
    (hcorr : ∀ h : ℕ, 0 < h →
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
          ∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i))
        atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), b i) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hb; rw [Metric.tendsto_atTop]; intro ε hε
  obtain ⟨H₀, hH₀⟩ := exists_nat_gt (2 * C ^ 2 / ε ^ 2); set H : ℕ := H₀ + 1
  have hHpos : 0 < H := Nat.succ_pos H₀
  have hHreal : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hHpos
  have hCH : C ^ 2 / (H : ℝ) < ε ^ 2 := by
    rw [div_lt_iff₀ hHreal]
    nlinarith [(div_lt_iff₀ (sq_pos_of_pos hε)).mp
      (hH₀.trans (Nat.cast_lt.mpr (Nat.lt_succ_self H₀))), sq_nonneg C]
  have hratio : Tendsto (fun n : ℕ ↦ (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
    have hlim : Tendsto (fun n : ℕ ↦ ((H : ℝ) + 1 * (n : ℝ)) / (1 + 1 * (n : ℝ))) atTop (𝓝 1) := by
      simpa using tendsto_add_mul_div_add_mul_atTop_nhds (H : ℝ) 1 1 (one_ne_zero : (1 : ℝ) ≠ 0)
    refine hlim.congr fun n ↦ ?_
    rw [(by omega : n + 1 + H - 1 = H + n)]; push_cast; ring_nf
  have hsum0 : Tendsto (fun n : ℕ ↦ ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
      (‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    rw [← sum_const_zero (s := Ico 1 H)]
    exact tendsto_finsetSum (Ico 1 H) fun h hh ↦ by simpa only [mul_zero] using
      (tendsto_vanDerCorput_lag hC (hcorr h (mem_Ico.mp hh).1)).const_mul ((H - h : ℕ) : ℝ)
  have hrhs : Tendsto (fun n : ℕ ↦
      (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * (C ^ 2 / (H : ℝ) +
        (2 / (H : ℝ) ^ 2) * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
          (‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (C ^ 2 / (H : ℝ))) := by
    simpa using hratio.mul (tendsto_const_nhds.add (hsum0.const_mul (2 / (H : ℝ) ^ 2)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrhs.eventually (gt_mem_nhds hCH))
  exact ⟨N, fun n hn ↦ by
    rw [dist_zero_right]
    nlinarith [(vanDerCorput_avg_sq_le hC hHpos n).trans_lt (hN n hn),
      norm_nonneg (((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), b i)]⟩

end TauCeti
