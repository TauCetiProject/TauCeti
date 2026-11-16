/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Equidistribution.Torus
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.Analysis.Fourier.Monomial

/-!
# Van der Corput's inequality and difference theorem

This file proves van der Corput's finite lag inequality for arbitrary complex sequences and deduces
van der Corput's difference theorem for asymptotic equidistribution on `UnitAddTorus d`.

## Main results

* `TauCeti.vanDerCorput_finite_lag_inequality`: for any complex sequence `b : ℕ → ℂ` and natural
  numbers `N H : ℕ`,
  $$H^2 \left\|\sum_{n < N} b(n)\right\|^2 \le (N + H - 1)
    \left(H \sum_{n < N} \|b(n)\|^2 + 2 \sum_{h = 1}^{H - 1} (H - h)
      \left\|\sum_{n < N - h} b(n + h)\overline{b(n)}\right\|\right).$$
* `TauCeti.vanDerCorput_difference`: if every positive lag difference `n ↦ x (n + h) - x n`
  (`h ≥ 1`) is equidistributed for Haar probability on `UnitAddTorus d`, then so is `x`.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Lemma 1.1.6 and Corollary 1.1.7).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Topology

namespace TauCeti

section FiniteLagInequality

/-- Split a symmetric double sum over `Finset.range H` into its diagonal and upper triangular
diagonals indexed by lag `h ∈ Finset.Ico 1 H`. -/
private theorem sum_range_sq_symm (f : ℕ → ℕ → ℝ) (hsym : ∀ i j, f j i = f i j) (H : ℕ) :
    ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, f i j =
      ∑ i ∈ Finset.range H, f i i +
        2 * ∑ h ∈ Finset.Ico 1 H, ∑ i ∈ Finset.range (H - h), f i (i + h) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ]
    simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih, Finset.sum_congr rfl fun i _ ↦ hsym i H]
    cases H with
    | zero => simp
    | succ H =>
      have hico : Finset.Ico 1 (H + 2) = insert (H + 1) (Finset.Ico 1 (H + 1)) := by
        ext h; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hico, Finset.sum_insert (by simp)]
      have hshift (h : ℕ) (hh : h ∈ Finset.Ico 1 (H + 1)) :
          ∑ i ∈ Finset.range (H + 2 - h), f i (i + h) =
            ∑ i ∈ Finset.range (H + 1 - h), f i (i + h) + f (H + 1 - h) (H + 1) := by
        have hh' := Finset.mem_Ico.1 hh
        rw [show H + 2 - h = (H + 1 - h) + 1 by omega, Finset.sum_range_succ,
          show H + 1 - h + h = H + 1 by omega]
      rw [Finset.sum_congr rfl hshift, Finset.sum_add_distrib]
      have hrefl : f 0 (H + 1) + ∑ h ∈ Finset.Ico 1 (H + 1), f (H + 1 - h) (H + 1) =
          ∑ i ∈ Finset.range (H + 1), f i (H + 1) := by
        rw [Finset.sum_range_succ', add_comm]
        congr 1
        refine Finset.sum_nbij (fun h ↦ H - h) (fun h hh ↦ ?_) (fun h₁ hh₁ h₂ hh₂ heq ↦ ?_)
          (fun i hi ↦ ?_) (fun h hh ↦ ?_)
        · simp only [Finset.mem_Ico, Finset.mem_range] at hh ⊢; omega
        · simp only [Finset.mem_coe, Finset.mem_Ico] at hh₁ hh₂; dsimp only at heq; omega
        · simp only [Finset.mem_coe, Finset.mem_range] at hi
          exact ⟨H - i, by simp only [Finset.mem_coe, Finset.mem_Ico]; omega, by dsimp only; omega⟩
        · simp only [Finset.mem_Ico] at hh; congr 1; omega
      rw [show H + 2 - (H + 1) = 1 by omega, Finset.sum_range_one, zero_add]
      linarith

/-- Summing a zero-padded translate of `b` over `Finset.range (N + H - 1)` recovers the partial
sum of `b` over `Finset.range N`. -/
private theorem sum_shift_eq (b : ℕ → ℂ) {N H h : ℕ} (hN : 1 ≤ N) (hh : h < H) :
    ∑ m ∈ Finset.range (N + H - 1), (if h ≤ m ∧ m < N + h then b (m - h) else 0) =
      ∑ n ∈ Finset.range N, b n := by
  have hM : h + N ≤ N + H - 1 := by omega
  rw [← Finset.sum_subset (Finset.range_mono hM)]
  · rw [Finset.sum_range_add]
    have hleft : ∑ m ∈ Finset.range h, (if h ≤ m ∧ m < N + h then b (m - h) else 0) = 0 :=
      Finset.sum_eq_zero fun m hm ↦ by simp [not_le_of_gt (Finset.mem_range.1 hm)]
    rw [hleft, zero_add]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn' : n < N := Finset.mem_range.1 hn
    simp [show h + n < N + h by omega]
  · intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    simp [show ¬ (m < N + h) by omega]

/-- Cross-correlation identity for zero-padded translates of `b` supported on `Finset.range N`. -/
private theorem sum_shift_mul_conj (b : ℕ → ℂ) {N H h₁ h₂ : ℕ} (h12 : h₁ ≤ h₂) (h2H : h₂ < H) :
    ∑ m ∈ Finset.range (N + H - 1),
        (if h₁ ≤ m ∧ m < N + h₁ then b (m - h₁) else 0) *
          starRingEnd ℂ (if h₂ ≤ m ∧ m < N + h₂ then b (m - h₂) else 0) =
      ∑ n ∈ Finset.range (N - (h₂ - h₁)), b (n + (h₂ - h₁)) * starRingEnd ℂ (b n) := by
  by_cases hN : h₂ - h₁ < N
  · have hM : h₂ + (N - (h₂ - h₁)) ≤ N + H - 1 := by omega
    rw [← Finset.sum_subset (Finset.range_mono hM)]
    · rw [Finset.sum_range_add]
      have hleft : ∑ m ∈ Finset.range h₂,
          (if h₁ ≤ m ∧ m < N + h₁ then b (m - h₁) else 0) *
            starRingEnd ℂ (if h₂ ≤ m ∧ m < N + h₂ then b (m - h₂) else 0) = 0 :=
        Finset.sum_eq_zero fun m hm ↦ by simp [not_le_of_gt (Finset.mem_range.1 hm)]
      rw [hleft, zero_add]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn' : n < N - (h₂ - h₁) := Finset.mem_range.1 hn
      simp only [show h₁ ≤ h₂ + n ∧ h₂ + n < N + h₁ by omega,
        show h₂ ≤ h₂ + n ∧ h₂ + n < N + h₂ by omega, and_self, ↓reduceIte,
        show h₂ + n - h₁ = n + (h₂ - h₁) by omega, show h₂ + n - h₂ = n by omega]
    · intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      simp [show ¬ (h₁ ≤ m ∧ m < N + h₁) by omega]
  · rw [show N - (h₂ - h₁) = 0 by omega, Finset.range_zero, Finset.sum_empty]
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    by_cases hm : h₂ ≤ m
    · simp [show ¬ (h₁ ≤ m ∧ m < N + h₁) by omega]
    · simp [hm]

/-- Expand `∑ m < M, ‖∑ h < H, c m h‖^2` into the real parts of the cross-correlations of `c`. -/
private theorem sum_norm_sq_sum_eq (c : ℕ → ℕ → ℂ) (M H : ℕ) :
    ∑ m ∈ Finset.range M, ‖∑ h ∈ Finset.range H, c m h‖ ^ 2 =
      ∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
        (∑ m ∈ Finset.range M, c m h₁ * starRingEnd ℂ (c m h₂)).re := by
  have hnorm (m : ℕ) : ‖∑ h ∈ Finset.range H, c m h‖ ^ 2 =
      ((∑ h ∈ Finset.range H, c m h) * starRingEnd ℂ (∑ h ∈ Finset.range H, c m h)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hnorm, ← Complex.re_sum]
  have hmul : ∑ m ∈ Finset.range M,
        (∑ h ∈ Finset.range H, c m h) * starRingEnd ℂ (∑ h ∈ Finset.range H, c m h) =
      ∑ h₁ ∈ Finset.range H, ∑ h₂ ∈ Finset.range H,
        ∑ m ∈ Finset.range M, c m h₁ * starRingEnd ℂ (c m h₂) := by
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  simp only [hmul, Complex.re_sum]

/-- Upper bound for the squared `ℓ²` norm of the sum of `H` zero-padded translates of `b`. -/
private theorem sum_shift_norm_sq_le (b : ℕ → ℂ) (N H : ℕ) :
    ∑ m ∈ Finset.range (N + H - 1),
        ‖∑ h ∈ Finset.range H, if h ≤ m ∧ m < N + h then b (m - h) else 0‖ ^ 2 ≤
      (H : ℝ) * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 +
        2 * ∑ h ∈ Finset.Ico 1 H, ((H - h : ℕ) : ℝ) *
          ‖∑ n ∈ Finset.range (N - h), b (n + h) * starRingEnd ℂ (b n)‖ := by
  let M : ℕ := N + H - 1
  let c (m h : ℕ) : ℂ := if h ≤ m ∧ m < N + h then b (m - h) else 0
  let S (h₁ h₂ : ℕ) : ℂ := ∑ m ∈ Finset.range M, c m h₁ * starRingEnd ℂ (c m h₂)
  have hS_symm (h₁ h₂ : ℕ) : (S h₂ h₁).re = (S h₁ h₂).re := by
    have hconj : S h₂ h₁ = starRingEnd ℂ (S h₁ h₂) := by
      simp only [S, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm]
    rw [hconj, Complex.conj_re]
  have hdiag : ∑ h₁ ∈ Finset.range H, (S h₁ h₁).re = (H : ℝ) * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 := by
    have hterm (h₁ : ℕ) (hh₁ : h₁ ∈ Finset.range H) :
        (S h₁ h₁).re = ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 := by
      have hcorr : S h₁ h₁ = ∑ n ∈ Finset.range N, b n * starRingEnd ℂ (b n) := by
        simpa only [Nat.sub_self, Nat.sub_zero, add_zero] using
          sum_shift_mul_conj b (N := N) le_rfl (Finset.mem_range.1 hh₁)
      rw [hcorr, Complex.re_sum]
      exact Finset.sum_congr rfl fun n _ ↦ by
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [sum_norm_sq_sum_eq c M H, sum_range_sq_symm (fun h₁ h₂ ↦ (S h₁ h₂).re) hS_symm, hdiag]
  gcongr with h hh
  have hh' := Finset.mem_Ico.1 hh
  calc ∑ i ∈ Finset.range (H - h), (S i (i + h)).re
      ≤ ∑ _i ∈ Finset.range (H - h),
          ‖∑ n ∈ Finset.range (N - h), b (n + h) * starRingEnd ℂ (b n)‖ := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : i < H - h := Finset.mem_range.1 hi
        have hraw := sum_shift_mul_conj b (N := N) (Nat.le_add_right i h) (by omega : i + h < H)
        rw [show i + h - i = h by omega] at hraw
        dsimp only [S, c, M]
        rw [hraw]
        exact Complex.re_le_norm _
    _ = ((H - h : ℕ) : ℝ) * ‖∑ n ∈ Finset.range (N - h), b (n + h) * starRingEnd ℂ (b n)‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Van der Corput's finite lag inequality.** For any complex sequence `b : ℕ → ℂ` and natural
numbers `N H : ℕ`, the squared modulus of the partial sum `∑ n < N, b n` is controlled by the
`L²` mass and positive lag correlations up to lag `H - 1`. -/
theorem vanDerCorput_finite_lag_inequality (b : ℕ → ℂ) (N H : ℕ) :
    ((H : ℝ) ^ 2) * ‖∑ n ∈ Finset.range N, b n‖ ^ 2 ≤
      ((N + H - 1 : ℕ) : ℝ) * ((H : ℝ) * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 +
        2 * ∑ h ∈ Finset.Ico 1 H, ((H - h : ℕ) : ℝ) *
          ‖∑ n ∈ Finset.range (N - h), b (n + h) * starRingEnd ℂ (b n)‖) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  let M : ℕ := N + H - 1
  let g (m : ℕ) : ℂ := ∑ h ∈ Finset.range H, if h ≤ m ∧ m < N + h then b (m - h) else 0
  have hsum_g : ∑ m ∈ Finset.range M, g m = (H : ℂ) * ∑ n ∈ Finset.range N, b n := by
    simp only [g]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun h hh ↦ sum_shift_eq b hN (Finset.mem_range.1 hh),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : (H : ℝ) * ‖∑ n ∈ Finset.range N, b n‖ ≤ ∑ m ∈ Finset.range M, ‖g m‖ := by
    calc (H : ℝ) * ‖∑ n ∈ Finset.range N, b n‖
        = ‖(H : ℂ) * ∑ n ∈ Finset.range N, b n‖ := by rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ m ∈ Finset.range M, g m‖ := by rw [hsum_g]
      _ ≤ ∑ m ∈ Finset.range M, ‖g m‖ := norm_sum_le _ _
  calc ((H : ℝ) ^ 2) * ‖∑ n ∈ Finset.range N, b n‖ ^ 2
      = ((H : ℝ) * ‖∑ n ∈ Finset.range N, b n‖) ^ 2 := by ring
    _ ≤ (∑ m ∈ Finset.range M, ‖g m‖) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ ≤ ((Finset.range M).card : ℝ) * ∑ m ∈ Finset.range M, ‖g m‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = (M : ℝ) * ∑ m ∈ Finset.range M, ‖g m‖ ^ 2 := by rw [Finset.card_range]
    _ ≤ (M : ℝ) * ((H : ℝ) * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 +
          2 * ∑ h ∈ Finset.Ico 1 H, ((H - h : ℕ) : ℝ) *
            ‖∑ n ∈ Finset.range (N - h), b (n + h) * starRingEnd ℂ (b n)‖) := by
        gcongr; exact sum_shift_norm_sq_le b N H

end FiniteLagInequality

section DifferenceTheorem

variable {d : Type*} [Fintype d]

/-- Truncating the top `h` terms of a Cesàro average of a unit-norm sequence does not affect a
zero limit. -/
private theorem tendsto_norm_sum_range_sub_div_zero {f : ℕ → ℂ} (hnorm : ∀ i, ‖f i‖ = 1)
    (htend : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), f i)
      atTop (𝓝 0)) (h : ℕ) :
    Tendsto (fun n : ℕ ↦ ‖∑ i ∈ Finset.range (n + 1 - h), f i‖ / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hnorm_tend : Tendsto (fun n : ℕ ↦ ‖∑ i ∈ Finset.range (n + 1), f i‖ / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have h1 := htend.norm
    rw [norm_zero] at h1
    refine h1.congr fun n ↦ ?_
    rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  have hrem_tend : Tendsto (fun n : ℕ ↦ (h : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).const_mul (h : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_
    (by simpa using hnorm_tend.add hrem_tend)
  filter_upwards [eventually_ge_atTop h] with n hn
  have hsplit : ∑ i ∈ Finset.range (n + 1), f i =
      ∑ i ∈ Finset.range (n + 1 - h), f i + ∑ i ∈ Finset.range h, f (n + 1 - h + i) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show h ≤ n + 1 by omega)]
    exact Finset.sum_range_add f (n + 1 - h) h
  have hle : ‖∑ i ∈ Finset.range (n + 1 - h), f i‖ ≤
      ‖∑ i ∈ Finset.range (n + 1), f i‖ + (h : ℝ) := by
    rw [eq_sub_of_add_eq hsplit.symm]
    calc ‖∑ i ∈ Finset.range (n + 1), f i - ∑ i ∈ Finset.range h, f (n + 1 - h + i)‖
        ≤ ‖∑ i ∈ Finset.range (n + 1), f i‖ + ‖∑ i ∈ Finset.range h, f (n + 1 - h + i)‖ :=
          norm_sub_le _ _
      _ ≤ ‖∑ i ∈ Finset.range (n + 1), f i‖ + ∑ i ∈ Finset.range h, ‖f (n + 1 - h + i)‖ := by
          gcongr; exact norm_sum_le _ _
      _ = ‖∑ i ∈ Finset.range (n + 1), f i‖ + (h : ℝ) := by simp [hnorm]
  rw [← add_div]
  push_cast
  exact div_le_div_of_nonneg_right hle (by positivity)

/-- Normalized form of van der Corput's finite lag inequality for unit-modulus sequences. -/
private theorem vanDerCorput_unit_avg_sq_le {b : ℕ → ℂ} (hnorm : ∀ i, ‖b i‖ = 1)
    {H : ℕ} (hH : 1 ≤ H) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), b i‖ ^ 2 ≤
      (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * ((H : ℝ)⁻¹ +
        (2 / (H : ℝ) ^ 2) * ∑ h ∈ Finset.Ico 1 H, ((H - h : ℕ) : ℝ) *
          (‖∑ i ∈ Finset.range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ /
            ((n + 1 : ℕ) : ℝ))) := by
  have hHR : (0 : ℝ) < H := Nat.cast_pos.2 hH
  have hnR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hineq := vanDerCorput_finite_lag_inequality b (n + 1) H
  have hbnorm : ∑ i ∈ Finset.range (n + 1), ‖b i‖ ^ 2 = ((n + 1 : ℕ) : ℝ) := by
    simp [hnorm]
  rw [hbnorm] at hineq
  have hdiv := div_le_div_of_nonneg_right hineq (by positivity : (0 : ℝ) ≤ (H : ℝ) ^ 2 *
    ((n + 1 : ℕ) : ℝ) ^ 2)
  have hlhs : ((H : ℝ) ^ 2) * ‖∑ i ∈ Finset.range (n + 1), b i‖ ^ 2 /
      ((H : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2) =
      ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), b i‖ ^ 2 := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow]
    field_simp [hHR.ne', hnR.ne']
  have hrhs : ((n + 1 + H - 1 : ℕ) : ℝ) * ((H : ℝ) * ((n + 1 : ℕ) : ℝ) +
        2 * ∑ h ∈ Finset.Ico 1 H, ((H - h : ℕ) : ℝ) *
          ‖∑ i ∈ Finset.range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖) /
      ((H : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2) =
      (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * ((H : ℝ)⁻¹ +
        (2 / (H : ℝ) ^ 2) * ∑ h ∈ Finset.Ico 1 H, ((H - h : ℕ) : ℝ) *
          (‖∑ i ∈ Finset.range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ /
            ((n + 1 : ℕ) : ℝ))) := by
    simp_rw [← mul_div_assoc, ← Finset.sum_div]
    field_simp [hHR.ne', hnR.ne']
  rwa [hlhs, hrhs] at hdiv

/-- For `1 ≤ H`, the ratio `(n + 1 + H - 1) / (n + 1)` tends to `1` as `n → ∞`. -/
private theorem tendsto_add_sub_one_div_one {H : ℕ} (hH : 1 ≤ H) :
    Tendsto (fun n : ℕ ↦ (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have hrew (n : ℕ) : (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
      1 + ((H - 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ := by
    have hnat : ((n + 1 + H - 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + ((H - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n + 1 + H - 1 = (n + 1) + (H - 1) by omega)
    rw [hnat, add_div, div_self (by positivity), div_eq_mul_inv]
  simp_rw [hrew]
  simpa using tendsto_const_nhds.add ((tendsto_inv_atTop_zero.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).const_mul
      ((H - 1 : ℕ) : ℝ))

/-- **Van der Corput's difference theorem on `UnitAddTorus d`.** If for every positive lag `h ≥ 1`
the difference sequence `n ↦ x (n + h) - x n` is equidistributed for Haar probability, then `x` is
equidistributed for Haar probability. -/
theorem vanDerCorput_difference (x : ℕ → UnitAddTorus d)
    (hdiff : ∀ h : ℕ, 1 ≤ h →
      AsympEquidistributed (fun n ↦ x (n + h) - x n) volume.toProbabilityMeasure) :
    AsympEquidistributed x volume.toProbabilityMeasure := by
  rw [weyl_criterion]
  intro k hk
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H₀, hH₀⟩ := exists_nat_gt ((ε ^ 2)⁻¹)
  set H : ℕ := max 1 H₀
  have hH1 : 1 ≤ H := le_max_left 1 H₀
  have hHinv : (H : ℝ)⁻¹ < ε ^ 2 := (inv_lt_comm₀ (Nat.cast_pos.2 hH1) (by positivity)).2
    (lt_of_lt_of_le hH₀ (by exact_mod_cast le_max_right 1 H₀))
  let b (i : ℕ) : ℂ := UnitAddTorus.mFourier k (x i)
  have hlag (h : ℕ) (hh : h ∈ Finset.Ico 1 H) :
      Tendsto (fun n : ℕ ↦ ((H - h : ℕ) : ℝ) *
        (‖∑ i ∈ Finset.range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ /
          ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hdt := (weyl_criterion _).1 (hdiff h (Finset.mem_Ico.1 hh).1) k hk
    have hcorr := tendsto_norm_sum_range_sub_div_zero
      (fun i ↦ UnitAddTorus.norm_mFourier_apply k (x (i + h) - x i)) hdt h
    have heq (n : ℕ) : ∑ i ∈ Finset.range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i) =
        ∑ i ∈ Finset.range (n + 1 - h), UnitAddTorus.mFourier k (x (i + h) - x i) :=
      Finset.sum_congr rfl fun i _ ↦ (UnitAddTorus.mFourier_apply_sub k (x (i + h)) (x i)).symm
    simp_rw [heq]
    simpa using hcorr.const_mul ((H - h : ℕ) : ℝ)
  have hrhs_tend : Tendsto (fun n : ℕ ↦
      (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * ((H : ℝ)⁻¹ +
        (2 / (H : ℝ) ^ 2) * ∑ h ∈ Finset.Ico 1 H, ((H - h : ℕ) : ℝ) *
          (‖∑ i ∈ Finset.range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ /
            ((n + 1 : ℕ) : ℝ)))) atTop (𝓝 (H : ℝ)⁻¹) := by
    have hsum := tendsto_finsetSum (Finset.Ico 1 H) hlag
    rw [Finset.sum_const_zero] at hsum
    simpa using (tendsto_add_sub_one_div_one hH1).mul
      (tendsto_const_nhds.add (hsum.const_mul (2 / (H : ℝ) ^ 2)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hrhs_tend.eventually_lt_const hHinv)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_zero_right]
  have hsq := vanDerCorput_unit_avg_sq_le (fun i ↦ UnitAddTorus.norm_mFourier_apply k (x i)) hH1 n
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (hsq.trans_lt (hN n hn))

end DifferenceTheorem

end TauCeti
