/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import TauCeti.Analysis.Asymptotics.Sum.Rpow
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds

/-!
# Logarithmic upper bounds for `riemannZeta` near `Re s = 1`

Cutting the first-order Euler–Maclaurin formula of
`TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds` at `N = ⌈|t|⌉₊` bounds `ζ(σ + it)`, for
`σ > 0` and `|t| ≥ 1`, by a harmonic sum weighted by `n^(1-σ) ≤ max 1 ((|t| + 2)^(1-σ))`, plus
terms of the same size. On the curves `σ = 1 - A / log (|t| + 2)` that weight is at most `exp A`, so
`ζ(s) ≪_A log (|t| + 2)` there. Together with the bound `‖riemannZeta₀ s - 1/2‖ ≤ ‖s‖/(2 Re s)` far
to the right and compactness at bounded height, this bounds the entire function
`riemannZeta₀ s = ζ(s) - 1/(s - 1)` by `C log (|Im s| + 2)` on the whole region
`1 - A / log (|Im s| + 2) ≤ Re s`, for every real `A`.

With Mathlib's entire `riemannZeta₀` as the analytic extension of `ζ(s) - 1/(s - 1)`, the region
contains the strip `1 - β / log (|Im s| + 2) ≤ Re s ≤ 10` for every width `β`.

## Main results

* `TauCeti.norm_riemannZeta_le_of_one_le_abs_im`: for `0 < Re s` and `1 ≤ |Im s|`,
  `‖ζ(s)‖ ≤ max 1 ((|Im s| + 2)^(1 - Re s)) * (log (|Im s| + 2) + 2 + 1/(2 Re s)) + 1`.
* `TauCeti.exists_norm_riemannZeta₀_le_of_abs_im_le`: `riemannZeta₀` is bounded on every
  half-strip `σ₁ ≤ Re s`, `|Im s| ≤ T`.
* `TauCeti.exists_norm_riemannZeta₀_le_mul_log`: for every real `A` there is `C` with
  `‖riemannZeta₀ s‖ ≤ C log (|Im s| + 2)` whenever `1 - A / log (|Im s| + 2) ≤ Re s`.
* `TauCeti.exists_norm_riemannZeta_le_mul_log`: the same bound for `ζ(s)` itself when
  `1 ≤ |Im s|`.

## References

* `ZetaUpperBnd` and `ZetaBnd_aux2` in A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd*,
  file `PrimeNumberTheoremAnd/ZetaBounds.lean` at revision
  `df5f7cd6fb8f5e270cacda148c68cb00eb159556` of
  <https://github.com/TauCetiProject/PrimeNumberTheoremAnd>: the bound `ζ(σ + it) ≪ log |t|`
  for `1 - A / log |t| ≤ σ ≤ 2`, `|t| > 3`, with the cut at `⌊|t|⌋₊`. Here the cut is restated on
  the sawtooth truncation bound `TauCeti.norm_riemannZeta_sub_sum_sawtooth_natCast_le`, the
  normalization is `log (|t| + 2)`, the condition `σ ≤ 2` is removed, every width `A` is allowed,
  and the pole-subtracted function is bounded down to `Im s = 0`.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, Theorem 3.5.
-/

public section

open Complex

namespace TauCeti

private lemma one_le_norm_sub_one {s : ℂ} (ht : 1 ≤ |s.im|) : 1 ≤ ‖s - 1‖ := by
  have h := abs_im_le_norm (s - 1)
  simp only [sub_im, one_im, sub_zero] at h
  exact ht.trans h

private lemma ne_one_of_one_le_abs_im {s : ℂ} (ht : 1 ≤ |s.im|) : s ≠ 1 := by
  rintro rfl
  norm_num at ht

private lemma norm_inv_sub_one_le_one {s : ℂ} (ht : 1 ≤ |s.im|) : ‖(s - 1)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_sub_one ht)

private lemma one_le_log_abs_im_add_two {s : ℂ} (ht : 1 ≤ |s.im|) :
    1 ≤ Real.log (|s.im| + 2) := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

/-- The sawtooth tail at a cut point `N ≥ |Im s|`: `‖s‖ N^(-σ)/(2σ) ≤ N^(-σ)/2 + N^(1-σ)/(2σ)`
for `σ = Re s > 0`. -/
private lemma norm_mul_rpow_neg_div_le {s : ℂ} (hs : 0 < s.re) {N : ℝ} (htN : |s.im| ≤ N) :
    ‖s‖ * N ^ (-s.re) / (2 * s.re) ≤ N ^ (-s.re) / 2 + N ^ (1 - s.re) / (2 * s.re) := by
  rcases ((abs_nonneg _).trans htN).eq_or_lt with rfl | hN
  · rw [Real.zero_rpow (by linarith : -s.re ≠ 0)]
    simp only [mul_zero, zero_div, zero_add]
    positivity
  have hns : ‖s‖ ≤ s.re + N := by
    have := norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs] at this
    linarith
  have hNN : N ^ (1 - s.re) = N * N ^ (-s.re) := by
    rw [sub_eq_add_neg, Real.rpow_add hN, Real.rpow_one]
  calc ‖s‖ * N ^ (-s.re) / (2 * s.re) ≤ (s.re + N) * N ^ (-s.re) / (2 * s.re) := by gcongr
    _ = _ := by rw [hNN]; field_simp

/-- **A weighted harmonic bound for `ζ` off the real axis.** For `0 < Re s` and `1 ≤ |Im s|`,
`‖ζ(s)‖ ≤ max 1 ((|Im s| + 2)^(1 - Re s)) * (log (|Im s| + 2) + 2 + 1/(2 Re s)) + 1`. -/
theorem norm_riemannZeta_le_of_one_le_abs_im {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ max 1 ((|s.im| + 2) ^ (1 - s.re)) *
      (Real.log (|s.im| + 2) + 2 + 1 / (2 * s.re)) + 1 := by
  set σ := s.re
  set t := |s.im|
  set M := max 1 ((t + 2) ^ (1 - σ))
  set N := ⌈t⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by linarith)
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNt : (N : ℝ) ≤ t + 2 := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ t)]
  have hNσ : (N : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN₁ (by linarith)
  have hNM : (N : ℝ) ^ (1 - σ) ≤ M := Real.natCast_rpow_le_max_one_rpow hNt _
  -- The finite sum, the polar term, the boundary term and the sawtooth tail.
  have h₁ : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ M * (1 + Real.log (t + 2)) := by
    refine (norm_sum_Icc_cpow_neg_le_mul_one_add_log (by positivity) fun n _ hnN ↦
      Real.natCast_rpow_le_max_one_rpow ((Nat.cast_le.mpr hnN).trans hNt) _).trans ?_
    gcongr
  have h₂ : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ M := by
    rw [norm_div, norm_natCast_cpow_of_pos hN]
    simp only [sub_re, one_re]
    exact (div_le_self (by positivity) (one_le_norm_sub_one ht)).trans hNM
  have h₃ : ‖(N : ℂ) ^ (-s) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_natCast_cpow_of_pos hN, neg_re, Complex.norm_two]
    exact div_le_div_of_nonneg_right hNσ zero_le_two
  have h₄ : ‖s‖ * (N : ℝ) ^ (-σ) / (2 * σ) ≤ 1 / 2 + M * (1 / (2 * σ)) := by
    refine (norm_mul_rpow_neg_div_le hs (Nat.le_ceil t)).trans ?_
    rw [mul_one_div]
    gcongr
  have hEM := norm_riemannZeta_sub_sum_sawtooth_natCast_le hN.ne' hs (ne_one_of_one_le_abs_im ht)
  have htri := norm_le_insert' (riemannZeta s)
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2)
  have happrox := norm_sub_le
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)) ((N : ℂ) ^ (-s) / 2)
  have hadd := norm_add_le (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) ((N : ℂ) ^ (1 - s) / (s - 1))
  nlinarith

/-- **`riemannZeta₀` is bounded on half-strips of bounded height.** For real `σ₁` and `T` there is
`D` with `‖riemannZeta₀ s‖ ≤ D` whenever `σ₁ ≤ Re s` and `|Im s| ≤ T`. -/
theorem exists_norm_riemannZeta₀_le_of_abs_im_le (σ₁ T : ℝ) :
    ∃ D : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → |s.im| ≤ T → ‖riemannZeta₀ s‖ ≤ D := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (|σ₁| + 2 + T)).exists_bound_of_continuousOn
    differentiable_riemannZeta₀.continuous.continuousOn
  refine ⟨max K (1 + |T|), fun s hσ₁ ht ↦ ?_⟩
  rcases le_or_gt 2 s.re with hσ | hσ
  · have h := norm_riemannZeta₀_sub_one_half_le (by linarith : 0 < s.re)
    have hns : ‖s‖ ≤ s.re + |T| := by
      have := norm_le_abs_re_add_abs_im s
      rw [abs_of_pos (by linarith : 0 < s.re)] at this
      linarith [le_abs_self T]
    have hdiv : ‖s‖ / (2 * s.re) ≤ 1 / 2 + |T| := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg T]
    have := norm_le_insert' (riemannZeta₀ s) (1 / 2)
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    exact (by linarith : ‖riemannZeta₀ s‖ ≤ 1 + |T|).trans (le_max_right _ _)
  · refine (hK s ?_).trans (le_max_left _ _)
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (norm_le_abs_re_add_abs_im s).trans ?_
    have : |s.re| ≤ |σ₁| + 2 := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le σ₁, abs_nonneg σ₁]
    linarith

/-- The high-height case of `TauCeti.exists_norm_riemannZeta₀_le_mul_log`: for `0 ≤ B`,
`exp (2B) ≤ |Im s|` and `(1 - Re s) log (|Im s| + 2) ≤ B`,
`‖riemannZeta₀ s‖ ≤ (4 exp B + 2) log (|Im s| + 2)`. -/
private lemma norm_riemannZeta₀_le_of_exp_le_abs_im {B : ℝ} (hB : 0 ≤ B) {s : ℂ}
    (hTt : Real.exp (2 * B) ≤ |s.im|) (hAL : (1 - s.re) * Real.log (|s.im| + 2) ≤ B) :
    ‖riemannZeta₀ s‖ ≤ (4 * Real.exp B + 2) * Real.log (|s.im| + 2) := by
  set L := Real.log (|s.im| + 2)
  have ht : 1 ≤ |s.im| := (Real.one_le_exp (by positivity)).trans hTt
  have hL1 : 1 ≤ L := one_le_log_abs_im_add_two ht
  have hLB : 2 * B ≤ L := by
    rw [← Real.log_exp (2 * B)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hσ : 1 / 2 ≤ s.re := by
    by_contra h
    have : 1 / 2 * L < (1 - s.re) * L := mul_lt_mul_of_pos_right (by linarith) (by linarith)
    linarith
  have hM : max 1 ((|s.im| + 2) ^ (1 - s.re)) ≤ Real.exp B := by
    refine max_le (Real.one_le_exp hB) ?_
    rw [Real.rpow_def_of_pos (by positivity), mul_comm]
    exact Real.exp_le_exp.mpr hAL
  have hζ := norm_riemannZeta_le_of_one_le_abs_im (by linarith) ht
  have hinv : 1 / (2 * s.re) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hpole := norm_inv_sub_one_le_one ht
  have hdecomp : riemannZeta₀ s = riemannZeta s - (s - 1)⁻¹ := by
    rw [riemannZeta_eq_inv_sub_add (ne_one_of_one_le_abs_im ht)]
    ring
  have hfac : 0 ≤ L + 2 + 1 / (2 * s.re) := by positivity
  have hexp : 0 < Real.exp B := Real.exp_pos B
  calc ‖riemannZeta₀ s‖ ≤ ‖riemannZeta s‖ + ‖(s - 1)⁻¹‖ := hdecomp ▸ norm_sub_le _ _
    _ ≤ Real.exp B * (L + 3) + 2 := by nlinarith [mul_le_mul_of_nonneg_right hM hfac]
    _ ≤ (4 * Real.exp B + 2) * L := by nlinarith

/-- **`ζ(s) - 1/(s - 1)` is `O(log (|Im s| + 2))` right of the curves
`Re s = 1 - A / log (|Im s| + 2)`.** For every real `A` there is `C` such that the entire
function `riemannZeta₀ s`, equal to `ζ(s) - 1/(s - 1)` for `s ≠ 1`, satisfies
`‖riemannZeta₀ s‖ ≤ C log (|Im s| + 2)` whenever `1 - A / log (|Im s| + 2) ≤ Re s`. -/
theorem exists_norm_riemannZeta₀_le_mul_log (A : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, 1 - A / Real.log (|s.im| + 2) ≤ s.re →
      ‖riemannZeta₀ s‖ ≤ C * Real.log (|s.im| + 2) := by
  set B := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨D, hD⟩ := exists_norm_riemannZeta₀_le_of_abs_im_le (1 - B / Real.log 2)
    (Real.exp (2 * B))
  refine ⟨max (4 * Real.exp B + 2) (|D| / Real.log 2), fun s hs ↦ ?_⟩
  set L := Real.log (|s.im| + 2)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  have hL : 0 < L := hlog2.trans_le hL2
  have hAL : (1 - s.re) * L ≤ B := by
    have := (le_div_iff₀ hL).mp (by linarith : 1 - s.re ≤ A / L)
    linarith [le_max_left A 0]
  rcases le_or_gt (Real.exp (2 * B)) |s.im| with hTt | hTt
  · exact (norm_riemannZeta₀_le_of_exp_le_abs_im hB hTt hAL).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hL.le)
  · have hσ₁ : 1 - B / Real.log 2 ≤ s.re := by
      have : B / L ≤ B / Real.log 2 := div_le_div_of_nonneg_left hB hlog2 hL2
      have := (le_div_iff₀ hL).mpr hAL
      linarith
    have hbound := (hD s hσ₁ hTt.le).trans (le_abs_self D)
    calc ‖riemannZeta₀ s‖ ≤ |D| / Real.log 2 * L := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          nlinarith [abs_nonneg D]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le

/-- **`ζ(s)` is `O(log (|Im s| + 2))` right of the curves `Re s = 1 - A / log (|Im s| + 2)`,
away from the real axis.** For every real `A` there is `C` such that
`‖ζ(s)‖ ≤ C log (|Im s| + 2)` whenever `1 ≤ |Im s|` and `1 - A / log (|Im s| + 2) ≤ Re s`. -/
theorem exists_norm_riemannZeta_le_mul_log (A : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, 1 ≤ |s.im| → 1 - A / Real.log (|s.im| + 2) ≤ s.re →
      ‖riemannZeta s‖ ≤ C * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC⟩ := exists_norm_riemannZeta₀_le_mul_log A
  refine ⟨C + 1, fun s ht hs ↦ ?_⟩
  have hs₁ := ne_one_of_one_le_abs_im ht
  have hL1 := one_le_log_abs_im_add_two ht
  have hpole := norm_inv_sub_one_le_one ht
  rw [riemannZeta_eq_inv_sub_add hs₁]
  linarith [norm_add_le (s - 1)⁻¹ (riemannZeta₀ s), hC s hs]

end TauCeti
