/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.RCLike.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# Landau upper bounds for the logarithmic derivative of the Riemann zeta function

For `1 ≤ |Im s|` and `1 ≤ Re s ≤ 9 / 8`, the Euler–Maclaurin bound
`‖riemannZeta₀ w‖ ≤ 1 + ‖w‖ / Re w` controls `ζ` on the disc of radius `1 / 2` centred at
`9 / 8 + i t`, away from its pole at `s = 1`. Landau's local logarithmic-derivative lemma then
gives an `O(log (|t| + 3))` upper bound for `-Re (ζ′/ζ)` while retaining divisor-weighted zero
terms over any finite set `S`. Extending across `Re s > 9 / 8` via the Dirichlet series at `9 / 8`,
and combining with the regularized pole bound near `s = 1` on `[1, 9 / 8] × [-1, 1]`, yields
uniform bounds across `1 ≤ Re s` both for `1 ≤ |Im s|` and (with the `(2 |Im s|)⁻¹` pole term) for
all `Im s ≠ 0`.

## Main results

* `TauCeti.exists_neg_re_logDeriv_riemannZeta_add_sum_le`: retained-zero Landau upper bound for
  `-Re (ζ′/ζ)` on `1 ≤ Re s ≤ 9 / 8`, `1 ≤ |Im s|`.
* `TauCeti.exists_neg_re_logDeriv_riemannZeta_le`: `-Re (ζ′/ζ(s)) ≪ log (|Im s| + 3)` uniformly
  for `1 ≤ Re s` and `1 ≤ |Im s|`.
* `TauCeti.exists_neg_re_logDeriv_riemannZeta_le_of_im_ne_zero`:
  `-Re (ζ′/ζ(s)) ≤ (2 |Im s|)⁻¹ + B log (|Im s| + 3)` uniformly for `1 ≤ Re s` and `Im s ≠ 0`.

## References

* Michael Stoll, David Loeffler, and Terence Tao, `riemannZeta_ne_zero_of_one_le_re` in
  `Mathlib.NumberTheory.LSeries.Nonvanishing`.
-/

public section

open Complex DirichletCharacter Metric Set

namespace TauCeti

private theorem norm_riemannZeta_on_closedBall {t : ℝ} (ht : 1 ≤ |t|) {w : ℂ}
    (hw : w ∈ closedBall ((9 / 8 : ℝ) + t * I) (1 / 2)) :
    5 / 8 ≤ w.re ∧ 1 / 2 ≤ |w.im| ∧ ‖riemannZeta w‖ ≤ 3 * (|t| + 3) := by
  have hre_diff : |w.re - 9 / 8| ≤ 1 / 2 := by
    simpa using RCLike.abs_re_sub_le_of_mem_closedBall hw
  have him_diff : |w.im - t| ≤ 1 / 2 := by
    simpa using RCLike.abs_im_sub_le_of_mem_closedBall hw
  have hw_re : 5 / 8 ≤ w.re := by linarith [(abs_le.mp hre_diff).1]
  have hw_im : 1 / 2 ≤ |w.im| := by
    cases abs_cases t <;> cases abs_cases w.im <;> linarith [abs_le.mp him_diff]
  have hw1 : w ≠ 1 := fun h ↦ by subst h; norm_num at hw_im
  have hinv : ‖(w - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    refine inv_le_of_inv_le₀ (by norm_num) ?_
    calc (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      _ ≤ |w.im| := hw_im
      _ = |(w - 1).im| := by simp
      _ ≤ ‖w - 1‖ := abs_im_le_norm _
  have hwn : ‖w‖ ≤ |t| + 3 := by
    have h : ‖w‖ ≤ |(9 / 8 : ℝ)| + |t| + 1 / 2 :=
      RCLike.norm_le_of_mem_closedBall_ofReal_add_mul_I hw
    rw [abs_of_nonneg (by norm_num)] at h
    linarith
  have hζ₀ : ‖riemannZeta₀ w‖ ≤ 1 + (|t| + 3) / (5 / 8) :=
    (TauCeti.norm_riemannZeta₀_le_one_add_norm_div_re (by linarith)).trans (by gcongr)
  refine ⟨hw_re, hw_im, ?_⟩
  rw [riemannZeta_eq_inv_sub_add hw1]
  calc ‖(w - 1)⁻¹ + riemannZeta₀ w‖ ≤ ‖(w - 1)⁻¹‖ + ‖riemannZeta₀ w‖ := norm_add_le _ _
    _ ≤ 2 + (1 + (|t| + 3) / (5 / 8)) := add_le_add hinv hζ₀
    _ ≤ 3 * (|t| + 3) := by linarith

/-- **Retained-zero Landau upper bound for `-Re (ζ′/ζ)`.** There is an absolute constant `A > 0`
such that for `1 ≤ σ ≤ 9 / 8`, `1 ≤ |t|`, and any `S : Finset ℂ`, retaining the divisor-weighted
zero terms over `S` gives an `A * Real.log (|t| + 3)` upper bound. -/
theorem exists_neg_re_logDeriv_riemannZeta_add_sum_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {σ t : ℝ}, 1 ≤ σ → σ ≤ 9 / 8 → 1 ≤ |t| → ∀ S : Finset ℂ,
      -(logDeriv riemannZeta (σ + t * I)).re +
          ∑ ρ ∈ S, (MeromorphicOn.divisor riemannZeta
            (closedBall ((9 / 8 : ℝ) + t * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) *
            ((((σ : ℂ) + t * I) - ρ)⁻¹).re ≤
        A * Real.log (|t| + 3) := by
  obtain ⟨A, hA, hLandau⟩ := TauCeti.exists_neg_re_logDeriv_add_sum_divisor_half_le
    (R := 1 / 2) (b := Real.exp (-(riemannZeta (9 / 8 : ℝ)).re))
    (c := 3) (K₀ := 3) (by norm_num) (Real.exp_pos _) (by norm_num)
  refine ⟨A, hA, fun {σ t} hσ1 hσ2 ht S ↦ ?_⟩
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall ((9 / 8 : ℝ) + t * I) (1 / 2)) :=
    analyticOn_riemannZeta.mono fun w hw h1 ↦ by
      have := (norm_riemannZeta_on_closedBall ht hw).2.1
      subst h1; norm_num at this
  have hb₀ : Real.exp (-(riemannZeta (9 / 8 : ℝ)).re) ≤ ‖riemannZeta ((9 / 8 : ℝ) + t * I)‖ := by
    simpa [LFunction_modOne_eq] using
      (1 : DirichletCharacter ℂ 1).exp_neg_re_riemannZeta_le_norm_LFunction
        (s := (9 / 8 : ℝ) + t * I) (by simp; norm_num)
  have hz : ‖((σ : ℂ) + t * I) - ((9 / 8 : ℝ) + t * I)‖ ≤ (1 / 2 : ℝ) / 4 := by
    rw [← dist_eq_norm, Complex.dist_of_im_eq (by simp), Real.dist_eq]
    simpa [abs_le] using ⟨by linarith, by linarith⟩
  exact hLandau hf hb₀
    (fun w hw ↦ (norm_riemannZeta_on_closedBall ht (sphere_subset_closedBall hw)).2.2) hz
    (riemannZeta_ne_zero_of_one_le_re (by simp [hσ1]))
    (fun ρ _ h0 ↦ (not_le.mp fun h1 ↦ riemannZeta_ne_zero_of_one_le_re h1 h0).le.trans
      (by simp [hσ1]))
    (by linarith [abs_nonneg t]) S

/-- **Upper bound for `-Re (ζ′/ζ)` away from the real axis.** There is an absolute constant `A > 0`
such that `-(logDeriv riemannZeta s).re ≤ A * Real.log (|s.im| + 3)` whenever `1 ≤ s.re` and
`1 ≤ |s.im|`. -/
theorem exists_neg_re_logDeriv_riemannZeta_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {s : ℂ}, 1 ≤ s.re → 1 ≤ |s.im| →
      -(logDeriv riemannZeta s).re ≤ A * Real.log (|s.im| + 3) := by
  obtain ⟨A₀, hA₀, h⟩ := exists_neg_re_logDeriv_riemannZeta_add_sum_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let σ₀ : ℝ := 9 / 8
  refine ⟨max A₀ (-(logDeriv riemannZeta σ₀).re / Real.log 3), lt_max_of_lt_left hA₀,
    fun {s} hs ht ↦ ?_⟩
  simpa [LFunction_modOne_eq] using
    (1 : DirichletCharacter ℂ 1).neg_re_logDeriv_LFunction_le_max_of_bound_on_left
      (σ₀ := σ₀) (by norm_num [σ₀]) hlog3
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])) fun hs9 ↦ by
        simpa [LFunction_modOne_eq, re_add_im s] using h hs hs9 ht ∅

/-- **Upper bound for `-Re (ζ′/ζ)` across the closed half-plane `1 ≤ Re s` off the real axis.**
There is an absolute constant `B > 0` such that
`-(logDeriv riemannZeta s).re ≤ (2 * |s.im|)⁻¹ + B * Real.log (|s.im| + 3)` whenever `1 ≤ s.re`
and `s.im ≠ 0`. -/
theorem exists_neg_re_logDeriv_riemannZeta_le_of_im_ne_zero :
    ∃ B : ℝ, 0 < B ∧ ∀ {s : ℂ}, 1 ≤ s.re → s.im ≠ 0 →
      -(logDeriv riemannZeta s).re ≤ (2 * |s.im|)⁻¹ + B * Real.log (|s.im| + 3) := by
  obtain ⟨A, hA, hhigh⟩ := exists_neg_re_logDeriv_riemannZeta_le
  have hK : IsCompact (Icc (1 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨CK, hCK⟩ := hK.exists_norm_logDeriv_riemannZeta_add_inv_sub_one_le fun z hz ↦ hz.1.1
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set C₉ : ℝ := max (max 0 CK) (-(logDeriv riemannZeta (9 / 8 : ℝ)).re)
  set B : ℝ := max A (C₉ / Real.log 3)
  refine ⟨B, lt_max_of_lt_left hA, fun {s} hs hsim ↦ ?_⟩
  set L : ℝ := Real.log (|s.im| + 3)
  have hL_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hL_pos : 0 < L := hlog3.trans_le hL_ge
  have hinv0 : 0 ≤ (2 * |s.im|)⁻¹ := by positivity
  rcases le_or_gt 1 |s.im| with ht | ht
  · linarith [hhigh hs ht, mul_le_mul_of_nonneg_right (le_max_left A (C₉ / Real.log 3)) hL_pos.le]
  have hC₉L : C₉ ≤ B * L := (TauCeti.le_div_mul_of_le ((le_max_left 0 CK).trans (le_max_left _ _))
    hlog3 hL_ge).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hL_pos.le)
  rcases le_or_gt s.re (9 / 8) with hs9 | hs9
  · have hsK : s ∈ Icc (1 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1 := ⟨⟨hs, hs9⟩, abs_le.mp ht.le⟩
    have hs1 : s ≠ 1 := fun h ↦ hsim (by simpa using congrArg im h)
    have hb : -(logDeriv riemannZeta s + (s - 1)⁻¹).re ≤ C₉ :=
      (neg_le_abs _).trans <| (abs_re_le_norm _).trans <|
        (hCK s hsK hs1).trans ((le_max_right 0 CK).trans (le_max_left _ _))
    have hs_re : ((s - 1)⁻¹).re ≤ (2 * |s.im|)⁻¹ := by
      simpa using RCLike.inv_re_le_inv_two_mul_abs_im (z := s - 1) (by simpa using hsim)
    rw [add_re] at hb
    linarith
  · have hnorm : -(logDeriv riemannZeta s).re ≤ C₉ := by
      refine ((neg_le_abs _).trans ((abs_re_le_norm _).trans ?_)).trans (le_max_right _ _)
      simpa [LFunction_modOne_eq] using
        (1 : DirichletCharacter ℂ 1).norm_logDeriv_LFunction_le_of_le_re
          (σ := 9 / 8) (by norm_num) hs9.le
    linarith

end TauCeti
