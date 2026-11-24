/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Algebra.Order.GroupWithZero.Basic
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.RCLike.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne
import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic

/-!
# Landau upper bounds for the logarithmic derivative of the Riemann zeta function

For `1 ≤ |Im s|` and `1 ≤ Re s ≤ 9 / 8`, the Euler–Maclaurin bound
`‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s` (`TauCeti.norm_riemannZeta_le_of_re_pos`) controls
`ζ` on the disc of radius `1 / 2` centred at `9 / 8 + i t`, away from its pole at `s = 1`. Landau's
local logarithmic-derivative lemma then gives an upper bound `A * log (|t| + 3)` for
`-Re (ζ′/ζ)`, with an absolute constant `A > 0`, while retaining divisor-weighted zero terms
over any finite set `S` (only zeros in `S ∩ closedBall ((9 / 8 : ℝ) + t * I) (1 / 4)`
contribute).

Extending past `Re s = 9 / 8` via the Dirichlet series at `9 / 8` drops the retained-zero sum and
bounds only `-Re (ζ′/ζ)` across `1 ≤ Re s` (`1 ≤ |Im s|`). Absorbing the single-zero reciprocal
`(σ - ρ.re)⁻¹` outside the local range `1 ≤ σ ≤ 9 / 8`, `7 / 8 ≤ ρ.re` gives the uniform
single-zero bound for all `σ ≥ 1` and every zero `ρ` of `riemannZeta` with `1 ≤ |ρ.im|`.
Combining the `1 ≤ |Im s|` bound with the regularized pole bound near `s = 1` on
`[1, 9 / 8] × [-1, 1]` yields the `(2 |Im s|)⁻¹ + B log (|Im s| + 3)` bound for all `1 ≤ Re s`
and `Im s ≠ 0`.

## Main results

* `TauCeti.exists_neg_re_logDeriv_riemannZeta_add_sum_le`: retained-zero Landau upper bound for
  `-Re (ζ′/ζ)` on `1 ≤ Re s ≤ 9 / 8`, `1 ≤ |Im s|`, retaining zeros in
  `S ∩ closedBall ((9 / 8 : ℝ) + t * I) (1 / 4)`.
* `TauCeti.exists_neg_re_logDeriv_riemannZeta_le`: the signed upper bound
  `-Re (ζ′/ζ(s)) ≤ A * log (|Im s| + 3)` with an absolute constant `A > 0`, uniformly for
  `1 ≤ Re s` and `1 ≤ |Im s|`, with no retained-zero sum.
* `TauCeti.exists_neg_re_logDeriv_riemannZeta_add_sub_inv_le`: uniform single-zero bound for
  `-Re (ζ′/ζ(σ + ρ.im * I)) + (σ - ρ.re)⁻¹` for all `1 ≤ σ` and every zero `ρ` with `1 ≤ |ρ.im|`.
* `TauCeti.exists_neg_re_logDeriv_riemannZeta_le_inv_add_mul_log_of_im_ne_zero`:
  `-Re (ζ′/ζ(s)) ≤ (2 |Im s|)⁻¹ + B log (|Im s| + 3)` uniformly for `1 ≤ Re s` and `Im s ≠ 0`.
* `TauCeti.neg_re_logDeriv_riemannZeta_le`: for every `t₀ > 1`, the two inputs
  `-Re (ζ′/ζ)(1 + δ + 2 i t) ≤ C log |t|` and
  `-Re (ζ′/ζ)(1 + δ + i t) ≤ -1 / (1 + δ - β) + C log |t|` (at a zero `β + i t`) of the 3-4-1
  argument at height `|t| ≥ t₀` (Davenport §13), for every `δ ≥ 0`. Its statement follows
  chrisflav's PR https://github.com/TauCetiProject/TauCeti/pull/45143.

## References

* Michael Stoll, David Loeffler, and Terence Tao, `riemannZeta_ne_zero_of_one_le_re` in
  `Mathlib.NumberTheory.LSeries.Nonvanishing`.
-/

public section

open Complex DirichletCharacter Metric Set

namespace TauCeti

/-- **Retained-zero Landau upper bound for `-Re (ζ′/ζ)`.** There is an absolute constant `A > 0`
such that for `1 ≤ σ ≤ 9 / 8`, `1 ≤ |t|`, and any finite set `S : Finset ℂ`, retaining the
divisor-weighted zero terms over `S` (where only zeros in
`S ∩ closedBall ((9 / 8 : ℝ) + t * I) (1 / 4)` contribute) gives an `A * Real.log (|t| + 3)`
upper bound. -/
theorem exists_neg_re_logDeriv_riemannZeta_add_sum_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {σ t : ℝ}, 1 ≤ σ → σ ≤ 9 / 8 → 1 ≤ |t| → ∀ S : Finset ℂ,
      -(logDeriv riemannZeta (σ + t * I)).re +
          ∑ ρ ∈ S, (MeromorphicOn.divisor riemannZeta
            (closedBall ((9 / 8 : ℝ) + t * I) ((1 / 2 : ℝ) / 2)) ρ : ℝ) *
            ((((σ : ℂ) + t * I) - ρ)⁻¹).re ≤
        A * Real.log (|t| + 3) := by
  obtain ⟨A, hA, hLandau⟩ :=
    TauCeti.exists_neg_re_logDeriv_add_sum_divisor_half_le_ofReal_add_mul_I
      (x₀ := 9 / 8) (R := 1 / 2) (b := Real.exp (-(riemannZeta (9 / 8 : ℝ)).re))
      (c := 3) (K₀ := 3) (a := 3) (by norm_num) (Real.exp_pos _) (by norm_num) (by norm_num)
  refine ⟨A, hA, fun {σ t} hσ1 hσ2 ht S ↦ ?_⟩
  have him_ge {w : ℂ} (hw : w ∈ closedBall ((9 / 8 : ℝ) + t * I) (1 / 2)) : 1 / 2 ≤ |w.im| := by
    have him_diff : |w.im - t| ≤ 1 / 2 := by
      simpa using RCLike.abs_im_sub_le_of_mem_closedBall hw
    cases abs_cases t <;> cases abs_cases w.im <;> linarith [abs_le.mp him_diff]
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall ((9 / 8 : ℝ) + t * I) (1 / 2)) :=
    analyticOnNhd_riemannZeta_closedBall (by simp; linarith)
  have hb₀ : Real.exp (-(riemannZeta (9 / 8 : ℝ)).re) ≤ ‖riemannZeta ((9 / 8 : ℝ) + t * I)‖ := by
    simpa [LFunction_modOne_eq] using
      (1 : DirichletCharacter ℂ 1).exp_neg_re_riemannZeta_le_norm_LFunction
        (s := (9 / 8 : ℝ) + t * I) (by simp; norm_num)
  refine hLandau hf hb₀ (fun w hw hwre hwn ↦ ?_) (by linarith) hσ2
    (riemannZeta_ne_zero_of_one_le_re (by simp [hσ1])) S
    (fun ρ _ _ h0 ↦ (re_lt_one_of_riemannZeta_eq_zero h0).le.trans (by simp [hσ1]))
    (by linarith [abs_nonneg t])
  have hw_im : 1 / 2 ≤ |w.im| := him_ge (sphere_subset_closedBall hw)
  have hinv : ‖w - 1‖⁻¹ ≤ 2 := by
    refine inv_le_of_inv_le₀ (by norm_num) ?_
    calc (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      _ ≤ |w.im| := hw_im
      _ = |(w - 1).im| := by simp
      _ ≤ ‖w - 1‖ := abs_im_le_norm _
  norm_num at hwre
  calc ‖riemannZeta w‖ ≤ ‖w - 1‖⁻¹ + 1 + ‖w‖ / w.re :=
      TauCeti.norm_riemannZeta_le_of_re_pos (by linarith)
    _ ≤ 2 + 1 + (|t| + 3) / (5 / 8) := by gcongr
    _ ≤ 3 * (|t| + 3) := by linarith

/-- **Upper bound for `-Re (ζ′/ζ)` away from the real axis.** There is an absolute constant `A > 0`
such that `-(logDeriv riemannZeta s).re ≤ A * Real.log (|s.im| + 3)` whenever `1 ≤ s.re` and
`1 ≤ |s.im|` (with no retained-zero sum). -/
theorem exists_neg_re_logDeriv_riemannZeta_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {s : ℂ}, 1 ≤ s.re → 1 ≤ |s.im| →
      -(logDeriv riemannZeta s).re ≤ A * Real.log (|s.im| + 3) := by
  obtain ⟨A₀, hA₀, h⟩ := exists_neg_re_logDeriv_riemannZeta_add_sum_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let σ₀ : ℝ := 9 / 8
  refine ⟨max A₀ (-(logDeriv riemannZeta σ₀).re / Real.log 3), lt_max_of_lt_left hA₀,
    fun {s} hs ht ↦ ?_⟩
  simpa [LFunction_modOne_eq] using
    (1 : DirichletCharacter ℂ 1).neg_re_logDeriv_LFunction_le_max_mul_of_bound_on_left
      (σ₀ := σ₀) (by norm_num [σ₀]) hlog3
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])) fun hs9 ↦ by
        simpa [LFunction_modOne_eq, re_add_im s] using h hs hs9 ht ∅

/-- **Single-zero Landau upper bound for `-Re (ζ′/ζ)` away from the real axis.** There is an
absolute constant `A > 0` such that for every `σ ≥ 1` and every zero `ρ` of `riemannZeta` with
`1 ≤ |ρ.im|`,
`-(logDeriv riemannZeta (σ + ρ.im * I)).re + (σ - ρ.re)⁻¹ ≤ A * Real.log (|ρ.im| + 3)`. -/
theorem exists_neg_re_logDeriv_riemannZeta_add_sub_inv_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {σ : ℝ} {ρ : ℂ}, 1 ≤ σ → 1 ≤ |ρ.im| → riemannZeta ρ = 0 →
      -(logDeriv riemannZeta (σ + ρ.im * I)).re + (σ - ρ.re)⁻¹ ≤
        A * Real.log (|ρ.im| + 3) := by
  obtain ⟨A₁, hA₁, hsum⟩ := exists_neg_re_logDeriv_riemannZeta_add_sum_le
  obtain ⟨A₂, _, hle⟩ := exists_neg_re_logDeriv_riemannZeta_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨max A₁ (A₂ + (1 / 8)⁻¹ / Real.log 3), lt_max_of_lt_left hA₁,
    fun {σ ρ} hσ1 ht hζ0 ↦ ?_⟩
  exact TauCeti.neg_re_logDeriv_add_sub_inv_le_max_mul
    (f := riemannZeta) (ρ := ρ) (σ₁ := 1) (σ₀ := 9 / 8) (σ := σ) (r := (1 / 2 : ℝ) / 2)
    (d := 1 / 8) (A₁ := A₁) (A₂ := A₂) (L₀ := Real.log 3) (L := Real.log (|ρ.im| + 3))
    hσ1 (by norm_num) (by norm_num) (by norm_num) hlog3
    (Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im]))
    (analyticOnNhd_riemannZeta_closedBall (by simp; linarith))
    (riemannZeta_ne_zero_of_one_le_re (by simp; norm_num)) hζ0
    (re_lt_one_of_riemannZeta_eq_zero hζ0).le
    (fun hσ9 ↦ hsum hσ1 hσ9 ht {ρ})
    (by simpa using hle (s := σ + ρ.im * I) (by simp [hσ1]) (by simpa using ht))

/-- **Upper bound for `-Re (ζ′/ζ)` across the closed half-plane `1 ≤ Re s` off the real axis.**
There is an absolute constant `B > 0` such that
`-(logDeriv riemannZeta s).re ≤ (2 * |s.im|)⁻¹ + B * Real.log (|s.im| + 3)` whenever `1 ≤ s.re`
and `s.im ≠ 0`. -/
theorem exists_neg_re_logDeriv_riemannZeta_le_inv_add_mul_log_of_im_ne_zero :
    ∃ B : ℝ, 0 < B ∧ ∀ {s : ℂ}, 1 ≤ s.re → s.im ≠ 0 →
      -(logDeriv riemannZeta s).re ≤ (2 * |s.im|)⁻¹ + B * Real.log (|s.im| + 3) := by
  obtain ⟨A, hA, hhigh⟩ := exists_neg_re_logDeriv_riemannZeta_le
  have hK : IsCompact (Icc (1 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨CK, hCK⟩ := hK.exists_norm_logDeriv_riemannZeta_add_inv_sub_one_le fun z hz ↦
    (Set.mem_Icc.1 (Complex.mem_reProdIm.1 hz).1).1
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
  · have hsK : s ∈ Icc (1 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1 :=
      Complex.mem_reProdIm.2 ⟨Set.mem_Icc.2 ⟨hs, hs9⟩, Set.mem_Icc.2 (abs_le.mp ht.le)⟩
    have hs1 : s ≠ 1 := fun h ↦ hsim (by simpa using congrArg im h)
    have hb : -(logDeriv riemannZeta s + (s - 1)⁻¹).re ≤ C₉ :=
      (neg_le_abs _).trans <| (abs_re_le_norm _).trans <|
        (hCK s hsK hs1).trans ((le_max_right 0 CK).trans (le_max_left _ _))
    have hs_re : ((s - 1)⁻¹).re ≤ (2 * |s.im|)⁻¹ := by
      simpa using RCLike.inv_re_le_two_mul_abs_im_inv (z := s - 1) (by simpa using hsim)
    rw [add_re] at hb
    linarith
  · have hnorm : -(logDeriv riemannZeta s).re ≤ C₉ := by
      refine ((neg_le_abs _).trans ((abs_re_le_norm _).trans ?_)).trans (le_max_right _ _)
      simpa [LFunction_modOne_eq] using
        (1 : DirichletCharacter ℂ 1).norm_logDeriv_LFunction_le_of_le_re
          (σ := 9 / 8) (by norm_num) hs9.le
    linarith

/-- **3-4-1 inputs for `-Re (ζ′/ζ)` at height `t`.** For every `t₀ > 1` there is `C`
such that, for `δ ≥ 0` and `|t| ≥ t₀`, `-Re (ζ′/ζ)(1 + δ + 2it) ≤ C log |t|`, and
`-Re (ζ′/ζ)(1 + δ + it) ≤ -1 / (1 + δ - β) + C log |t|` whenever `β + it` is a zero of `ζ`: the
two inputs of the 3-4-1 argument at height `t` (Davenport §13). The threshold keeps `log |t|`
positive. -/
theorem neg_re_logDeriv_riemannZeta_le (t₀ : ℝ) (ht₀ : 1 < t₀) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 ≤ δ → ∀ t : ℝ, t₀ ≤ |t| →
      -(logDeriv riemannZeta (1 + δ + 2 * t * I)).re ≤ C * Real.log |t| ∧
        ∀ β : ℝ, riemannZeta (β + t * I) = 0 →
          -(logDeriv riemannZeta (1 + δ + t * I)).re ≤ -1 / (1 + δ - β) + C * Real.log |t| := by
  obtain ⟨A₁, hA₁, hfree⟩ := exists_neg_re_logDeriv_riemannZeta_le
  obtain ⟨A₂, hA₂, hret⟩ := exists_neg_re_logDeriv_riemannZeta_add_sub_inv_le
  set M : ℝ := 1 + Real.log 5 / Real.log t₀
  refine ⟨max A₁ A₂ * M, fun δ hδ t ht ↦ ?_⟩
  have ht1 : 1 ≤ |t| := ht₀.le.trans ht
  -- Both heights `t` and `2t` give `log (|Im s| + 3) ≤ log (5 |t|) ≤ M log |t|`.
  have hL : Real.log (2 * |t| + 3) ≤ M * Real.log |t| := by
    have h5 := TauCeti.le_div_mul_of_le (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5))
      (Real.log_pos ht₀) (Real.log_le_log (by linarith) ht)
    calc Real.log (2 * |t| + 3) ≤ Real.log (5 * |t|) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 5 + Real.log |t| := Real.log_mul (by norm_num) (by positivity)
      _ ≤ M * Real.log |t| := by simp only [M]; linarith
  have hL1 : Real.log (|t| + 3) ≤ M * Real.log |t| :=
    (Real.log_le_log (by positivity) (by linarith)).trans hL
  have hML : 0 ≤ M * Real.log |t| := (Real.log_nonneg (by linarith)).trans hL1
  have hA {A : ℝ} {L : ℝ} (hA0 : 0 < A) (hLe : L ≤ M * Real.log |t|) (hAle : A ≤ max A₁ A₂) :
      A * L ≤ max A₁ A₂ * M * Real.log |t| := by
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hLe hA0.le).trans (mul_le_mul_of_nonneg_right hAle hML)
  refine ⟨?_, fun β hβ ↦ ?_⟩
  · have h := hfree (s := 1 + δ + 2 * t * I) (by simp; linarith) (by simp [abs_mul]; linarith)
    rw [show ((1 : ℂ) + δ + 2 * t * I).im = 2 * t by simp, abs_mul, abs_two] at h
    exact h.trans (hA hA₁ hL (le_max_left _ _))
  · have h := hret (σ := 1 + δ) (ρ := β + t * I) (by linarith) (by simpa using ht1) hβ
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
      add_im, mul_im, zero_add, add_zero, ofReal_add, ofReal_one] at h
    have := hA hA₂ hL1 (le_max_right _ _)
    rw [neg_div, one_div]
    linarith

end TauCeti
