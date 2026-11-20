/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.SpecialFunctions.Log.GrowthScale
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDerivNearOne

/-!
# The classical zero-free region for the Riemann zeta function

De la Vallée Poussin proved that `ζ(s)` has no zeros in a region of the form
`Re s ≥ 1 - c / log (|Im s| + 3)` away from its simple pole at `s = 1`.

For `|Im s| ≥ 1`, the Euler–Maclaurin bound `‖riemannZeta₀ w‖ ≤ 1 + ‖w‖ / Re w` controls `ζ` on the
disc of radius `1 / 2` centred at `9 / 8 + i t`, away from the pole at `1`. Landau's local
logarithmic-derivative lemma then gives an upper bound of order `log (|t| + 3)` for `-Re (ζ′/ζ)`,
retaining any nearby zero `ρ = β + i t` with a positive partial-fraction term `(σ - β)⁻¹` (and
extending across `Re s > 9 / 8` via the Dirichlet series at `9 / 8`). Combined with the pole bound
`-Re (ζ′/ζ(1 + η)) ≤ η⁻¹ + O(1)` and the `3–4–1` trigonometric inequality at `σ = 1 + 4 (1 - β)`,
this forces `1 - β ≫ (log (|t| + 3))⁻¹`.

For `|Im s| ≤ 1`, the regularized function `LFunctionTrivChar₁ 1` (equal to `(s - 1) ζ(s)` away
from `s = 1`) is entire and nonvanishing along the segment `{1} × [-1, 1]`, so compactness separates
its zeros in `[1/2, 1] × [-1, 1]` from the line `Re s = 1` by a uniform strip.

## Main results

* `TauCeti.LFunctions.exists_neg_re_logDeriv_riemannZeta_le`: `-Re (ζ′/ζ(s)) ≪ log (|Im s| + 3)`
  uniformly for `1 ≤ Re s` and `1 ≤ |Im s|`.
* `TauCeti.LFunctions.exists_neg_re_logDeriv_riemannZeta_le_of_im_ne_zero`:
  `-Re (ζ′/ζ(s)) ≤ (2 |Im s|)⁻¹ + B log (|Im s| + 3)` uniformly for `1 ≤ Re s` and `Im s ≠ 0`.
* `TauCeti.LFunctions.riemannZeta_zeroFreeRegion`: the classical de la Vallée Poussin zero-free
  region `Re s ≥ 1 - c / log (|Im s| + 3)` for `riemannZeta` away from `s = 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §13.
* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §3.11.
-/

public section

open Complex DirichletCharacter Metric Set

namespace TauCeti.LFunctions

private theorem norm_riemannZeta_on_closedBall {t : ℝ} (ht : 1 ≤ |t|) {w : ℂ}
    (hw : w ∈ closedBall ((9 / 8 : ℝ) + t * I) (1 / 2)) :
    5 / 8 ≤ w.re ∧ 1 / 2 ≤ |w.im| ∧ ‖riemannZeta w‖ ≤ 3 * (|t| + 3) := by
  have hre_diff : |w.re - 9 / 8| ≤ 1 / 2 := by simpa using abs_re_sub_le_of_mem_closedBall hw
  have him_diff : |w.im - t| ≤ 1 / 2 := by simpa using abs_im_sub_le_of_mem_closedBall hw
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
    have h := norm_le_abs_re_add_abs_im_add_of_mem_closedBall hw
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at h
    norm_num at h
    linarith
  have hζ₀ : ‖riemannZeta₀ w‖ ≤ 1 + (|t| + 3) / (5 / 8) :=
    (TauCeti.norm_riemannZeta₀_le_one_add_norm_div_re (by linarith)).trans (by gcongr)
  refine ⟨hw_re, hw_im, ?_⟩
  rw [riemannZeta_eq_inv_sub_add hw1]
  calc ‖(w - 1)⁻¹ + riemannZeta₀ w‖ ≤ ‖(w - 1)⁻¹‖ + ‖riemannZeta₀ w‖ := norm_add_le _ _
    _ ≤ 2 + (1 + (|t| + 3) / (5 / 8)) := add_le_add hinv hζ₀
    _ ≤ 3 * (|t| + 3) := by linarith

private theorem exists_neg_re_logDeriv_riemannZeta_add_sum_le :
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
    rw [add_sub_add_right_eq_sub, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  exact hLandau hf hb₀
    (fun w hw ↦ (norm_riemannZeta_on_closedBall ht (sphere_subset_closedBall hw)).2.2) hz
    (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))
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
    (1 : DirichletCharacter ℂ 1).neg_re_logDeriv_LFunction_le_max_of_re_le
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
      simpa using (s - 1).inv_re_le_inv_two_mul_abs_im (by simpa using hsim)
    rw [add_re] at hb
    linarith
  · have hnorm : -(logDeriv riemannZeta s).re ≤ C₉ := by
      refine ((neg_le_abs _).trans ((abs_re_le_norm _).trans ?_)).trans (le_max_right _ _)
      simpa [LFunction_modOne_eq] using
        (1 : DirichletCharacter ℂ 1).norm_logDeriv_LFunction_le_of_le_re
          (σ := 9 / 8) (by norm_num) hs9.le
    linarith

private theorem exists_neg_re_logDeriv_riemannZeta_retained :
    ∃ A : ℝ, 0 < A ∧ ∀ {σ : ℝ} {s : ℂ}, 1 ≤ σ → σ ≤ 9 / 8 → 1 ≤ |s.im| → 7 / 8 ≤ s.re →
      riemannZeta s = 0 →
        -(logDeriv riemannZeta (σ + s.im * I)).re + (σ - s.re)⁻¹ ≤
          A * Real.log (|s.im| + 3) := by
  obtain ⟨A, hA, hLandau⟩ := exists_neg_re_logDeriv_riemannZeta_add_sum_le
  refine ⟨A, hA, fun {σ s} hσ1 hσ2 ht hs7 hζ0 ↦ ?_⟩
  have hs_lt1 : s.re < 1 :=
    by_contra fun h ↦ riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ0
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall ((9 / 8 : ℝ) + s.im * I) ((1 / 2 : ℝ) / 2)) :=
    analyticOn_riemannZeta.mono fun w hw h1 ↦ by
      have := (norm_riemannZeta_on_closedBall ht
        (closedBall_subset_closedBall (by norm_num) hw)).2.1
      subst h1; norm_num at this
  exact hf.neg_re_logDeriv_add_inv_sub_le
    (riemannZeta_ne_zero_of_one_le_re (by simp; norm_num))
    (abs_le.mpr ⟨by linarith, by linarith⟩) hζ0 (hs_lt1.le.trans hσ1) (hLandau hσ1 hσ2 ht {s})

private theorem exists_riemannZeta_ne_zero_of_one_le_abs_im :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 ≤ |s.im| → 1 - c / Real.log (|s.im| + 3) ≤ s.re →
      riemannZeta s ≠ 0 := by
  obtain ⟨A₁, hA₁, hfree⟩ := exists_neg_re_logDeriv_riemannZeta_le
  obtain ⟨A₂, hA₂, hret⟩ := exists_neg_re_logDeriv_riemannZeta_retained
  obtain ⟨C₁, hC₁0, hpole0⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set B : ℝ := 3 * C₁ / Real.log 3 + 4 * A₂ + 2 * A₁
  have hB : 0 < B := by positivity
  set c : ℝ := min (1 / 32 * Real.log 3) ((1 / 20) / (2 * B))
  refine ⟨c, by positivity, fun s ht hs hζ0 ↦ ?_⟩
  set L : ℝ := Real.log (|s.im| + 3)
  have hlog_ge : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlog_pos : 0 < L := hlog3.trans_le hlog_ge
  set δ : ℝ := 1 - s.re
  have hδ0 : 0 < δ := sub_pos.2 <|
    by_contra fun h ↦ riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ0
  have hδ_le : δ ≤ c / L := by linarith
  have hδ_32 : δ ≤ 1 / 32 := hδ_le.trans
    (TauCeti.div_le_of_le_mul_of_le (by norm_num) hlog3.le hlog_ge (min_le_left _ _))
  set σ : ℝ := 1 + 4 * δ
  have hpole : -(logDeriv riemannZeta σ).re ≤ (4 * δ)⁻¹ + C₁ / Real.log 3 * L :=
    le_trans (by simpa [σ] using hpole0 (η := 4 * δ) (by positivity) (by linarith))
      (add_le_add_right (TauCeti.le_div_mul_of_le hC₁0 hlog3 hlog_ge) _)
  have hzero_t : -(logDeriv riemannZeta (σ + s.im * I)).re + (5 * δ)⁻¹ ≤ A₂ * L := by
    have hsub : σ - s.re = 5 * δ := by simp only [σ, δ]; ring
    simpa [hsub] using hret (σ := σ) (s := s) (by linarith) (by linarith) ht (by linarith) hζ0
  have hzero_2t : -(logDeriv riemannZeta (σ + 2 * s.im * I)).re ≤ 2 * A₁ * L := by
    have him : ((σ : ℂ) + 2 * s.im * I).im = 2 * s.im := by simp
    have h2 := hfree (s := (σ : ℂ) + 2 * s.im * I) (by simp; linarith)
      (by rw [him, abs_mul]; norm_num; linarith)
    have hlog2 : Real.log (|2 * s.im| + 3) ≤ 2 * L := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      simpa using Real.log_mul_two_mul_add_le (q := 1) le_rfl (abs_nonneg s.im) (by norm_num)
    rw [him] at h2; nlinarith
  have h341 : 3 * (logDeriv riemannZeta σ).re + 4 * (logDeriv riemannZeta (σ + s.im * I)).re +
      (logDeriv riemannZeta (σ + 2 * s.im * I)).re ≤ 0 := by
    simpa [one_pow, LFunction_modOne_eq] using
      (1 : DirichletCharacter ℂ 1).threeFourOne_re_logDeriv_riemannZeta_LFunction_nonpos
        (σ := σ) (by linarith) s.im
  have hcomb : 1 / 20 * δ⁻¹ ≤ B * L := by
    have halg : 4 * (5 * δ)⁻¹ - 3 * (4 * δ)⁻¹ = 1 / 20 * δ⁻¹ := by field_simp [hδ0.ne']; ring
    have : B * L = 3 * (C₁ / Real.log 3 * L) + 4 * (A₂ * L) + 2 * A₁ * L := by simp [B]; ring
    linarith
  exact (TauCeti.mul_lt_mul_inv_of_le_div_two_mul hδ0 hB hlog_pos
    (hδ_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) hlog_pos.le))).not_ge hcomb

private theorem exists_riemannZeta_ne_zero_of_abs_im_le_one :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, s ≠ 1 → |s.im| ≤ 1 → 1 - δ ≤ s.re → riemannZeta s ≠ 0 := by
  set K : Set ℂ := Icc (1 / 2 : ℝ) 1 ×ℂ Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  set Z : Set ℂ := {z ∈ K | LFunctionTrivChar₁ 1 z = 0}
  have hZ : IsCompact Z :=
    hK.inter_right (isClosed_eq (differentiable_LFunctionTrivChar₁ 1).continuous continuous_const)
  have hline (z : ℂ) (hz : 1 ≤ z.re) : LFunctionTrivChar₁ 1 z ≠ 0 := by
    rcases eq_or_ne z 1 with rfl | hz1
    · exact LFunctionTrivChar₁_apply_one_ne_zero 1
    · rw [LFunctionTrivChar₁, Function.update_of_ne hz1, LFunctionTrivChar, LFunction_modOne_eq]
      exact mul_ne_zero (sub_ne_zero.2 hz1) (riemannZeta_ne_zero_of_one_le_re hz)
  have hne_of_not_mem (δ : ℝ) (hδ_half : δ ≤ 1 / 2) (hdisj : ∀ z ∈ Z, z.re < 1 - δ)
      (s : ℂ) (hs1 : s ≠ 1) (hsim : |s.im| ≤ 1) (hsre : 1 - δ ≤ s.re) : riemannZeta s ≠ 0 := by
    rcases le_or_gt 1 s.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1
    have hsK : s ∈ K := ⟨⟨by linarith, h1.le⟩, abs_le.mp hsim⟩
    have hsZ : LFunctionTrivChar₁ 1 s ≠ 0 := fun h0 ↦ (hdisj s ⟨hsK, h0⟩).not_ge hsre
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1, LFunctionTrivChar, LFunction_modOne_eq]
      at hsZ
    exact right_ne_zero_of_mul hsZ
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · exact ⟨1 / 2, by norm_num, hne_of_not_mem (1 / 2) le_rfl (by simp [hZe])⟩
  obtain ⟨z₀, hz₀Z, hz₀max⟩ := hZ.exists_isMaxOn hZne continuous_re.continuousOn
  have hz₀_lt1 : z₀.re < 1 :=
    lt_of_le_of_ne hz₀Z.1.1.2 fun h1 ↦ hline z₀ h1.ge hz₀Z.2
  refine ⟨min (1 / 2) ((1 - z₀.re) / 2), by positivity,
    hne_of_not_mem _ (min_le_left _ _) fun z hz ↦ ?_⟩
  have hle : z.re ≤ z₀.re := hz₀max hz
  have hmin : min (1 / 2) ((1 - z₀.re) / 2) ≤ (1 - z₀.re) / 2 := min_le_right _ _
  linarith

/-- **The classical de la Vallée Poussin zero-free region for `ζ`.** There is an absolute constant
`c > 0` such that `riemannZeta s ≠ 0` whenever `s ≠ 1` and
`1 - c / Real.log (|s.im| + 3) ≤ s.re`. -/
theorem riemannZeta_zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 3) ≤ s.re →
      riemannZeta s ≠ 0 := by
  obtain ⟨c₁, hc₁, hhigh⟩ := exists_riemannZeta_ne_zero_of_one_le_abs_im
  obtain ⟨δ, hδ, hlow⟩ := exists_riemannZeta_ne_zero_of_abs_im_le_one
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨min c₁ (δ * Real.log 3), by positivity, fun s hs1 hsre ↦ ?_⟩
  have hlog_ge : Real.log 3 ≤ Real.log (|s.im| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlog_pos : 0 < Real.log (|s.im| + 3) := hlog3.trans_le hlog_ge
  rcases le_or_gt 1 |s.im| with him | him
  · refine hhigh s him (le_trans ?_ hsre)
    gcongr
    exact min_le_left _ _
  · refine hlow s hs1 him.le (le_trans ?_ hsre)
    linarith [TauCeti.div_le_of_le_mul_of_le hδ.le hlog3.le hlog_ge (min_le_right c₁ _)]

/-! ### Example -/

example : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ 10 → ∀ σ : ℝ, 1 - δ ≤ σ → σ < 1 →
    riemannZeta (σ + t * I) ≠ 0 := by
  obtain ⟨c, hc, hζ⟩ := riemannZeta_zeroFreeRegion
  have _ : 0 < Real.log 13 := Real.log_pos (by norm_num)
  refine ⟨c / Real.log 13, by positivity, fun t ht σ hσ1 hσ2 ↦ ?_⟩
  have hs1 : (σ : ℂ) + t * I ≠ 1 := fun h ↦ by
    have := congrArg re h; simp at this; linarith
  refine hζ _ hs1 ?_
  have hlog : Real.log (|((σ : ℂ) + t * I).im| + 3) ≤ Real.log 13 :=
    Real.log_le_log (by positivity) (by simp; linarith)
  have hlog_pos : 0 < Real.log (|((σ : ℂ) + t * I).im| + 3) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans_le (Real.log_le_log (by norm_num) (by simp))
  have hdiv : c / Real.log 13 ≤ c / Real.log (|((σ : ℂ) + t * I).im| + 3) :=
    div_le_div_of_nonneg_left hc.le hlog_pos hlog
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  linarith

end TauCeti.LFunctions
