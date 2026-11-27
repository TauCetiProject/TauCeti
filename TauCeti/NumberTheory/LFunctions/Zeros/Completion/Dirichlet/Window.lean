/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard
import TauCeti.Analysis.Complex.Hadamard.Window
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.LogDeriv.Growth
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic

/-!
# Local logarithmic derivative of a primitive Dirichlet L-function

On `-1 ≤ Re s ≤ 2`, subtract the poles whose ordinates differ from `Im s` by at most one.
The remaining logarithmic derivative is bounded uniformly in the conductor. This is the
local estimate used to control the horizontal sides of explicit-formula contours. The
window and normalization are those of Koukoulopoulos, *The Distribution of Prime Numbers*,
Lemma 11.4, with the local estimate obtained here by horizontal comparison of Hadamard sums.
-/

public section

open Complex TauCeti TauCeti.LFunctions

namespace DirichletCharacter

/-- On the right reference line the logarithmic derivative of the entire completion is
bounded by `C log (N (|Im s| + 2))` uniformly in primitive nonprincipal characters. -/
theorem exists_norm_logDeriv_completion_le_log_of_re_eq_two :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
      (hχ : χ.IsPrimitive), χ ≠ 1 → ∀ s : ℂ, s.re = 2 → 1 / 2 ≤ |s.im| →
      ‖logDeriv (dirichletData χ hχ).entireCompletion s‖ ≤
        C * Real.log (N * (|s.im| + 2)) := by
  obtain ⟨D, hD, hΓ⟩ := exists_norm_logDeriv_gammaFactor_le_log
  let B := |(logDeriv riemannZeta 2).re|
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / 2 + D + B / Real.log 2, by positivity, fun {N} [_] χ hχ hne s hs him ↦ ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hx : 2 ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hlog : Real.log 2 ≤ Real.log (|s.im| + 2) := Real.log_le_log (by norm_num) hx
  have hB : B ≤ (B / Real.log 2) * Real.log (|s.im| + 2) := by
    calc B = (B / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ hlog2.ne').symm
         _ ≤ _ := by gcongr
  have hL := χ.norm_logDeriv_LFunction_le (s := s) (by rw [hs]; norm_num)
  rw [hs] at hL
  have hG := hΓ χ s (by rw [hs]; constructor <;> norm_num) him
  have hsum := logDeriv_dirichletData_entireCompletion χ hχ hne (s := s) (by rw [hs]; norm_num)
    (χ.LFunction_ne_zero_of_one_le_re (.inl hne) (by rw [hs]; norm_num))
  rw [hsum, Real.log_mul (by positivity) (by positivity)]
  calc
    _ ≤ Real.log N / 2 + ‖logDeriv χ.gammaFactor s‖ + ‖logDeriv χ.LFunction s‖ := by
      have ht := norm_add_le ((Real.log N : ℂ) / 2) (logDeriv χ.gammaFactor s)
      rw [norm_div, norm_ofNat, norm_real, Real.norm_of_nonneg (Real.log_nonneg hN)] at ht
      exact (norm_add_le _ _).trans (add_le_add_left ht _)
    _ ≤ (1 / 2 + D + B / Real.log 2) * (Real.log N + Real.log (|s.im| + 2)) := by
      have hLB : ‖logDeriv χ.LFunction s‖ ≤ B := hL.trans (neg_le_abs _)
      have h₁ : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN
      have h₂ : 0 ≤ Real.log (|s.im| + 2) := hlog2.le.trans hlog
      nlinarith only [hB, hLB, hG, h₂, mul_nonneg hD.le h₁,
        mul_nonneg (by positivity : 0 ≤ B / Real.log 2) h₁]

open scoped Classical in
/-- The Hadamard window error for a Dirichlet completion in terms of its logarithmic
derivative at the right reference point. -/
private theorem norm_logDeriv_completion_sub_window_sub_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {s w : ℂ}
    (hs : s.re ∈ Set.Icc (-1) 2) (hf : (dirichletData χ hχ).entireCompletion s ≠ 0)
    (hw : w.re = 2) (hwi : w.im = s.im) :
    let f := (dirichletData χ hχ).entireCompletion
    let d := MeromorphicOn.divisor f Set.univ
    ‖logDeriv f s - (∑' ρ : d.support, if |(ρ : ℂ).im - s.im| ≤ 1 then
      ((d ρ).toNat : ℂ) / (s - (ρ : ℂ)) else 0) - logDeriv f w‖ ≤ 12 * ‖logDeriv f w‖ := by
  have hd : ‖w - s‖ ≤ 3 := by
    have he : w - s = ((2 - s.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hw, hwi]
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    linarith [hs.1]
  have h := (dirichletData_entireCompletion_orderLE_one χ hχ).norm_logDeriv_sub_window_sub_le
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ) (fun _ hρ ↦
      Set.Ioo_subset_Icc_self (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hρ))
    hf hw hwi hd
  dsimp only at h
  rw [← re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ (by rw [hw]; norm_num))] at h
  exact h.trans (mul_le_mul_of_nonneg_left (re_le_norm _) (by norm_num))

open scoped Classical in
/-- The local logarithmic derivative estimate for primitive nonprincipal Dirichlet
characters. Subtract the multiplicity-weighted poles within one unit of `Im s`. The
resulting error is `O(log (N (|Im s| + 2)))` throughout the indicated strip. -/
theorem exists_norm_logDeriv_LFunction_sub_window_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
      (hχ : χ.IsPrimitive), χ ≠ 1 → ∀ s : ℂ, s.re ∈ Set.Icc (-1) 2 → 1 / 2 ≤ |s.im| →
      χ.LFunction s ≠ 0 →
      let d := MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ
      ‖logDeriv χ.LFunction s - ∑' ρ : d.support, if |(ρ : ℂ).im - s.im| ≤ 1 then
        ((d ρ).toNat : ℂ) / (s - (ρ : ℂ)) else 0‖ ≤ C * Real.log (N * (|s.im| + 2)) := by
  classical
  obtain ⟨A, hA, hRef⟩ := exists_norm_logDeriv_completion_le_log_of_re_eq_two
  obtain ⟨G, hG, hΓ⟩ := exists_norm_logDeriv_gammaFactor_le_log
  refine ⟨13 * A + 1 / 2 + G, by positivity, fun {N} [_] χ hχ hne s hs him hL ↦ ?_⟩
  let f := (dirichletData χ hχ).entireCompletion
  let w : ℂ := 2 + (s.im : ℂ) * I
  let d := MeromorphicOn.divisor f Set.univ
  let W := ∑' ρ : d.support, if |(ρ : ℂ).im - s.im| ≤ 1 then
    ((d ρ).toNat : ℂ) / (s - (ρ : ℂ)) else 0
  have hw : w.re = 2 := by simp [w]
  have hwi : w.im = s.im := by simp [w]
  have hN₁ : N ≠ 1 := fun h ↦ hne (χ.level_one' h)
  have hq := χ.LFunction_eq_completed_div_gammaFactor s (.inr hN₁)
  have hdiv : χ.completedLFunction s / χ.gammaFactor s ≠ 0 := hq ▸ hL
  obtain ⟨hcomp, hγ⟩ := div_ne_zero_iff.mp hdiv
  have hf : f s ≠ 0 := by
    have hpow : (N : ℂ) ^ (s / 2) ≠ 0 :=
      cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))
    simpa only [f, dirichletData_entireCompletion_eq χ hχ hne] using mul_ne_zero hpow hcomp
  have herr := norm_logDeriv_completion_sub_window_sub_le χ hχ hs hf hw hwi
  -- The conductor term and the gamma term account for the difference from the completion.
  have hsplit : logDeriv f s = (Real.log N : ℂ) / 2 + logDeriv χ.gammaFactor s +
      logDeriv χ.LFunction s := by
    dsimp only [f]
    rw [χ.logDeriv_dirichletData_entireCompletion_eq_logDeriv_Gammaℝ_add hχ hne hL,
      χ.logDeriv_gammaFactor_eq_logDeriv_Gammaℝ_add_sub_div hγ]
  have he : logDeriv χ.LFunction s - W = (logDeriv f s - W - logDeriv f w) +
      logDeriv f w - ((Real.log N : ℂ) / 2 + logDeriv χ.gammaFactor s) := by rw [hsplit]; ring
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlog : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have href := hRef χ hχ hne w hw (hwi ▸ him)
  rw [hwi] at href
  -- Fold the window sum back into `W` before rewriting the norm's argument.
  change ‖logDeriv χ.LFunction s - W‖ ≤ _
  rw [he, Real.log_mul (by positivity) (by positivity)]
  let u := logDeriv f s - W - logDeriv f w
  let v := logDeriv f w
  let g := logDeriv χ.gammaFactor s
  have hsum := (norm_sub_le (u + v) ((Real.log N : ℂ) / 2 + g)).trans
    (add_le_add (norm_add_le u v) (norm_add_le ((Real.log N : ℂ) / 2) g))
  rw [norm_div, norm_ofNat, norm_real, Real.norm_of_nonneg (Real.log_nonneg hN)] at hsum
  refine hsum.trans ?_
  rw [Real.log_mul (by positivity) (by positivity)] at href
  nlinarith only [herr, href, hΓ χ s hs him, mul_nonneg hG.le (Real.log_nonneg hN), hlog]

end DirichletCharacter
