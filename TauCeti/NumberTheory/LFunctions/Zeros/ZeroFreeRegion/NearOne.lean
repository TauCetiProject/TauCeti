/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.DerivBound
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.Dirichlet
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.RiemannZeta
import TauCeti.NumberTheory.LSeries.Moebius
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds

/-!
# Uniform bounds for logarithmic derivatives near one

For levels `q ≤ X^A`, the pole-removed Dirichlet L-functions are nonvanishing on
`‖s - 1‖ ≤ 1/X` and their logarithmic derivatives there have norm at most `X`, for
sufficiently large `X`. The zero-free region and Siegel's theorem give a larger zero-free disc;
Borel–Carathéodory bounds the logarithmic derivative from a point just right of `1`.

The near-one estimate is the one used in `New.eventually_norm_logDeriv_entireL_le_near_one`
in the shorter GRH formalization (lsernau/grh-lean, `Lib/Analytic/Primes.lean`, at `72fead1`).
Here it holds for all polynomially bounded levels (not just powers of a fixed modulus), with an
ineffective threshold because the real-zero gap uses Siegel's theorem.
-/

public section

open Complex hiding log
open DirichletCharacter Filter Metric Real Asymptotics

namespace TauCeti.LFunctions

-- At polynomially bounded levels the Siegel gap is wider than the auxiliary disc.
private theorem eventually_real_ne_zero_of_level_le_pow (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ y ^ B →
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, 1 - β ≤ 5 / y → χ.LFunction β ≠ 0 := by
  let ε : ℝ := 1 / (4 * ((B : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, hSiegel⟩ := Multiquadratic.quadratic_LFunction_siegel hε
  have hlog := (isLittleO_log_rpow_rpow_atTop 2 (s := 3 / 4) (by norm_num)).const_mul_left
    (405 * (B : ℝ) ^ 2)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlog.bound (show 0 < C / 2 by positivity)]
    with y hy hlog q _ χ hq hquad hχ β hβ hz
  have hy₀ : 0 < y := zero_lt_one.trans hy
  have hq₃ : (3 : ℝ) ≤ q := by exact_mod_cast χ.three_le_level_of_ne_one hχ
  have hden : 0 < 81 * log (q : ℝ) ^ 2 := by
    exact mul_pos (by norm_num) (sq_pos_of_pos (log_pos (by linarith)))
  have hqpow : y ^ (-(1 / 4) : ℝ) ≤ (q : ℝ) ^ (-ε) := by
    have h := rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < q) hq (neg_nonpos.mpr hε.le)
    rw [← rpow_natCast, ← rpow_mul hy₀.le] at h
    refine (rpow_le_rpow_of_exponent_le hy.le ?_).trans h
    dsimp [ε]
    have : 0 < 4 * ((B : ℝ) + 1) := by positivity
    field_simp
    linarith
  have hlogq : log (q : ℝ) ≤ (B : ℝ) * log y :=
    (log_le_log (by positivity : (0 : ℝ) < q) hq).trans_eq (log_pow _ _)
  have hqlog : 405 * log (q : ℝ) ^ 2 ≤ (C / 2) * y ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ 405 * ((B : ℝ) * log y) ^ 2 := by gcongr
      _ = (405 * (B : ℝ) ^ 2) * (log y) ^ (2 : ℝ) := by rw [rpow_two]; ring
      _ ≤ _ := by
        refine (le_abs_self _).trans ?_
        simpa only [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hy₀.le _)] using hlog
  have hpower : y ^ (3 / 4 : ℝ) = y * y ^ (-(1 / 4) : ℝ) := by
    calc
      _ = y ^ ((1 : ℝ) + -(1 / 4)) := by norm_num
      _ = _ := by rw [rpow_add hy₀, rpow_one]
  have hgap := χ.LFunction_one_re_div_log_sq_le_one_sub_of_LFunction_eq_zero hχ hz
  have hfinal : (χ.LFunction 1).re ≤ 405 * log (q : ℝ) ^ 2 / y :=
    ((div_le_iff₀ hden).1 hgap).trans <|
      (mul_le_mul_of_nonneg_right hβ hden.le).trans_eq (by ring)
  have hupper : (405 * log (q : ℝ) ^ 2) / y ≤ (C / 2) * y ^ (-(1 / 4) : ℝ) := by
    rw [div_le_iff₀ hy₀]
    exact hqlog.trans_eq (by rw [hpower]; ring)
  have hlower := (mul_le_mul_of_nonneg_left hqpow hC.le).trans (hSiegel q χ hquad hχ)
  have := hlower.trans (hfinal.trans hupper)
  nlinarith [mul_pos hC (rpow_pos_of_pos hy₀ (-(1 / 4) : ℝ))]

private theorem eventually_LFunction_ne_zero_of_level_le_pow (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ y ^ B →
      ∀ s : ℂ, ‖s - 1‖ ≤ 5 / y → s ≠ 1 → χ.LFunction s ≠ 0 := by
  obtain ⟨c, hc, -, hreg⟩ := dirichletLFunction_zeroFreeRegion
  obtain ⟨d, hd, hζ⟩ := riemannZeta_zeroFreeRegion
  have hlog := (isLittleO_log_rpow_atTop (r := 1) one_pos).const_mul_left (5 * ((B : ℝ) + 2))
  filter_upwards [eventually_gt_atTop (10 : ℝ), hlog.bound (lt_min hc hd),
    eventually_real_ne_zero_of_level_le_pow B] with y hy hlog hreal q _ χ hq s hs hs₁
  have hy₀ : 0 < y := by linarith
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hδ : 5 / y < 1 := (div_lt_iff₀ hy₀).2 (by linarith)
  have hre : -(5 / y) ≤ s.re - 1 := by
    simpa using (abs_le.mp ((abs_re_le_norm (s - 1)).trans hs)).1
  have him : |s.im| ≤ 5 / y := by simpa using (abs_im_le_norm (s - 1)).trans hs
  have hL₀ : 0 < log ((q : ℝ) * (|s.im| + 3)) := log_pos (by nlinarith [abs_nonneg s.im])
  have hL : log ((q : ℝ) * (|s.im| + 3)) ≤ ((B : ℝ) + 2) * log y := by
    calc
      _ ≤ log (y ^ (B + 2)) := by
        apply log_le_log (by positivity)
        rw [pow_add]
        exact mul_le_mul hq (by linarith [show 4 ≤ y ^ 2 by nlinarith]) (by positivity)
          (by positivity)
      _ = _ := by rw [log_pow, Nat.cast_add]; norm_num
  have hsmall : 5 / y ≤ min c d / log ((q : ℝ) * (|s.im| + 3)) := by
    rw [div_le_div_iff₀ hy₀ hL₀]
    calc
      _ ≤ 5 * ((B : ℝ) + 2) * log y := by linarith
      _ ≤ _ := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, rpow_one, abs_of_pos hy₀]
        using hlog)
  intro hz
  by_cases hχ : χ = 1
  · subst χ
    have hm : changeLevel (one_dvd q) (1 : DirichletCharacter ℂ 1) = 1 := map_one _
    have hzeta := LFunction_changeLevel_eq_zero_iff (1 : DirichletCharacter ℂ 1) (one_dvd q)
      (by linarith : 0 < s.re) (.inr hs₁)
    rw [hm, LFunction_modOne_eq] at hzeta
    have hl : 0 < log (|s.im| + 3) := log_pos (by linarith [abs_nonneg s.im])
    have hle : log (|s.im| + 3) ≤ log ((q : ℝ) * (|s.im| + 3)) :=
      log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hq₁)
    have hδd := hsmall.trans ((div_le_div_of_nonneg_right (min_le_right _ _) hL₀.le).trans
      (div_le_div_of_nonneg_left hd.le hl hle))
    exact hζ s hs₁ (by linarith) (hzeta.1 hz)
  · have hsreg : 1 - c / log ((q : ℝ) * (|s.im| + 3)) ≤ s.re := by
      linarith [hsmall.trans (div_le_div_of_nonneg_right (min_le_left c d) hL₀.le)]
    obtain ⟨him₀, hsq, -⟩ := (hreg q χ).1 s hsreg
      (χ.meromorphicOrderAt_LFunction_pos_iff.2 ⟨hz, .inr hχ⟩)
    have heq : (s.re : ℂ) = s := Complex.ext (by simp) (by simpa using him₀.symm)
    exact hreal q χ hq (MulChar.isQuadratic_iff_sq_eq_one.2 hsq) hχ s.re (by linarith) (heq ▸ hz)

-- This estimate applies to the same pole-removed function on the Borel–Carathéodory disc.
open Classical in
private theorem norm_poleRemoved_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : ‖s - 1‖ ≤ 1 / 2) :
    ‖(if χ = 1 then LFunctionTrivChar₁ q else χ.LFunction) s‖ ≤ 8 * q := by
  classical
  have hre := (abs_re_le_norm (s - 1)).trans hs
  rw [sub_re, one_re] at hre
  have hsre : 1 / 2 ≤ s.re := by linarith [(abs_le.mp hre).1]
  have hsabs : ‖s‖ ≤ 3 / 2 := by
    calc
      _ = ‖s - 1 + 1‖ := by rw [sub_add_cancel]
      _ ≤ _ := by linarith [norm_add_le (s - 1) (1 : ℂ), norm_one (α := ℂ)]
  have hquot : ‖s‖ / s.re ≤ 3 := by
    rw [div_le_iff₀ (by linarith : 0 < s.re)]
    linarith
  by_cases hχ : χ = 1
  · simp only [ite_eq_left hχ]
    rcases eq_or_ne s 1 with rfl | h₁
    · calc
        ‖LFunctionTrivChar₁ q 1‖ ≤ 1 := by
          -- At the pole the definition is the updated value, not `(s - 1) * L(s)`.
          have hvalue : LFunctionTrivChar₁ q 1 = ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) :=
            Function.update_self _ _ _
          rw [hvalue, norm_prod]
          refine Finset.prod_le_one₀ (fun p _ ↦ norm_nonneg _) fun p hp ↦ ?_
          have hp₁ : (1 : ℝ) ≤ p := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
          rw [← ofReal_natCast, ← ofReal_inv, ← ofReal_one, ← ofReal_sub,
            norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hp₁))]
          linarith [inv_nonneg.mpr (show (0 : ℝ) ≤ p by positivity)]
        _ ≤ 8 * (q : ℝ) := by
          have : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
          linarith
    · rw [LFunctionTrivChar₁_apply_of_ne_one q h₁, norm_mul]
      have ht : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h₁)
      have hb := (1 : DirichletCharacter ℂ q).norm_LFunction_le (by linarith : 0 < s.re) (.inl h₁)
      calc
        _ ≤ ‖s - 1‖ * ((q : ℝ) * (‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re)) :=
          mul_le_mul_of_nonneg_left hb ht.le
        _ ≤ ‖s - 1‖ * ((q : ℝ) * (‖s - 1‖⁻¹ + 4)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by linarith only [hquot]) (Nat.cast_nonneg q)) ht.le
        _ = (q : ℝ) * (1 + 4 * ‖s - 1‖) := by field_simp
        _ ≤ 8 * q := by rw [mul_comm 8]; gcongr; linarith
  · simp only [ite_eq_right hχ]
    exact (χ.norm_LFunction_le_level_mul_norm_div_re hχ (by linarith : 0 < s.re)).trans (by
      rw [mul_div_assoc, mul_comm 8]; gcongr; linarith)

open Classical in
private theorem inv_bound_le_norm_poleRemoved {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {y : ℝ} (hy : 1 ≤ y) :
    1 / (2 * y ^ 2) ≤ ‖(if χ = 1 then LFunctionTrivChar₁ q else χ.LFunction) (1 + (y⁻¹ : ℝ))‖ := by
  classical
  let z : ℂ := 1 + (y⁻¹ : ℝ)
  have hy₀ : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hinv : 0 < y⁻¹ := inv_pos.mpr hy₀
  have hz : 1 < z.re := by simpa [z] using hinv
  have hz₁ : z ≠ 1 := by rintro h; simp [h] at hz
  have heq : z.re - 1 = y⁻¹ := by simp [z]
  have hζ := norm_riemannZeta_lt_one_add_one_div_sub_one (s := (z.re : ℂ)) (by simpa using hz)
  simp only [ofReal_re, heq, one_div, inv_inv] at hζ
  have hL : 1 / (2 * y) ≤ ‖χ.LFunction z‖ := by
    refine le_trans ?_ (χ.norm_riemannZeta_two_mul_re_div_le_norm_LFunction hz)
    rw [norm_div]
    have hzeta : 0 < ‖riemannZeta z.re‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hz))
    have hnum := (one_lt_riemannZeta_re (by linarith : 1 < 2 * z.re)).le.trans
      (re_le_norm (riemannZeta ((2 * z.re : ℝ) : ℂ)))
    push_cast at hnum
    exact div_le_div₀ (norm_nonneg _) hnum hzeta (hζ.le.trans (by linarith))
  by_cases hχ : χ = 1
  · rw [ite_eq_left hχ, LFunctionTrivChar₁_apply_of_ne_one q hz₁, norm_mul, LFunctionTrivChar,
      ← hχ]
    have ht : ‖z - 1‖ = y⁻¹ := by simp [z, abs_of_nonneg hy₀.le]
    rw [ht]
    calc
      _ = y⁻¹ * (1 / (2 * y)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hL hinv.le
  · rw [ite_eq_right hχ]
    exact (by gcongr; nlinarith : 1 / (2 * y ^ 2) ≤ 1 / (2 * y)).trans hL

open Classical in
private theorem eventually_poleRemoved_ne_zero_of_level_le_pow (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ y ^ B →
      ∀ s : ℂ, ‖s - 1‖ ≤ 5 / y → (if χ = 1 then LFunctionTrivChar₁ q else χ.LFunction) s ≠ 0 := by
  filter_upwards [eventually_LFunction_ne_zero_of_level_le_pow B] with y hzero q _ χ hq s hs
  by_cases hχ : χ = 1
  · rw [ite_eq_left hχ]
    rcases eq_or_ne s 1 with rfl | hs₁
    · exact LFunctionTrivChar₁_apply_one_ne_zero _
    · rw [LFunctionTrivChar₁_apply_of_ne_one q hs₁, LFunctionTrivChar, ← hχ]
      exact mul_ne_zero (sub_ne_zero.2 hs₁) (hzero q χ hq s hs hs₁)
  · rw [ite_eq_right hχ]
    rcases eq_or_ne s 1 with rfl | hs₁
    · exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simp)
    · exact hzero q χ hq s hs hs₁

-- Compare the norm on the larger disc to the norm at a reference point to the right of one.
open Classical in
private theorem norm_poleRemoved_le_mul_reference {B q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {y : ℝ} (hy : 1 ≤ y) (hq : (q : ℝ) ≤ y ^ B)
    {s : ℂ} (hs : ‖s - 1‖ ≤ 1 / 2) :
    let F := if χ = 1 then LFunctionTrivChar₁ q else χ.LFunction
    ‖F s‖ ≤ (16 * y ^ (B + 2)) * ‖F (1 + (y⁻¹ : ℝ))‖ := by
  calc
    _ ≤ 8 * (q : ℝ) := norm_poleRemoved_le χ hs
    _ ≤ 8 * y ^ B := by gcongr
    _ = (16 * y ^ (B + 2)) * (1 / (2 * y ^ 2)) := by rw [pow_add]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_bound_le_norm_poleRemoved χ hy) (by positivity)

open Classical in
private theorem eventually_norm_logDeriv_near_one_sq (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ y ^ B →
      ∀ s : ℂ, ‖s - 1‖ ≤ 1 / y ^ 2 →
        let F := if χ = 1 then LFunctionTrivChar₁ q else χ.LFunction
        F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ y ^ 2 := by
  classical
  have hlog : (fun y ↦ 6 * (B + 3 : ℝ) * log y) =o[atTop] (fun y : ℝ ↦ y) := by
    simpa only [rpow_one] using (isLittleO_log_rpow_atTop one_pos).const_mul_left (6 * (B + 3 : ℝ))
  filter_upwards [eventually_gt_atTop (16 : ℝ), eventually_poleRemoved_ne_zero_of_level_le_pow B,
    hlog.eventuallyLE] with y hy hzero hlog q _ χ hq s hs
  dsimp only
  set F := if χ = 1 then LFunctionTrivChar₁ q else χ.LFunction
  let r := y⁻¹
  let z : ℂ := 1 + (r : ℝ)
  have hy₀ : 0 < y := by linarith
  have hy₁ : 1 ≤ y := by linarith
  have hr : 0 < r := inv_pos.mpr hy₀
  have hz : dist z 1 = r := by simp [z, dist_eq_norm, abs_of_pos hr]
  have hsub : ball z (4 * r) ⊆ ball (1 : ℂ) (5 * r) :=
    ball_subset_ball' (by rw [hz]; linarith)
  have hdist {w : ℂ} (hw : w ∈ ball z (4 * r)) : ‖w - 1‖ ≤ 5 / y :=
    (mem_ball_iff_norm.1 (hsub hw)).le.trans_eq (by simp [r, div_eq_mul_inv])
  have hF : Differentiable ℂ F := by
    rcases eq_or_ne χ 1 with hχ | hχ
    · simpa [F, hχ] using differentiable_LFunctionTrivChar₁ q
    · simpa [F, hχ] using differentiable_LFunction hχ
  have hF₀ (w : ℂ) (hw : w ∈ ball z (4 * r)) : F w ≠ 0 := hzero q χ hq w (hdist hw)
  have hM (w : ℂ) (hw : w ∈ ball z (4 * r)) : ‖F w‖ ≤ (16 * y ^ (B + 2)) * ‖F z‖ :=
    norm_poleRemoved_le_mul_reference χ hy₁ hq
      ((hdist hw).trans ((div_le_iff₀ hy₀).2 (by linarith)))
  have hs' : ‖s - z‖ ≤ 2 * r := by
    have hsmall : 1 / y ^ 2 ≤ r := by dsimp [r]; rw [← one_div]; gcongr; nlinarith
    have h := dist_triangle s 1 z
    rw [dist_comm (1 : ℂ) z, hz, dist_eq_norm, dist_eq_norm] at h
    linarith only [h, hs.trans hsmall]
  have hs'' : ‖s - z‖ < 4 * r := hs'.trans_lt (by linarith)
  refine ⟨hF₀ s (mem_ball_iff_norm.mpr hs''), ?_⟩
  have hlogM : log (16 * y ^ (B + 2)) ≤ (B + 3 : ℝ) * log y := by
    rw [log_mul (by norm_num) (by positivity), log_pow, Nat.cast_add, Nat.cast_ofNat]
    linarith [log_le_log (by norm_num : (0 : ℝ) < 16) hy.le]
  calc
    _ ≤ 4 * (4 * r + ‖s - z‖) / (4 * r - ‖s - z‖) ^ 2 * log (16 * y ^ (B + 2)) :=
      norm_logDeriv_le_of_forall_mem_ball_norm_le_mul hF.differentiableOn hF₀ hM hs''
    _ ≤ 4 * (6 * r) / (2 * r) ^ 2 * ((B + 3 : ℝ) * log y) := by
      have hlog₀ : 0 ≤ log (16 * y ^ (B + 2)) := log_nonneg (by
        have := one_le_pow₀ hy₁ (n := B + 2)
        linarith)
      gcongr <;> linarith
    _ = y * (6 * (B + 3 : ℝ) * log y) := by dsimp [r]; field_simp; ring
    _ ≤ y ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_of_pos hy₀] using hlog)) hy₀.le

open Classical in
/-- Uniform near-one estimate for Dirichlet characters of level at most `X^A`. For sufficiently
large `X`, the L-function, with the pole of the principal character removed, is nonvanishing on
`‖s - 1‖ ≤ 1/X` and its logarithmic derivative there has norm at most `X`. -/
theorem eventually_norm_logDeriv_poleRemoved_LFunction_le_near_one (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ X ^ A →
      ∀ s : ℂ, ‖s - 1‖ ≤ 1 / X →
        let F := if χ = 1 then LFunctionTrivChar₁ q else χ.LFunction
        F s ≠ 0 ∧ ‖logDeriv F s‖ ≤ X := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    tendsto_sqrt_atTop.eventually (eventually_norm_logDeriv_near_one_sq (2 * A))]
    with X hX h q _ χ hq s hs
  simpa only [pow_mul, sq_sqrt hX] using h q χ (by simpa only [pow_mul, sq_sqrt hX]) s
    (by simpa only [sq_sqrt hX])

end TauCeti.LFunctions
