/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.DerivBound
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.Dirichlet
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFreeRegion.RiemannZeta
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel

/-!
# Uniform bounds for logarithmic derivatives near one

The theorem `TauCeti.LFunctions.eventually_entireLFunction_ne_zero_and_norm_logDeriv_le_near_one`
shows that for sufficiently large `X` and levels `q ≤ X^A`, the pole-removed Dirichlet
L-functions are nonvanishing on `‖s - 1‖ ≤ 1/X` and their logarithmic derivatives there have
norm at most `X`. The zero-free region and Siegel's theorem give a larger zero-free disc;
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
  have hC₂ : 0 < C / 2 := by positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlog.bound hC₂]
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
        have hy₂ : 4 ≤ y ^ 2 := by nlinarith
        exact mul_le_mul hq (by linarith) (by positivity) (by positivity)
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

private theorem eventually_entireLFunction_ne_zero_of_level_le_pow (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ y ^ B →
      ∀ s : ℂ, ‖s - 1‖ ≤ 5 / y → χ.entireLFunction s ≠ 0 := by
  filter_upwards [eventually_LFunction_ne_zero_of_level_le_pow B] with y hzero q _ χ hq s hs
  rcases eq_or_ne s 1 with rfl | hs₁
  · exact χ.entireLFunction_ne_zero_of_one_le_re (by simp)
  · by_cases hχ : χ = 1
    · subst χ
      rw [entireLFunction_one_apply hs₁]
      exact mul_ne_zero (sub_ne_zero.2 hs₁) (hzero q 1 hq s hs hs₁)
    · rw [entireLFunction_of_ne_one hχ]
      exact hzero q χ hq s hs hs₁

-- Compare the norm on the larger disc to the norm at a reference point to the right of one.
private theorem norm_entireLFunction_le_mul_reference {B q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {y : ℝ} (hy : 1 ≤ y) (hq : (q : ℝ) ≤ y ^ B)
    {s : ℂ} (hs : ‖s - 1‖ ≤ 1 / 2) :
    ‖χ.entireLFunction s‖ ≤ (16 * y ^ (B + 2)) * ‖χ.entireLFunction (1 + (y⁻¹ : ℝ))‖ := by
  let z : ℂ := 1 + (y⁻¹ : ℝ)
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hz : 1 < z.re := by simpa [z] using inv_pos.mpr hy₀
  have hdist : ‖z - 1‖ = y⁻¹ := by simp [z, abs_of_nonneg hy₀.le]
  have hre : z.re - 1 = y⁻¹ := by simp [z]
  have hlower : y⁻¹ / (1 + y) ≤ ‖χ.entireLFunction z‖ := by
    simpa only [hdist, hre, inv_inv, min_eq_right (inv_le_one_of_one_le₀ hy)] using
      χ.min_one_norm_sub_one_div_le_norm_entireLFunction hz
  calc
    _ ≤ 8 * (q : ℝ) := χ.norm_entireLFunction_le_eight_mul_level hs
    _ ≤ 8 * y ^ B := by gcongr
    _ = (16 * y ^ (B + 2)) * (y⁻¹ / (2 * y)) := by rw [pow_add]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((div_le_div_of_nonneg_left (inv_nonneg.mpr hy₀.le) (by positivity) (by linarith)).trans
        hlower) (by positivity)

private theorem eventually_norm_logDeriv_near_one_sq (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ y ^ B →
      ∀ s : ℂ, ‖s - 1‖ ≤ 1 / y ^ 2 →
        χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ y ^ 2 := by
  have hlog : (fun y ↦ 6 * (B + 3 : ℝ) * log y) =o[atTop] (fun y : ℝ ↦ y) := by
    simpa only [rpow_one] using (isLittleO_log_rpow_atTop one_pos).const_mul_left (6 * (B + 3 : ℝ))
  filter_upwards [eventually_gt_atTop (16 : ℝ),
    eventually_entireLFunction_ne_zero_of_level_le_pow B, hlog.eventuallyLE]
    with y hy hzero hlog q _ χ hq s hs
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
  have hF₀ (w : ℂ) (hw : w ∈ ball z (4 * r)) : χ.entireLFunction w ≠ 0 :=
    hzero q χ hq w (hdist hw)
  have hM (w : ℂ) (hw : w ∈ ball z (4 * r)) :
      ‖χ.entireLFunction w‖ ≤ (16 * y ^ (B + 2)) * ‖χ.entireLFunction z‖ :=
    norm_entireLFunction_le_mul_reference χ hy₁ hq
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
      norm_logDeriv_le_of_forall_mem_ball_norm_le_mul
        χ.differentiable_entireLFunction.differentiableOn hF₀ hM hs''
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

/-- Uniform near-one estimate for Dirichlet characters of level at most `X^A`. For sufficiently
large `X`, the L-function, with the pole of the principal character removed, is nonvanishing on
`‖s - 1‖ ≤ 1/X` and its logarithmic derivative there has norm at most `X`. -/
theorem eventually_entireLFunction_ne_zero_and_norm_logDeriv_le_near_one (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ X ^ A →
      ∀ s : ℂ, ‖s - 1‖ ≤ 1 / X →
        χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ X := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    tendsto_sqrt_atTop.eventually (eventually_norm_logDeriv_near_one_sq (2 * A))]
    with X hX h q _ χ hq s hs
  simpa only [pow_mul, sq_sqrt hX] using h q χ (by simpa only [pow_mul, sq_sqrt hX]) s
    (by simpa only [sq_sqrt hX])

end TauCeti.LFunctions
