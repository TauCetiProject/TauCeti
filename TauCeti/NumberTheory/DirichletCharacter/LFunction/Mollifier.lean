/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
public import TauCeti.NumberTheory.LSeries.GaussianTheta
import TauCeti.Analysis.Complex.VerticalStrip.Basic
import TauCeti.Analysis.Complex.VerticalStrip.PowerBounds
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# A truncated Gaussian mollifier for Dirichlet L-functions, and zero detection

The Mellin integral of the theta series with coefficients `μ(n) χ(n)`, truncated below `r`,
approximates `Γℝ(s+j)/(2 L(s,χ))` on `Re s = 2`. Multiplying by the gamma-weighted L-function
shows that the error is `O(r)`, uniformly in the character, its modulus and the imaginary part.
This provides the right boundary estimate in the three-lines argument that detects zeros from
theta integrals. The estimate corresponds to `New.norm_mul_mollifier_sub_le` in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of lsernau/grh-lean (`72fead1`).

The zero-detection step interpolates a bound on the critical line and a decaying error bound on
`Re z = 2` for the mollified completed L-function. At a zero the mollified term drops out, so
the error bounds the square of the gamma factor. On a box of fixed height this excludes zeros,
provided the mollifier satisfies the two edge estimates at sufficiently large scale.

The choice of exponents and the half-gamma normalization follow
`New.three_lines_bound_of_LFunction_eq_zero` in `grh/src/Lib/Analytic/QuadraticTwist.lean`
(<https://github.com/lsernau/grh-lean>, commit `72fead1`).
-/

public section

section GaussianMollifier

open Complex MeasureTheory Set TauCeti
open scoped ArithmeticFunction.Moebius

namespace DirichletCharacter

/-- The Mellin integral above `r` of the Gaussian theta sum with coefficients `χ(n) μ(n)` and
monomial weight of degree `j`. For a character of parity `j ∈ {0,1}`, this mollifies the
L-function with its matching gamma factor. -/
noncomputable def gaussianMollifier {N : ℕ} (χ : DirichletCharacter ℂ N)
    (j : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi r, (t : ℂ) ^ (s - 1) *
    gaussianDirichletTheta j (fun n ↦ χ n * (μ n : ℂ)) t

/-- The defining truncated Mellin integral for the Gaussian mollifier. -/
theorem gaussianMollifier_def {N : ℕ} (χ : DirichletCharacter ℂ N)
    (j : ℕ) (r : ℝ) (s : ℂ) :
    χ.gaussianMollifier j r s =
    ∫ t : ℝ in Ioi r, (t : ℂ) ^ (s - 1) *
      gaussianDirichletTheta j (fun n ↦ χ n * (μ n : ℂ)) t := (rfl)

/-- On `Re s = 2`, the completed product of a Dirichlet L-function and its Gaussian
mollifier differs from the square of the half-gamma factor by at most `C r`. The constant
depends only on the degree `j` of the monomial weight. -/
theorem norm_LFunction_mul_gaussianMollifier_sub (j : ℕ) :
    ∃ C > (0 : ℝ), ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
      {r : ℝ}, 0 ≤ r → ∀ {s : ℂ}, s.re = 2 →
      ‖(Gammaℝ (s + j) / 2) * χ.LFunction s * χ.gaussianMollifier j r s -
        (Gammaℝ (s + j) / 2) ^ 2‖ ≤ C * r := by
  let Z : ℝ := ∑' n : ℕ, ‖LSeries.term 1 (2 : ℂ) n‖
  let G : ℝ := Real.pi ^ (-(2 + (j : ℝ)) / 2) * Real.Gamma ((2 + (j : ℝ)) / 2) / 2
  have hGpos : 0 < G := by dsimp [G]; positivity
  have hZnonneg : 0 ≤ Z := tsum_nonneg fun _ ↦ norm_nonneg _
  refine ⟨G * (Z + 1) * ((j.factorial : ℝ) * Real.exp 1),
    mul_pos (mul_pos hGpos (by linarith [hZnonneg])) (by positivity),
    fun {N} _ χ {r} hr {s} hs ↦ ?_⟩
  have hs₁ : 1 < s.re := by linarith
  have hχ : ‖χ.LFunction s‖ ≤ Z := by
    rw [LFunction_eq_LSeries χ hs₁]
    have h₁ : LSeriesSummable 1 (2 : ℂ) := LSeriesSummable_one_iff.mpr (by norm_num)
    have hχsum := χ.LSeriesSummable_of_one_lt_re hs₁
    refine (norm_tsum_le_tsum_norm hχsum.norm).trans
      (hχsum.norm.tsum_le_tsum (fun n ↦ ?_) h₁.norm)
    exact (LSeries.norm_term_le (g := 1) s (by simpa using χ.norm_le_one n)).trans
      (LSeries.norm_term_le_of_re_le_re 1 (by simp [hs]) n)
  have hΓ : ‖Gammaℝ (s + j) / 2‖ ≤ G := by
    have hσ : (s + (j : ℂ)).re = 2 + (j : ℝ) := by simp [hs]
    have hσ' : ((s + (j : ℂ)) / 2).re = (2 + (j : ℝ)) / 2 := by rw [div_ofNat_re, hσ]
    rw [norm_div, norm_ofNat, norm_Gammaℝ, hσ]
    dsimp only [G]
    gcongr
    simpa only [hσ'] using norm_Gamma_le_Gamma_re (s := (s + j) / 2) (by rw [hσ']; positivity)
  have hcoeff (n : ℕ) (_ : n ≠ 0) : ‖χ n * (μ n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n)).trans ?_
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  let γ := Gammaℝ (s + j) / 2
  have hinv : χ.LFunction s * LSeries (fun n ↦ χ n * (μ n : ℂ)) s = 1 := by
    rw [LFunction_eq_LSeries χ hs₁]
    exact LSeries.mul_mu_eq_one χ hs₁
  have heq : γ * χ.LFunction s * χ.gaussianMollifier j r s - γ ^ 2 =
      γ * χ.LFunction s *
        (χ.gaussianMollifier j r s - LSeries (fun n ↦ χ n * (μ n : ℂ)) s * γ) := by
    rw [mul_sub]
    congr 1
    rw [← mul_assoc, mul_assoc γ, hinv, mul_one, pow_two]
  calc
    _ = ‖γ‖ * ‖χ.LFunction s‖ *
        ‖χ.gaussianMollifier j r s - LSeries (fun n ↦ χ n * (μ n : ℂ)) s * γ‖ := by
      rw [heq, norm_mul, norm_mul]
    _ ≤ G * (Z + 1) * (1 * (j.factorial : ℝ) * Real.exp 1 * r) := by
      gcongr
      · exact hχ.trans (by linarith)
      · rw [gaussianMollifier_def]
        exact norm_integral_gaussianDirichletTheta_sub j hcoeff hr hs
    _ = _ := by ring

end DirichletCharacter

end GaussianMollifier

section ZeroDetection

open Complex Complex.HadamardThreeLines Filter Set
open TauCeti.Complex.HadamardThreeLines (closure_verticalStrip
  norm_le_max_mul_rpow_of_mem_verticalClosedStrip)
open scoped Topology

namespace TauCeti.DirichletCharacter

/-- The discrepancy of the mollified completion is continuous on the closed strip,
holomorphic in its interior, and bounded. -/
private theorem mollified_discrepancy_on_strip {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {M : ℂ → ℂ}
    (hM : DiffContOnCl ℂ M (verticalStrip (1 / 2) 2))
    (hMb : BddAbove ((norm ∘ M) '' verticalClosedStrip (1 / 2) 2))
    {C : ℝ} (hΓ : ∀ z ∈ verticalClosedStrip (1 / 2) 2, ‖χ.gammaFactor z / 2‖ ≤ C) :
    let F (z : ℂ) := χ.completedLFunction z / 2 * M z - (χ.gammaFactor z / 2) ^ 2
    DiffContOnCl ℂ F (verticalStrip (1 / 2) 2) ∧
      BddAbove ((norm ∘ F) '' verticalClosedStrip (1 / 2) 2) := by
  intro F
  have hΓd : DiffContOnCl ℂ (fun z ↦ (χ.gammaFactor z / 2) ^ 2) (verticalStrip (1 / 2) 2) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_verticalStrip (by norm_num : (1 / 2 : ℝ) < 2)]
    intro z hz
    have h := (χ.analyticAt_gammaFactor_of_re_pos
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le hz.1)).differentiableAt
    exact ((h.div_const 2).pow 2).differentiableWithinAt
  have hLd := _root_.DirichletCharacter.differentiable_completedLFunction hχ
  refine ⟨((hLd.div_const 2).diffContOnCl.smul hM).sub hΓd, ?_⟩
  obtain ⟨L, hL, hLb⟩ := exists_norm_completedLFunction_le_of_re_mem_Icc hχ (b := 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨B, hB⟩ := hMb
  refine ⟨L / 2 * B + C ^ 2, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  refine (norm_sub_le ..).trans ?_
  rw [norm_mul, norm_pow, norm_div (χ.completedLFunction z), norm_ofNat]
  exact add_le_add (mul_le_mul (div_le_div_of_nonneg_right (hLb z hz) (by norm_num))
    (hB (mem_image_of_mem _ hz)) (norm_nonneg _) (by positivity)) (by gcongr; exact hΓ z hz)

/-- For a nonprincipal character, critical-line bounds of `2 T ^ (2δ)` and `T ^ (2δ)` on
`Λ/2` and a mollifier `M`, and a right-edge error of `D / T`, force a small gamma factor at
any zero with real part at least `1/2 + 9δ`. The bound is uniform in the modulus. -/
theorem norm_gammaFactor_div_two_sq_le_of_LFunction_eq_zero (D : ℝ) :
    ∃ C > 0, ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ ≠ 1 →
    ∀ {T δ : ℝ}, 1 ≤ T → 0 ≤ δ → ∀ {M : ℂ → ℂ},
    DiffContOnCl ℂ M (verticalStrip (1 / 2) 2) →
    BddAbove ((norm ∘ M) '' verticalClosedStrip (1 / 2) 2) →
    (∀ z : ℂ, z.re = 1 / 2 → ‖χ.completedLFunction z / 2‖ ≤ 2 * T ^ (2 * δ)) →
    (∀ z : ℂ, z.re = 1 / 2 → ‖M z‖ ≤ T ^ (2 * δ)) →
    (∀ z : ℂ, z.re = 2 →
      ‖χ.completedLFunction z / 2 * M z - (χ.gammaFactor z / 2) ^ 2‖ ≤ D / T) →
    ∀ {s : ℂ}, 1 / 2 + 9 * δ ≤ s.re → χ.LFunction s = 0 →
      ‖χ.gammaFactor s / 2‖ ^ 2 ≤ C * T ^ (-2 * δ) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_gammaFactor_mul_one_add_norm_le (b := 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨max (2 + (CΓ / 2) ^ 2) D, lt_of_lt_of_le (by positivity) (le_max_left ..), ?_⟩
  intro N _ χ hχ T δ hT hδ M hM hMb hleftL hleftM hright s hs hzero
  let F (z : ℂ) := χ.completedLFunction z / 2 * M z - (χ.gammaFactor z / 2) ^ 2
  have hΓ' (z : ℂ) (hz : z ∈ verticalClosedStrip (1 / 2) 2) : ‖χ.gammaFactor z / 2‖ ≤ CΓ / 2 := by
    rw [norm_div, norm_ofNat]
    have h₁ : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
    exact div_le_div_of_nonneg_right ((le_mul_of_one_le_right (norm_nonneg _) h₁).trans
      (hΓ χ hz)) (by norm_num)
  obtain ⟨hd, hb⟩ := mollified_discrepancy_on_strip hχ hM hMb hΓ'
  have hl (z : ℂ) (hz : z.re = 1 / 2) : ‖F z‖ ≤ (2 + (CΓ / 2) ^ 2) * T ^ (4 * δ) := by
    have hz' : z ∈ verticalClosedStrip (1 / 2) 2 := ⟨hz.ge, by rw [hz]; norm_num⟩
    have hpow : 1 ≤ T ^ (4 * δ) := Real.one_le_rpow hT (by positivity)
    calc
      _ ≤ ‖χ.completedLFunction z / 2‖ * ‖M z‖ + ‖χ.gammaFactor z / 2‖ ^ 2 := by
        have h := norm_sub_le (χ.completedLFunction z / 2 * M z) ((χ.gammaFactor z / 2) ^ 2)
        rw [norm_mul, norm_pow] at h
        exact h
      _ ≤ (2 * T ^ (2 * δ)) * T ^ (2 * δ) + (CΓ / 2) ^ 2 :=
        add_le_add (mul_le_mul (hleftL z hz) (hleftM z hz) (norm_nonneg _) (by positivity))
          (by gcongr; exact hΓ' z hz')
      _ ≤ _ := by
        rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans_le hT), ← two_mul, ← mul_assoc]
        rw [add_mul]
        linarith [le_mul_of_one_le_right (sq_nonneg (CΓ / 2)) hpow]
  have hs₀ : 0 < s.re := by linarith
  have hFzero : ‖F s‖ = ‖χ.gammaFactor s / 2‖ ^ 2 := by
    simp [F, χ.completedLFunction_eq_gammaFactor_mul_LFunction hs₀, hzero, norm_pow]
  rw [← hFzero]
  have hs₁ : s.re < 1 := lt_of_not_ge fun h ↦ χ.LFunction_ne_zero_of_one_le_re (.inl hχ) h hzero
  have hz : s ∈ verticalClosedStrip (1 / 2) 2 := ⟨by linarith, hs₁.le.trans (by norm_num)⟩
  refine (norm_le_max_mul_rpow_of_mem_verticalClosedStrip
    (q := -1) (zero_lt_one.trans_le hT) hz hd hb hl
      (fun z hz ↦ by simpa only [F, Real.rpow_neg_one, div_eq_mul_inv] using hright z hz)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT ?_) (by positivity)
  let θ := (s.re - 1 / 2) / (2 - 1 / 2)
  have hθδ : 6 * δ ≤ θ := by dsimp only [θ]; norm_num; linarith
  have hθ : 0 ≤ θ := (by positivity : 0 ≤ 6 * δ).trans hθδ
  calc
    (1 - θ) * (4 * δ) + θ * (-1) ≤ 4 * δ - θ := by nlinarith [mul_nonneg hθ hδ]
    _ ≤ -2 * δ := by linarith

/-- For every fixed height `H` and `δ > 0`, at sufficiently large `T` the critical-line
and right-edge mollifier bounds exclude all zeros with `Re s ≥ 1/2 + 9δ` and `|Im s| ≤ H`.
The threshold is independent of the modulus and of the mollifier. -/
theorem eventually_LFunction_ne_zero_of_mollifier_bounds (D H : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ ≠ 1 →
    ∀ {M : ℂ → ℂ}, DiffContOnCl ℂ M (verticalStrip (1 / 2) 2) →
    BddAbove ((norm ∘ M) '' verticalClosedStrip (1 / 2) 2) →
    (∀ z : ℂ, z.re = 1 / 2 → ‖χ.completedLFunction z / 2‖ ≤ 2 * T ^ (2 * δ)) →
    (∀ z : ℂ, z.re = 1 / 2 → ‖M z‖ ≤ T ^ (2 * δ)) →
    (∀ z : ℂ, z.re = 2 →
      ‖χ.completedLFunction z / 2 * M z - (χ.gammaFactor z / 2) ^ 2‖ ≤ D / T) →
    ∀ {s : ℂ}, 1 / 2 + 9 * δ ≤ s.re → |s.im| ≤ H → χ.LFunction s ≠ 0 := by
  obtain ⟨C, _, hC⟩ := norm_gammaFactor_div_two_sq_le_of_LFunction_eq_zero D
  let K := Icc (1 / 2 : ℝ) 1 ×ℂ Icc (-H) H
  obtain ⟨c, hc, hΓ⟩ := exists_pos_le_norm_gammaFactor_on_isCompact
    (K := K) (isCompact_Icc.reProdIm isCompact_Icc)
    (fun z hz ↦ (by norm_num : (0 : ℝ) < 1 / 2).trans_le (mem_reProdIm.mp hz).1.1)
  have ht : Tendsto (fun T : ℝ ↦ C * T ^ (-2 * δ)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_mul] using
      (tendsto_rpow_neg_atTop (mul_pos two_pos hδ)).const_mul C
  have hsmall := ht.eventually_lt_const (by positivity : 0 < (c / 2) ^ 2)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall]
    with T hT hsmall N _ χ hχ M hM hMb hleftL hleftM hright s hs hH
  by_cases hs₁ : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) hs₁
  intro hzero
  have hK : s ∈ K := mem_reProdIm.mpr ⟨⟨by linarith, le_of_not_ge hs₁⟩, abs_le.mp hH⟩
  have hlower : (c / 2) ^ 2 ≤ ‖χ.gammaFactor s / 2‖ ^ 2 := by
    rw [norm_div, norm_ofNat]
    gcongr
    exact hΓ χ hK
  have hupper := hC hχ hT hδ.le hM hMb hleftL hleftM hright hs hzero
  exact (hlower.trans hupper).not_gt hsmall

end TauCeti.DirichletCharacter

end ZeroDetection
