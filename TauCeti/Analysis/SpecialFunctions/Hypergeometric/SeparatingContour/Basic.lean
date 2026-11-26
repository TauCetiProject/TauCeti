/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Barnes.Contour
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Analyticity and uniform vertical Stirling bounds for the Mellin–Barnes integrand

This module extends `TauCeti.Analysis.SpecialFunctions.Hypergeometric.Barnes.Contour` with:
* monotonicity of `Complex.gammaPolesRightOf` in the abscissa `σ`;
* the right-family residue formula
  `Complex.residue_hypergeometricMellinBarnesIntegrand_neg_sub_natCast_right` at `t = -b - k`,
  obtained by symmetry from `Complex.residue_hypergeometricMellinBarnesIntegrand_neg_sub_natCast`;
* `AnalyticAt` and joint five-variable holomorphy of `Complex.hypergeometricMellinBarnesIntegrand`
  in `(a, b, c, z, t)` away from the pole families `-a - ℕ`, `-b - ℕ`, `ℕ` and the branch cut
  `-z ∉ Complex.slitPlane`;
* uniform vertical-strip exponential decay bounds
  `Complex.exists_norm_hypergeometricMellinBarnesIntegrand_vertical_le` on bounded parameter balls
  and compact sectorial subsets of `-z ∈ Complex.slitPlane`, supporting locally uniform truncation
  and joint four-variable holomorphy in `SeparatingContour/Analyticity.lean`.

## Main results

* `Complex.gammaPolesRightOf_antitone`: `gammaPolesRightOf a` is antitone in `σ`.
* `Complex.analyticAt_hypergeometricMellinBarnesIntegrand`,
  `Complex.analyticAt_hypergeometricMellinBarnesIntegrand_uncurry`,
  `Complex.analyticAt_hypergeometricMellinBarnesIntegrand_uncurry_vertical`: single-variable and
  joint five-variable analyticity of `hypergeometricMellinBarnesIntegrand`.
* `Complex.residue_hypergeometricMellinBarnesIntegrand_neg_sub_natCast_right`: closed-form
  candidate-pole residue at `t = -b - k` by parameter symmetry.
* `Complex.exists_norm_hypergeometricMellinBarnesIntegrand_vertical_le`: uniform vertical decay
  bound on parameter balls and slit-plane sectors.

## References

* NIST DLMF, §15.6(ii), eq. 15.6.6; Whittaker & Watson, §14.5; Olver, Ch. 5.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace Complex

/-! ### Pole combinatorics and right-family residue -/

/-- `gammaPolesRightOf a` is antitone in the abscissa `σ`: shifting `σ` to the left only adds
poles of `t ↦ Γ(a + t)` to the right of `Re t = σ`. -/
theorem gammaPolesRightOf_antitone (a : ℂ) : Antitone (gammaPolesRightOf a) :=
  fun _ _ h s hs => by
    rw [mem_gammaPolesRightOf] at hs ⊢
    exact ⟨h.trans_lt hs.1, hs.2⟩

/-- Residue evaluation of `hypergeometricMellinBarnesIntegrand a b c z` at the candidate
left-family pole `t = -b - k` when `-b - k` avoids both `-a - ℕ` and `ℕ`. Note that the
reciprocal Gamma factor `(Γ(c - b - k))⁻¹` vanishes when `c - b - k ∈ -ℕ`, which cancels the pole
of `Γ(b + t)` and makes the singularity removable (with residue `0`). -/
theorem residue_hypergeometricMellinBarnesIntegrand_neg_sub_natCast_right (c : ℂ) {a b z : ℂ}
    (k : ℕ) (hb : ∀ m : ℕ, b + k ≠ -m) (hba : ∀ m : ℕ, a - b - k ≠ -m) :
    TauCeti.Contour.residue (hypergeometricMellinBarnesIntegrand a b c z) (-b - k) =
      (-1) ^ k / k ! * (Gamma (a - b - k) * Gamma (b + k) * (Gamma (c - b - k))⁻¹ *
        (-z) ^ (-b - k)) := by
  rw [hypergeometricMellinBarnesIntegrand_comm]
  exact residue_hypergeometricMellinBarnesIntegrand_neg_sub_natCast c k hb hba

/-! ### Single-variable and joint analyticity of the Mellin–Barnes integrand -/

/-- Away from the pole families `-a - ℕ`, `-b - ℕ`, and `ℕ`, `hypergeometricMellinBarnesIntegrand`
is analytic in `t` for all parameters `a, b, c, z : ℂ`. -/
theorem analyticAt_hypergeometricMellinBarnesIntegrand (a b c z : ℂ) {t : ℂ}
    (ha : ∀ k : ℕ, t ≠ -a - k) (hb : ∀ k : ℕ, t ≠ -b - k) (ht : ∀ m : ℕ, t ≠ m) :
    AnalyticAt ℂ (hypergeometricMellinBarnesIntegrand a b c z) t := by
  rw [funext (hypergeometricMellinBarnesIntegrand_def a b c z)]
  refine (((((analyticAt_Gamma fun k h => ha k (by dsimp at h; linear_combination h)).comp
    (analyticAt_const.add analyticAt_id)).mul
    ((analyticAt_Gamma fun k h => hb k (by dsimp at h; linear_combination h)).comp
      (analyticAt_const.add analyticAt_id))).mul
    ((analyticAt_Gamma fun m h => ht m (by dsimp at h; linear_combination -h)).comp
      analyticAt_id.neg)).mul
    ((differentiable_one_div_Gamma.analyticAt (c + t)).comp
      (analyticAt_const.add analyticAt_id))).mul
    (analyticAt_id.const_cpow (Or.inr (by simpa using ht 0)))

/-- Joint analyticity of the uncurried Mellin–Barnes integrand in `(a, b, c, z, t)` away from
the pole families `-a - ℕ`, `-b - ℕ`, `ℕ` and the branch cut `-z ∉ slitPlane`. -/
theorem analyticAt_hypergeometricMellinBarnesIntegrand_uncurry {p : ℂ × ℂ × ℂ × ℂ} {t : ℂ}
    (ha : ∀ k : ℕ, p.1 + t ≠ -k) (hb : ∀ k : ℕ, p.2.1 + t ≠ -k) (ht : ∀ m : ℕ, -t ≠ -m)
    (hz : -p.2.2.2 ∈ slitPlane) :
    AnalyticAt ℂ
      (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        hypergeometricMellinBarnesIntegrand x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2)
      (p, t) := by
  have hp1 : AnalyticAt ℂ (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ => x.1.1) (p, t) :=
    analyticAt_fst.comp analyticAt_fst
  have hp2 : AnalyticAt ℂ (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ => x.1.2.1) (p, t) :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hp3 : AnalyticAt ℂ (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ => x.1.2.2.1) (p, t) :=
    analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst))
  have hp4 : AnalyticAt ℂ (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ => x.1.2.2.2) (p, t) :=
    analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst))
  simp_rw [hypergeometricMellinBarnesIntegrand_def]
  exact ((((((analyticAt_Gamma ha).comp_of_eq (hp1.add analyticAt_snd) rfl).mul
    ((analyticAt_Gamma hb).comp_of_eq (hp2.add analyticAt_snd) rfl)).mul
    ((analyticAt_Gamma ht).comp_of_eq analyticAt_snd.neg rfl)).mul
    ((differentiable_one_div_Gamma.analyticAt (p.2.2.1 + t)).comp_of_eq
      (hp3.add analyticAt_snd) rfl)).mul (hp4.neg.cpow analyticAt_snd hz))

/-- Joint analyticity of the uncurried Mellin–Barnes integrand along a vertical point `t = σ + i y`
when `Re a + σ`, `Re b + σ ∉ -ℕ`, `σ ∉ ℕ`, and `-z ∈ slitPlane`. -/
theorem analyticAt_hypergeometricMellinBarnesIntegrand_uncurry_vertical {p : ℂ × ℂ × ℂ × ℂ}
    {σ : ℝ} (ha : ∀ k : ℕ, p.1.re + σ ≠ -k) (hb : ∀ k : ℕ, p.2.1.re + σ ≠ -k)
    (hσ : ∀ m : ℕ, σ ≠ m) (hz : -p.2.2.2 ∈ slitPlane) (y : ℝ) :
    AnalyticAt ℂ
      (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        hypergeometricMellinBarnesIntegrand x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2)
      (p, (σ : ℂ) + y * I) :=
  analyticAt_hypergeometricMellinBarnesIntegrand_uncurry
    (fun k h => ha k (by have hre := congrArg re h; simp at hre; linarith))
    (fun k h => hb k (by have hre := congrArg re h; simp at hre; linarith))
    (fun m h => hσ m (by have hre := congrArg re h; simp at hre; linarith)) hz

/-! ### Uniform vertical-strip Stirling decay bound -/

/-- Uniform vertical-strip exponential decay bound for `hypergeometricMellinBarnesIntegrand` on
bounded parameter balls and compact sectorial subsets of `-z ∈ slitPlane`. -/
theorem exists_norm_hypergeometricMellinBarnesIntegrand_vertical_le {R r₁ r₂ δ : ℝ}
    (hr₁ : 0 < r₁) (hδ : 0 < δ) :
    ∃ B Y₀ : ℝ, 0 ≤ B ∧ 1 ≤ Y₀ ∧ Integrable (fun y : ℝ => B * Real.exp (-δ * |y|)) ∧
      ∀ (a b c z : ℂ) (σ y : ℝ),
        ‖a‖ ≤ R → ‖b‖ ≤ R → ‖c‖ ≤ R → r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → |(-z).arg| ≤ π - 2 * δ →
        |σ| ≤ R → Y₀ ≤ |y| →
        ‖hypergeometricMellinBarnesIntegrand a b c z (σ + y * I)‖ ≤
          B * Real.exp (-δ * |y|) := by
  obtain ⟨A, Y₀, hY₀, hG⟩ :=
    TauCeti.exists_norm_Gamma_add_mul_I_le (2 * R) (by positivity : 0 < δ / 4)
  let Mz : ℝ := max |Real.log r₁| |Real.log (max r₁ r₂)|
  have hint_exp : Integrable fun y : ℝ => Real.exp (-δ * |y|) := by
    simpa only [neg_mul] using TauCeti.integrable_exp_neg_mul_abs hδ
  refine ⟨Real.exp (4 * A + R * Mz), Y₀, (Real.exp_pos _).le, hY₀, hint_exp.const_mul _,
    fun a b c z σ y ha hb hc hzr₁ hzr₂ harg hσ hy => ?_⟩
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  have hGshift {w : ℂ} (hw : ‖w‖ ≤ R) :
      ‖Gamma (w + (σ + y * I))‖ ≤ Real.exp (A + (-π / 2 + δ / 4) * |y|) ∧
        ‖(Gamma (w + (σ + y * I)))⁻¹‖ ≤ Real.exp (A + (π / 2 + δ / 4) * |y|) := by
    rw [← add_assoc]
    exact hG (w + σ) y
      (by
        simpa using ((abs_add_le w.re σ).trans
          (add_le_add ((abs_re_le_norm w).trans hw) hσ)).trans_eq (two_mul R).symm)
      (by simpa using ((abs_im_le_norm w).trans hw).trans (by linarith)) hy
  have hz_ne : -z ≠ 0 := neg_ne_zero.2 (norm_pos_iff.1 (hr₁.trans_le hzr₁))
  have hlogz : |Real.log ‖-z‖| ≤ Mz := by
    rw [norm_neg]
    exact abs_le.2 ⟨by linarith [Real.log_le_log hr₁ hzr₁, neg_abs_le (Real.log r₁),
        (le_max_left |Real.log r₁| |Real.log (max r₁ r₂)| : |Real.log r₁| ≤ Mz)],
      (Real.log_le_log (hr₁.trans_le hzr₁) (hzr₂.trans (le_max_right r₁ r₂))).trans
        ((le_abs_self _).trans (le_max_right _ _))⟩
  have hcpow : ‖(-z) ^ ((σ : ℂ) + y * I)‖ ≤ Real.exp (R * Mz + (π - 2 * δ) * |y|) :=
    norm_cpow_add_mul_I_le hz_ne hlogz harg hσ
  have hGs : ‖Gamma (-((σ : ℂ) + y * I))‖ ≤ Real.exp (A + (-π / 2 + δ / 4) * |y|) := by
    rw [neg_ofReal_add_mul_I]
    simpa only [abs_neg] using
      (hG ((-σ : ℝ) : ℂ) (-y) (by simpa using hσ.trans (by linarith))
        (by simp [hR]) (by simpa using hy)).1
  have hGa := (hGshift ha).1
  have hGb := (hGshift hb).1
  have hGc := (hGshift hc).2
  simp only [hypergeometricMellinBarnesIntegrand_def, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖ *
        ‖(Gamma (c + (σ + y * I)))⁻¹‖ * ‖(-z) ^ ((σ : ℂ) + y * I)‖
      ≤ Real.exp (A + (-π / 2 + δ / 4) * |y|) * Real.exp (A + (-π / 2 + δ / 4) * |y|) *
        Real.exp (A + (-π / 2 + δ / 4) * |y|) * Real.exp (A + (π / 2 + δ / 4) * |y|) *
        Real.exp (R * Mz + (π - 2 * δ) * |y|) := by gcongr
    _ = Real.exp (4 * A + R * Mz) * Real.exp (-δ * |y|) := by
        simp only [← Real.exp_add]; congr 1; ring

end Complex
