/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv

/-!
# Shared logarithmic-derivative bounds for zero-free regions

Zero-free region arguments for `riemannZeta` and `DirichletCharacter.LFunction` share three steps
around Landau's local logarithmic-derivative lemma:

1. **Uniform disc bound (`TauCeti.LFunctions.exists_neg_re_logDeriv_add_sum_divisor_half_le`)**:
   converting a uniform lower bound `b ≤ ‖f z₀‖` at the centre and a sphere upper bound
   `‖f w‖ ≤ c * K` (`1 < K₀ ≤ K`) into an `O(log K)` upper bound on
   `-Re (f′/f(z)) + ∑_{ρ ∈ S} m_ρ Re ((z - ρ)⁻¹)`, with a constant `A > 0` depending only on
   `(R, b, c, K₀)`.
2. **Single-zero retention (`TauCeti.LFunctions.neg_re_logDeriv_add_inv_sub_le`)**: specializing an
   `S = {ρ}` divisor-sum bound along the horizontal line `Im = ρ.im` to extract `(σ - ρ.re)⁻¹`.
3. **Horizontal tail extension (`TauCeti.LFunctions.neg_re_logDeriv_LFunction_le_max_of_strip`)**:
   combining a strip bound on `s.re ≤ σ₀` (`1 < σ₀`) with the Dirichlet-series comparison
   `‖L′/L(s, χ)‖ ≤ -Re (ζ′/ζ(σ₀))` across `σ₀ < s.re`.
-/

public section

open Complex DirichletCharacter Metric Set

namespace TauCeti.LFunctions

/-- **Uniform disc form of Landau's retained-zero inequality.** Fix a nonzero radius `R ≠ 0`, a
centre lower bound `b > 0`, a growth factor `c`, and a base `K₀ > 1`. There is a constant `A > 0`
depending only on `(R, b, c, K₀)` such that for every `f` analytic on `closedBall z₀ R` with
`b ≤ ‖f z₀‖` and `‖f w‖ ≤ c * K` on `sphere z₀ R` (`K₀ ≤ K`), at every `z` with `‖z - z₀‖ ≤ R / 4`,
`f z ≠ 0`, and `ρ.re ≤ z.re` for all zeros `ρ ∈ closedBall z₀ (R / 2)` of `f`, and for every
finite set `S : Finset ℂ`,
`-(logDeriv f z).re + ∑ ρ ∈ S, (divisor f (closedBall z₀ (R / 2)) ρ : ℝ) * ((z - ρ)⁻¹).re ≤
  A * Real.log K`. -/
theorem exists_neg_re_logDeriv_add_sum_divisor_half_le
    {R b c K₀ : ℝ} (hR : R ≠ 0) (hb : 0 < b) (hK₀ : 1 < K₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ {f : ℂ → ℂ} {z₀ z : ℂ} {K : ℝ},
      AnalyticOnNhd ℂ f (closedBall z₀ R) →
      b ≤ ‖f z₀‖ →
      (∀ w ∈ sphere z₀ R, ‖f w‖ ≤ c * K) →
      ‖z - z₀‖ ≤ R / 4 →
      f z ≠ 0 →
      (∀ ρ ∈ closedBall z₀ (R / 2), f ρ = 0 → ρ.re ≤ z.re) →
      K₀ ≤ K →
      ∀ S : Finset ℂ,
        -(logDeriv f z).re +
            ∑ ρ ∈ S, (MeromorphicOn.divisor f (closedBall z₀ (R / 2)) ρ : ℝ) * ((z - ρ)⁻¹).re ≤
          A * Real.log K := by
  have : 0 < |R| := abs_pos.2 hR
  set C₀ : ℝ := max 1 c / b
  have hC₀ : 0 < C₀ := by positivity
  have hlogK₀ : 0 < Real.log K₀ := Real.log_pos hK₀
  refine ⟨48 / |R| * (max 0 (Real.log C₀) / Real.log K₀ + 1), by positivity,
    fun {f z₀ z K} hf hb₀ hM₀ hz hfz hre hK S ↦ ?_⟩
  have hRpos : 0 < R := lt_of_le_of_ne (by linarith [norm_nonneg (z - z₀)]) hR.symm
  have hK_pos : 0 < K := (zero_lt_one.trans hK₀).trans_le hK
  have h1le : 1 ≤ b⁻¹ * ‖f z₀‖ := (le_inv_mul_iff₀ hb).2 (by simpa using hb₀)
  have hM (w : ℂ) (hw : w ∈ sphere z₀ R) : ‖f w‖ ≤ C₀ * K * ‖f z₀‖ := by
    calc ‖f w‖ ≤ c * K := hM₀ w hw
      _ ≤ max 1 c * K := mul_le_mul_of_nonneg_right (le_max_right _ _) hK_pos.le
      _ ≤ max 1 c * K * (b⁻¹ * ‖f z₀‖) := le_mul_of_one_le_right (by positivity) h1le
      _ = C₀ * K * ‖f z₀‖ := by simp only [C₀, div_eq_mul_inv]; ring
  have hmain := hf.neg_re_logDeriv_add_sum_divisor_half_le hR hM hz hfz hre S
  have hlog_ge : Real.log K₀ ≤ Real.log K := Real.log_le_log (zero_lt_one.trans hK₀) hK
  have hmax : Real.log C₀ ≤ max 0 (Real.log C₀) / Real.log K₀ * Real.log K :=
    (le_max_right _ _).trans (TauCeti.le_div_mul_of_le (le_max_left _ _) hlogK₀ hlog_ge)
  rw [Real.log_mul hC₀.ne' hK_pos.ne'] at hmain
  rw [abs_of_pos hRpos]
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_left hmax (Real.log K))
    (by positivity : (0 : ℝ) ≤ 48 / R)
  linarith

/-- Retaining a single zero `ρ` on the horizontal line `Im = ρ.im` inside a divisor-sum upper
bound: if `f` is analytic on `closedBall (σ₀ + ρ.im * I) r`, nonzero at the centre, and vanishes at
`ρ` with `|ρ.re - σ₀| ≤ r` and `ρ.re ≤ σ`, then the `S = {ρ}` sum contributes at least
`(σ - ρ.re)⁻¹`. -/
theorem neg_re_logDeriv_add_inv_sub_le {f : ℂ → ℂ} {σ₀ r σ B : ℝ} {ρ : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall ((σ₀ : ℂ) + ρ.im * I) r))
    (hfz₀ : f ((σ₀ : ℂ) + ρ.im * I) ≠ 0) (hρ : |ρ.re - σ₀| ≤ r) (hfρ : f ρ = 0)
    (hre : ρ.re ≤ σ)
    (hsum : -(logDeriv f ((σ : ℂ) + ρ.im * I)).re +
        ∑ w ∈ ({ρ} : Finset ℂ),
          (MeromorphicOn.divisor f (closedBall ((σ₀ : ℂ) + ρ.im * I) r) w : ℝ) *
            ((((σ : ℂ) + ρ.im * I) - w)⁻¹).re ≤ B) :
    -(logDeriv f ((σ : ℂ) + ρ.im * I)).re + (σ - ρ.re)⁻¹ ≤ B := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hρ
  have hterm := hf.inv_sub_re_le_divisor_mul (z := (σ : ℂ) + ρ.im * I)
    (convex_closedBall _ _).isPreconnected ⟨_, mem_closedBall_self hr, hfz₀⟩
    (mem_closedBall_ofReal_add_im_mul_I_iff.2 hρ) hfρ (by simpa using hre)
  have hdiff : ((σ : ℂ) + ρ.im * I) - ρ = ((σ - ρ.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp)
  rw [Finset.sum_singleton] at hsum
  rw [hdiff, ← ofReal_inv, ofReal_re] at hterm hsum
  linarith

/-- Extending an upper bound `-(logDeriv χ.LFunction s).re ≤ A₀ * L` from `s.re ≤ σ₀` (`1 < σ₀`) to
arbitrary `s : ℂ` via the Dirichlet-series comparison `‖L′/L(s, χ)‖ ≤ -Re (ζ′/ζ(σ₀))` on
`σ₀ ≤ s.re`. -/
theorem neg_re_logDeriv_LFunction_le_max_of_strip {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ₀ A₀ L₀ L : ℝ} (hσ₀ : 1 < σ₀) (hL₀ : 0 < L₀)
    (hL : L₀ ≤ L) {s : ℂ}
    (hstrip : s.re ≤ σ₀ → -(logDeriv χ.LFunction s).re ≤ A₀ * L) :
    -(logDeriv χ.LFunction s).re ≤ max A₀ (-(logDeriv riemannZeta σ₀).re / L₀) * L := by
  have hLnonneg : 0 ≤ L := hL₀.le.trans hL
  rcases le_or_gt s.re σ₀ with hs | hs
  · exact (hstrip hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hLnonneg)
  · have hC₀ : 0 ≤ -(logDeriv riemannZeta σ₀).re :=
      (norm_nonneg _).trans (χ.norm_logDeriv_LFunction_le_of_le_re (s := σ₀) hσ₀ (by simp))
    have htail : -(logDeriv χ.LFunction s).re ≤ -(logDeriv riemannZeta σ₀).re :=
      ((neg_le_abs _).trans (abs_re_le_norm _)).trans
        (χ.norm_logDeriv_LFunction_le_of_le_re hσ₀ hs.le)
    exact htail.trans ((TauCeti.le_div_mul_of_le hC₀ hL₀ hL).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hLnonneg))

end TauCeti.LFunctions
