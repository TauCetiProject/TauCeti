/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HuaIntegral.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import TauCeti.Analysis.Real.Factorial

/-!
# Integrable affine determinant bounds

Hua's estimate for lower integrals gives an integrable negative determinant power on a complex
matrix space. In the one-sided affine case, in column dimension zero or at least seven, the
lower integral is bounded by the Jacobian factor and the negative power of the determinant of the
positive definite part, with no additional volume constant. This gives an integrable majorant
on affine families of frames.

The estimate uses `TauCeti.lintegral_norm_det_add_conjTranspose_mul_inv_pow_le`, the row-by-row
bound from Hua's *Harmonic Analysis of Functions of Several Complex Variables in the Classical
Domains*, §2.
-/

public section

open Fintype Matrix MeasureTheory
open scoped ComplexOrder

namespace TauCeti

/-- The negative power in Hua's two-sided affine estimate is integrable whenever the exponent
is at least the sum of the row and column dimensions. -/
theorem integrable_norm_det_add_conjTranspose_mul_inv_pow {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] {S : Matrix ι ι ℂ} (hS : S.det ≠ 0)
    {T : Matrix κ κ ℂ} (hT : T.det ≠ 0) (c : Matrix ι κ ℂ) {G : Matrix κ κ ℂ} (hG : G.PosDef)
    {r : ℕ} (hr : card κ ≤ r) :
    Integrable (fun X : ι → κ → ℂ ↦ ‖(G + (S * of X * T + c)ᴴ *
      (S * of X * T + c)).det‖⁻¹ ^ (r + card ι)) := by
  have hcont : Continuous (fun X : ι → κ → ℂ ↦
      (G + (S * of X * T + c)ᴴ * (S * of X * T + c)).det) := by
    fun_prop
  have hm := hcont.measurable.norm.inv.pow_const (r + card ι)
  refine (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (.of_forall fun X ↦ pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)).mp ?_
  exact ((lintegral_norm_det_add_conjTranspose_mul_inv_pow_le hS hT c hG hr).trans_lt
    ENNReal.ofReal_lt_top).ne

/-- **Hua's affine integral bound with unit volume factor.** In column dimension zero or at
least seven, the integral of the negative determinant power is bounded by the affine Jacobian
times the negative determinant power of the positive definite part. -/
theorem lintegral_norm_det_add_conjTranspose_mul_inv_pow_le_of_card_eq_zero_or_ge_seven
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : Matrix ι ι ℂ} (hS : S.det ≠ 0) (c : Matrix ι κ ℂ) {G : Matrix κ κ ℂ}
    (hG : G.PosDef) (hk : card κ = 0 ∨ 7 ≤ card κ) :
    ∫⁻ X : ι → κ → ℂ,
        ENNReal.ofReal (‖(G + (S * of X + c)ᴴ * (S * of X + c)).det‖⁻¹ ^ (card κ + card ι)) ≤
      ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ) * ‖G.det‖⁻¹ ^ card κ) := by
  have hT : (1 : Matrix κ κ ℂ).det ≠ 0 := by simp
  have h := lintegral_norm_det_add_conjTranspose_mul_inv_pow_le hS hT c hG le_rfl
  simp only [Matrix.mul_one, det_one, norm_one, inv_one, one_pow, one_mul] at h
  have hfactor : (Real.pi ^ card κ / ((card κ).factorial : ℝ)) ^ card ι ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (by positivity)).2 (Real.pi_pow_le_factorial_iff.2 hk))
  exact h.trans (ENNReal.ofReal_le_ofReal (by
    simpa using mul_le_mul_of_nonneg_right hfactor (by positivity)))

end TauCeti
