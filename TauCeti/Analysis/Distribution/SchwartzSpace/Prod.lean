/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Normed.Operator.Prod
public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Tensor products of Schwartz functions

For a real Schwartz function `ψ` on `D` and a Schwartz function `u` on `E`, the function
`(t, x) ↦ ψ t • u x` on `D × E` is again a Schwartz function, `SchwartzMap.prodSMul ψ u`. Its
directional derivative in the direction `(s, a)` is the sum of the tensor products of the
derivative of one factor with the other factor (`SchwartzMap.lineDerivOp_prodSMul`).

Such tensor products separate the variables of a product space. A typical use is to transfer an
estimate from `D × E` to `E` by testing it against `ψ ⊗ u` with `ψ` a fixed profile.

## Main declarations

* `SchwartzMap.prodSMul`: the Schwartz function `(t, x) ↦ ψ t • u x`.
* `SchwartzMap.lineDerivOp_prodSMul`: `∂_{(s, a)} (ψ ⊗ u) = (∂_s ψ) ⊗ u + ψ ⊗ ∂_a u`.
-/

public section

noncomputable section

open LineDeriv
open scoped ContDiff SchwartzMap

namespace SchwartzMap

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The tensor product `(t, x) ↦ ψ t • u x` of a real Schwartz function `ψ` on `D` and a Schwartz
function `u` on `E`, a Schwartz function on `D × E`. -/
def prodSMul (ψ : 𝓢(D, ℝ)) (u : 𝓢(E, F)) : 𝓢(D × E, F) where
  toFun z := ψ z.1 • u z.2
  smooth' := ((ψ.smooth ⊤).comp contDiff_fst).smul ((u.smooth ⊤).comp contDiff_snd)
  decay' k m := by
    refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      (SchwartzMap.seminorm ℝ k i ψ * SchwartzMap.seminorm ℝ 0 (m - i) u +
        SchwartzMap.seminorm ℝ 0 i ψ * SchwartzMap.seminorm ℝ k (m - i) u), fun z => ?_⟩
    have hψ := (ψ.smooth ⊤).comp (ContinuousLinearMap.fst ℝ D E).contDiff
    have hu := (u.smooth ⊤).comp (ContinuousLinearMap.snd ℝ D E).contDiff
    -- The Leibniz rule, and `‖(t, x)‖ ^ k ≤ ‖t‖ ^ k + ‖x‖ ^ k` for the sup norm.
    have hz : ‖z‖ ^ k ≤ ‖z.1‖ ^ k + ‖z.2‖ ^ k := by
      rw [Prod.norm_def]
      rcases le_total ‖z.1‖ ‖z.2‖ with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (by positivity)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (by positivity)
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ m (fun z : D × E => ψ z.1 • u z.2) z‖
        ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (ψ ∘ ContinuousLinearMap.fst ℝ D E) z‖ *
            ‖iteratedFDeriv ℝ (m - i) (u ∘ ContinuousLinearMap.snd ℝ D E) z‖ :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hψ hu z
            (by exact_mod_cast le_top)) (by positivity)
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            (SchwartzMap.seminorm ℝ k i ψ * SchwartzMap.seminorm ℝ 0 (m - i) u +
              SchwartzMap.seminorm ℝ 0 i ψ * SchwartzMap.seminorm ℝ k (m - i) u) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        -- The projections have norm at most one.
        have h₁ := ((ContinuousLinearMap.fst ℝ D E).norm_iteratedFDeriv_comp_right_le (ψ.smooth ⊤) z
          (i := i) (WithTop.coe_le_coe.2 le_top)).trans (mul_le_of_le_one_right (norm_nonneg _)
            (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ D E)))
        have h₂ := ((ContinuousLinearMap.snd ℝ D E).norm_iteratedFDeriv_comp_right_le (u.smooth ⊤) z
          (i := m - i) (WithTop.coe_le_coe.2 le_top)).trans (mul_le_of_le_one_right (norm_nonneg _)
            (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ D E)))
        have a₁ := ψ.le_seminorm ℝ k i z.1
        have a₂ := ψ.le_seminorm ℝ 0 i z.1
        have b₁ := u.le_seminorm ℝ 0 (m - i) z.2
        have b₂ := u.le_seminorm ℝ k (m - i) z.2
        simp only [pow_zero, one_mul] at a₂ b₁
        calc ‖z‖ ^ k * ((m.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (ψ ∘ ContinuousLinearMap.fst ℝ D E) z‖ *
              ‖iteratedFDeriv ℝ (m - i) (u ∘ ContinuousLinearMap.snd ℝ D E) z‖)
            ≤ (‖z.1‖ ^ k + ‖z.2‖ ^ k) * ((m.choose i : ℝ) *
                ‖iteratedFDeriv ℝ i ψ z.1‖ * ‖iteratedFDeriv ℝ (m - i) u z.2‖) := by
              gcongr ?_ * (_ * ?_ * ?_)
              exacts [h₁, h₂]
          _ = (m.choose i : ℝ) *
                ((‖z.1‖ ^ k * ‖iteratedFDeriv ℝ i ψ z.1‖) * ‖iteratedFDeriv ℝ (m - i) u z.2‖ +
                  ‖iteratedFDeriv ℝ i ψ z.1‖ * (‖z.2‖ ^ k * ‖iteratedFDeriv ℝ (m - i) u z.2‖)) := by
              ring
          _ ≤ _ := by gcongr

@[simp]
theorem prodSMul_apply (ψ : 𝓢(D, ℝ)) (u : 𝓢(E, F)) (z : D × E) :
    prodSMul ψ u z = ψ z.1 • u z.2 :=
  (rfl)

theorem coe_prodSMul (ψ : 𝓢(D, ℝ)) (u : 𝓢(E, F)) :
    ⇑(prodSMul ψ u) = fun z : D × E => ψ z.1 • u z.2 :=
  funext (prodSMul_apply ψ u)

@[simp]
theorem zero_prodSMul (u : 𝓢(E, F)) : prodSMul (0 : 𝓢(D, ℝ)) u = 0 := by
  ext z
  simp

@[simp]
theorem prodSMul_zero (ψ : 𝓢(D, ℝ)) : prodSMul ψ (0 : 𝓢(E, F)) = 0 := by
  ext z
  simp

@[simp]
theorem add_prodSMul (ψ φ : 𝓢(D, ℝ)) (u : 𝓢(E, F)) :
    prodSMul (ψ + φ) u = prodSMul ψ u + prodSMul φ u := by
  ext z
  simp [add_smul]

@[simp]
theorem prodSMul_add (ψ : 𝓢(D, ℝ)) (u v : 𝓢(E, F)) :
    prodSMul ψ (u + v) = prodSMul ψ u + prodSMul ψ v := by
  ext z
  simp [smul_add]

@[simp]
theorem smul_prodSMul (c : ℝ) (ψ : 𝓢(D, ℝ)) (u : 𝓢(E, F)) :
    prodSMul (c • ψ) u = c • prodSMul ψ u := by
  ext z
  simp [mul_smul]

@[simp]
theorem prodSMul_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (ψ : 𝓢(D, ℝ)) (c : 𝕜) (u : 𝓢(E, F)) :
    prodSMul ψ (c • u) = c • prodSMul ψ u := by
  ext z
  simp [smul_comm (ψ z.1) c]

/-- **Derivatives of a tensor product.** The directional derivative of `ψ ⊗ u` in the direction
`(s, a)` is `(∂_s ψ) ⊗ u + ψ ⊗ ∂_a u`. -/
@[simp]
theorem lineDerivOp_prodSMul (ψ : 𝓢(D, ℝ)) (u : 𝓢(E, F)) (s : D) (a : E) :
    ∂_{(s, a)} (prodSMul ψ u) = prodSMul (∂_{s} ψ) u + prodSMul ψ (∂_{a} u) := by
  ext z
  have h : HasFDerivAt (fun z : D × E => ψ z.1 • u z.2)
      (ψ z.1 • (fderiv ℝ u z.2).comp (ContinuousLinearMap.snd ℝ D E) +
        ((fderiv ℝ ψ z.1).comp (ContinuousLinearMap.fst ℝ D E)).smulRight (u z.2)) z :=
    (ψ.differentiableAt.hasFDerivAt.comp z hasFDerivAt_fst).smul
      (u.differentiableAt.hasFDerivAt.comp z hasFDerivAt_snd)
  rw [lineDerivOp_apply_eq_fderiv, coe_prodSMul]
  simp [h.fderiv, lineDerivOp_apply_eq_fderiv, add_comm]

end SchwartzMap
