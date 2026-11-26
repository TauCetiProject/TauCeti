/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.SplitWitt
import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Determinant
import Mathlib.Analysis.Complex.Basic

/-!
# Regression examples: Witt decomposition of hermitian spaces

These examples exercise the Witt decomposition of signed hermitian spaces:

* over `ℂ/ℝ` the plane `⟨1, 1⟩` is anisotropic, so its Witt index is `0`, while `⟨1, -1⟩` is the
  hyperbolic plane, of Witt index `1`;
* the hyperbolic plane has Gram determinant `-1`;
* over the split algebra `ℚ × ℚ` with the swap, the rank-three space `⟨1, 1, 1⟩` has Witt
  index `1`, not `0` and not `3 / 2`.
-/

open TauCeti SignedHermitianSpace

-- Over `ℂ/ℝ`, the plane `⟨1, 1⟩` is anisotropic (`|x₀|² + |x₁|² = 0` forces `x = 0`), so its
-- Witt index is `0`.
example :
    (diagonal (starRingEnd ℂ) 1 ![1, 1] (fun i ↦ by fin_cases i <;> simp)
      (fun i ↦ by fin_cases i <;> simp)).Anisotropic ∧
    (diagonal (starRingEnd ℂ) 1 ![1, 1] (fun i ↦ by fin_cases i <;> simp)
      (fun i ↦ by fin_cases i <;> simp)).wittIndex = 0 := by
  have hσ : ∃ z : ℂ, starRingEnd ℂ z ≠ z := ⟨Complex.I, by norm_num [Complex.ext_iff]⟩
  have hani : (diagonal (starRingEnd ℂ) 1 ![1, 1] (fun i ↦ by fin_cases i <;> simp)
      (fun i ↦ by fin_cases i <;> simp)).Anisotropic := by
    rintro x ⟨hxx, hx⟩
    have h := congrArg Complex.re hxx
    simp only [diagonal_form_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, Complex.add_re, Complex.zero_re] at h
    rw [Complex.conj_mul', Complex.conj_mul'] at h
    norm_cast at h
    obtain ⟨h₀, h₁⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h
    rw [sq_eq_zero_iff, norm_eq_zero] at h₀ h₁
    exact one_ne_zero (hx 1 (by ext i; fin_cases i <;> simp [h₀, h₁]))
  exact ⟨hani, (wittIndex_eq_zero_iff hσ).2 hani⟩

-- Over `ℂ/ℝ`, `⟨1, -1⟩` is the hyperbolic plane, of Witt index `1`.
example : (diagonal (starRingEnd ℂ) 1 ![1, -1] (fun i ↦ by fin_cases i <;> simp)
    (fun i ↦ by fin_cases i <;> simp)).wittIndex = 1 := by
  have hσ : ∃ z : ℂ, starRingEnd ℂ z ≠ z := ⟨Complex.I, by norm_num [Complex.ext_iff]⟩
  rw [← (equivalent_hyperbolic_diagonal hσ (a := 1) (ε := 1) (by simp)
    one_ne_zero).wittIndex_eq, wittIndex_hyperbolic, Fintype.card_fin]

-- The hyperbolic plane has Gram determinant `-1`.
example : (LinearMap.toMatrix₂ ((Pi.basisFun ℂ (Fin 1)).prod (Pi.basisFun ℂ (Fin 1)))
    ((Pi.basisFun ℂ (Fin 1)).prod (Pi.basisFun ℂ (Fin 1)))
      (hyperbolic ℂ (starRingEnd ℂ) 1 (Fin 1)).form).det = -1 := by
  simp [det_toMatrix₂_hyperbolic]

-- Over `ℚ × ℚ` with the swap, the space `⟨1, 1, 1⟩` has Witt index `⌊3 / 2⌋ = 1`.
example (σ : ℚ × ℚ →+* ℚ × ℚ) [RingHomInvPair σ σ] (hσ : ∀ x, σ x = x.swap) :
    (diagonal σ 1 ![1, 1, 1] (fun i ↦ by fin_cases i <;> simp)
      (fun i ↦ by fin_cases i <;> simp)).wittIndex = 1 := by
  rw [wittIndex_split _ hσ]
  simp
