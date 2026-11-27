/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Contour
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic

/-!
# Shifted Riesz sums of a nonprincipal Dirichlet character

In a zero-free rectangle the only residue encountered in shifting the contour for the
first Riesz sum of `χ(n) Λ(n)` is the one at `s = 1` from the kernel. A bound for `L′/L` on
the rectangle therefore controls the increment of the Riesz sum after its linear term
has been subtracted. The tails on `Re s = 2` have an absolute bound from the Euler product.

The zero-free-box method for the twisted Riesz increment is due here to Levent Alpöge's
formalization of the Riemann hypothesis for Dirichlet L-functions (announced 20 November 2026).
-/

public section

open ArithmeticFunction Complex Set TauCeti
open scoped Real

namespace DirichletCharacter

/-- An upper bound `A` for `|L′/L|` on a zero-free rectangle `[σ,2] × [-T,T]` bounds the
first Riesz increment with its residue term canceled. No primitivity is required. -/
theorem norm_rieszSum_sub_add_mul_logDeriv_le_of_box_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {z η σ T A : ℝ}
    (hz : 1 ≤ z) (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hσ : 0 < σ) (hσ₁ : σ < 1) (hT : 1 ≤ T)
    (hzero : ∀ s ∈ Icc σ 2 ×ℂ Icc (-T) T, χ.LFunction s ≠ 0)
    (hA : ∀ s ∈ Icc σ 2 ×ℂ Icc (-T) T, ‖logDeriv χ.LFunction s‖ ≤ A) :
    let a := fun n : ℕ ↦ χ n * (Λ n : ℂ)
    ‖rieszSum a (z * (1 + η)) - rieszSum a z + (z * η : ℝ) * logDeriv χ.LFunction 1‖ ≤
      (4 * A * η * z ^ σ * Real.log (1 + T / (1 - σ)) +
        (20 * A - 10 * (logDeriv riemannZeta 2).re) * z ^ 2 / T) / (2 * π) := by
  intro a
  have hhol (s : ℂ) (hs : s ∈ Icc σ 2 ×ℂ Icc (-T) T) :
      AnalyticAt ℂ (fun w ↦ -logDeriv χ.LFunction w) s :=
    (((differentiable_LFunction hχ).analyticAt s).logDeriv (hzero s hs)).neg
  have h := norm_rieszSum_sub_sub_mul_le_of_box_bound (a := a)
    (F := fun s ↦ -logDeriv χ.LFunction s) (B := -(logDeriv riemannZeta 2).re)
    hz hη hη₁ hσ hσ₁ hT (LSeriesSummable_twist_vonMangoldt χ (by norm_num))
    (fun s hs ↦ (hhol s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hhol s ⟨Ioo_subset_Icc_self hs.1, Ioo_subset_Icc_self hs.2⟩).differentiableAt
      |>.differentiableWithinAt)
    (fun t ↦ by
      rw [χ.logDeriv_LFunction_eq_neg_LSeries (by simp), neg_neg]
      simp only [a, Pi.mul_def])
    (fun s hs ↦ by simpa only [norm_neg] using hA s hs)
    (fun t _ ↦ by simpa only [norm_neg, ofReal_ofNat] using
      χ.norm_logDeriv_LFunction_le_of_le_re (σ := 2) (s := 2 + t * I) (by norm_num) (by simp))
  simpa only [sub_eq_add_neg, neg_mul, neg_neg, mul_comm (logDeriv χ.LFunction 1), mul_neg] using h

end DirichletCharacter
