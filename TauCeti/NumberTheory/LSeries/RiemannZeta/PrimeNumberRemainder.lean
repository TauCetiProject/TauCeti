/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.SummatoryTail
import TauCeti.NumberTheory.Chebyshev.WeightedError

/-!
# The conductor-one Riesz remainder from the prime number theorem

The Riesz remainder of the trivial primitive Dirichlet character is `-y` times the integral
of `(ψ(t) - t) / t²` above `y`. Its constant term comes from the finite part of the logarithmic
zeta derivative at one. The classical de la Vallée Poussin bound on `ψ(t) - t` then gives
square-root logarithmic exponential decay of the normalized Riesz remainder, unconditionally.

The Riesz normalization is that of Levent Alpöge's `Formalism.Gz` in the formalization of the
Riemann hypothesis for Dirichlet L-functions (<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open ArithmeticFunction Complex Filter MeasureTheory Set
open scoped Chebyshev Topology

namespace TauCeti.PrimitiveDirichletCharacter

/-- The conductor-one Riesz remainder is `-y` times the weighted tail of the Chebyshev error.
The tail is integrable for `y > 0`; at `y = 0` both sides vanish. -/
theorem rieszRemainder_one_eq_neg_mul_integral_psi_sub_div_sq {y : ℝ} (hy : 0 ≤ y) :
    (1 : PrimitiveDirichletCharacter).rieszRemainder y =
      ((-y * ∫ t in Ioi y, (ψ t - t) / t ^ 2 : ℝ) : ℂ) := by
  rw [rieszRemainder_one]
  rcases hy.eq_or_lt with rfl | hy
  · simp
  rcases le_or_gt 1 y with hy₁ | hy₁
  · have h := rieszSum_div_sub_log_eq_integral (fun n ↦ (Λ n : ℂ)) 1 hy₁
    simp only [one_mul, Chebyshev.sum_vonMangoldt_sub_div_sq, integral_complex_ofReal] at h
    rw [← intervalIntegral.integral_of_le hy₁,
      ← intervalIntegral.integral_Ioi_sub_Ioi (Chebyshev.integrableOn_psi_sub_div_sq one_pos) hy₁,
      Chebyshev.integral_psi_sub_div_sq] at h
    push_cast at h ⊢
    linear_combination (norm := (field_simp [hy.ne']; ring)) (y : ℂ) * h
  · have hsmall : (∫ t in y..1, (ψ t - t) / t ^ 2) = Real.log y := by
      rw [intervalIntegral.integral_congr (g := fun t : ℝ ↦ -(t⁻¹)) (fun t ht ↦ ?_),
        intervalIntegral.integral_neg, integral_inv_of_pos hy zero_lt_one, one_div, Real.log_inv,
        neg_neg]
      rw [uIcc_of_le hy₁.le] at ht
      exact Chebyshev.psi_sub_div_sq_eq_neg_inv_of_le_one ht.2
    rw [← intervalIntegral.integral_Ioi_sub_Ioi (Chebyshev.integrableOn_psi_sub_div_sq hy) hy₁.le,
      Chebyshev.integral_psi_sub_div_sq] at hsmall
    rw [rieszSum_eq_zero_of_le_one _ hy₁.le]
    have hsmall' := congrArg Complex.ofReal hsmall
    push_cast at hsmall' ⊢
    linear_combination (y : ℂ) * hsmall'

/-- The principal Riesz remainder satisfies the de la Vallée Poussin type bound
`C * y * exp (-c * √(log y))`, uniformly for `y ≥ 1`. -/
theorem exists_norm_rieszRemainder_one_le_mul_exp_neg_mul_sqrt_log :
    ∃ c > 0, ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y‖ ≤
        C * y * Real.exp (-c * √(Real.log y)) := by
  obtain ⟨c, hc, C, hC, _, htail⟩ := Chebyshev.exists_abs_integral_psi_sub_div_sq_le
  refine ⟨c, hc, C, hC, fun y hy ↦ ?_⟩
  have hy₀ := zero_lt_one.trans_le hy
  rw [rieszRemainder_one_eq_neg_mul_integral_psi_sub_div_sq hy₀.le,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hy₀.le]
  calc
    _ ≤ y * (C * Real.exp (-c * √(Real.log y))) := mul_le_mul_of_nonneg_left (htail y hy) hy₀.le
    _ = _ := by ring

end TauCeti.PrimitiveDirichletCharacter
