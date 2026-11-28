/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import TauCeti.NumberTheory.Chebyshev.Mertens.WeightedTail
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
  have hfloor : y ∈ Icc (⌊y⌋₊ : ℝ) (⌊y⌋₊ + 1) :=
    ⟨Nat.floor_le hy.le, (Nat.lt_floor_add_one y).le⟩
  have hIcc : Finset.Icc 1 ⌊y⌋₊ = Finset.Ioc 0 ⌊y⌋₊ := by
    simpa only [zero_add] using Finset.Icc_add_one_left_eq_Ioc 0 ⌊y⌋₊
  rw [rieszSum_eq_sum_mul_sub_sum_of_mem_Icc _ hfloor, hIcc]
  have hpsi : ψ y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n := by
    rw [Chebyshev.psi_eq_sum_Icc, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
    simp
  have hψ := congrArg Complex.ofReal hpsi
  have h := congrArg Complex.ofReal
    (Chebyshev.sum_vonMangoldt_div_eq_log_sub_eulerMascheroniConstant_add hy)
  push_cast at h hψ ⊢
  rw [← hψ]
  linear_combination (norm := (field_simp [hy.ne']; ring)) (y : ℂ) * h

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
