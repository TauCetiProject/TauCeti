/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.LowOrder
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Topology.MetricSpace.Holder

/-!
# The sine function in the bounded Hölder spaces `C_b^{k,α}(ℝ)`

The sine function is the basic calibrating element of the spaces `C_b^{k,α}(ℝ)` of bounded `C^k`
maps with bounded derivatives and globally `α`-Hölder `k`-th derivative
(`TauCeti.CkHolderSpace`), whose norm is the sum norm

`‖f‖ = ∑_{i ≤ k} ‖Dⁱf‖_∞ + [Dᵏf]_α`.

Every derivative of `sin` is `±sin` or `±cos`. So each supremum norm equals `1`, and the `α`-Hölder
seminorm of `Dᵏ sin` lies between `2 / π^α` and `2^(1 - α)` for `0 ≤ α ≤ 1`. The upper bound
interpolates between the Lipschitz bound `|Dᵏ sin x - Dᵏ sin y| ≤ |x - y|` and the oscillation
bound `2`. The lower bound is the difference quotient between two points at distance `π`, where
`Dᵏ sin` takes opposite values of absolute value `1`. Hence `sin ∈ C_b^{k,α}(ℝ)` with norm
`k + 1 + [Dᵏ sin]_α`, which is at most `k + 3` and exceeds `k + 2` as soon as `π^α < 2`.

At `k = 1` the space `C_b^{1,α}(ℝ)` is identified with `TauCeti.C1HolderSpace`, whose norm is the
maximum `max(‖f‖_∞, ‖f'‖_∞ + [f']_α)` rather than the sum. The two norms are equivalent with
constants `1` and `2` (`TauCeti.CkHolderSpace.norm_equivC1HolderSpace_le`,
`TauCeti.CkHolderSpace.norm_le_two_mul_norm_equivC1HolderSpace`), and the sine function shows they
are never equal: its sum norm is its `C1HolderSpace` norm plus one. By the bounds above, for
`α = 1/2` the sum norm lies between `2 + 2 / √π` and `2 + √2`, and the maximum norm between
`1 + 2 / √π` and `1 + √2`.

By contrast `x ↦ x²` lies in no `C_b^{k,α}(ℝ)`, since it is unbounded.

## Main declarations

* `TauCeti.holderWith_iteratedFDeriv_sin`, `TauCeti.nnHolderNorm_iteratedFDeriv_sin_le`,
  `TauCeti.two_div_pi_rpow_le_nnHolderNorm_iteratedFDeriv_sin`: the Hölder bounds for `Dᵏ sin`.
* `TauCeti.CkHolderSpace.exists_coe_eq_sin`: `sin ∈ C_b^{k,α}(ℝ)` for `α ≤ 1`.
* `TauCeti.CkHolderSpace.norm_eq_of_coe_eq_sin`: its norm is `k + 1 + [Dᵏ sin]_α`.
* `TauCeti.CkHolderSpace.norm_le_add_three_of_coe_eq_sin`,
  `TauCeti.CkHolderSpace.add_two_lt_norm_of_coe_eq_sin`: the norm is at most `k + 3`, and exceeds
  `k + 2` when `π^α < 2`.
* `TauCeti.CkHolderSpace.norm_eq_norm_equivC1HolderSpace_add_one_of_coe_eq_sin`: at `k = 1` the
  sum norm of `sin` is its `C1HolderSpace` norm plus one.
* `TauCeti.CkHolderSpace.not_exists_coe_eq_sq`: `x ↦ x²` is not in `C_b^{k,α}(ℝ)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1 (the Hölder spaces and their norms).
-/

public section

noncomputable section

open Real
open scoped NNReal

namespace TauCeti

variable {α : ℝ≥0}

/-- For `α ≤ 1`, every iterated derivative of `sin` is `α`-Hölder with constant `2^(1 - α)`: it is
`1`-Lipschitz and its values lie in `[-1, 1]`. -/
theorem holderWith_iteratedFDeriv_sin (hα : α ≤ 1) (k : ℕ) :
    HolderWith ((2 : ℝ≥0) ^ (1 - (α : ℝ))) α (iteratedFDeriv ℝ k sin) := by
  rw [iteratedFDeriv_eq_equiv_comp, (LinearIsometryEquiv.isometry _).holderWith_comp_iff]
  have h₁ : HolderWith 1 1 (iteratedDeriv k sin) :=
    holderWith_one.2 (lipschitzWith_iteratedDeriv_sin k)
  have h₀ : HolderWith (2 * 1) 0 (iteratedDeriv k sin) :=
    holderWith_zero_of_nnnorm_le fun x ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, NNReal.coe_one]
      exact abs_iteratedDeriv_sin_le_one k x
  have h := h₁.interpolate h₀ (add_tsub_cancel_of_le hα)
  simpa [NNReal.coe_sub hα] using h

/-- For `α ≤ 1`, the `α`-Hölder seminorm of every iterated derivative of `sin` is at most
`2^(1 - α)`. -/
theorem nnHolderNorm_iteratedFDeriv_sin_le (hα : α ≤ 1) (k : ℕ) :
    (nnHolderNorm α (iteratedFDeriv ℝ k sin) : ℝ) ≤ 2 ^ (1 - (α : ℝ)) := by
  have h := (holderWith_iteratedFDeriv_sin hα k).nnholderNorm_le
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow, NNReal.coe_ofNat] at h
  exact h

/-- For `α ≤ 1`, the `α`-Hölder seminorm of every iterated derivative of `sin` is at least
`2 / π^α`: at two points at distance `π` the derivative takes opposite values of absolute
value `1`. -/
theorem two_div_pi_rpow_le_nnHolderNorm_iteratedFDeriv_sin (hα : α ≤ 1) (k : ℕ) :
    2 / π ^ (α : ℝ) ≤ nnHolderNorm α (iteratedFDeriv ℝ k sin) := by
  set C := nnHolderNorm α (iteratedFDeriv ℝ k sin)
  have hC : HolderWith C α (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ ∘
      iteratedDeriv k sin) := by
    rw [← iteratedFDeriv_eq_equiv_comp]
    exact (holderWith_iteratedFDeriv_sin hα k).memHolder.holderWith
  obtain ⟨x, hx⟩ := exists_abs_iteratedDeriv_sin_eq_one k
  have h := ((LinearIsometryEquiv.isometry _).holderWith_comp_iff.1 hC).dist_le (x + π) x
  -- The values at `x + π` and `x` are `-c` and `c` with `|c| = 1`, at distance `π`.
  rw [Real.dist_eq, Real.dist_eq, iteratedDeriv_sin_add_pi, add_sub_cancel_left,
    abs_of_pos pi_pos] at h
  rw [div_le_iff₀ (by positivity)]
  calc (2 : ℝ) = |-iteratedDeriv k sin x - iteratedDeriv k sin x| := by
        rw [neg_sub_left, abs_neg, ← two_mul, abs_mul, hx, abs_two, mul_one]
    _ ≤ C * π ^ (α : ℝ) := h

namespace CkHolderSpace

variable {k : ℕ}

/-- For `α ≤ 1`, the sine function is a bounded `C^{k,α}` map on `ℝ` for every `k`. -/
theorem exists_coe_eq_sin (hα : α ≤ 1) : ∃ f : CkHolderSpace k α ℝ ℝ, ⇑f = sin :=
  ⟨ofContDiff sin contDiff_sin (fun i _ ↦ ⟨1, fun x ↦ by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact abs_iteratedDeriv_sin_le_one i x⟩)
    (holderWith_iteratedFDeriv_sin hα k).memHolder, coe_ofContDiff _ _ _ _⟩

/-- Every derivative field of `sin` in `C_b^{k,α}(ℝ)` has supremum norm `1`. -/
theorem norm_iteratedFDeriv_eq_one_of_coe_eq_sin {f : CkHolderSpace k α ℝ ℝ} (hf : ⇑f = sin)
    (i : Fin (k + 1)) : ‖f.iteratedFDeriv i‖ = 1 := by
  have hval (x : ℝ) : ‖f.iteratedFDeriv i x‖ = |iteratedDeriv i sin x| := by
    rw [coe_iteratedFDeriv, hf, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  refine le_antisymm ((BoundedContinuousFunction.norm_le zero_le_one).2 fun x ↦ ?_) ?_
  · rw [hval]
    exact abs_iteratedDeriv_sin_le_one i x
  · obtain ⟨x, hx⟩ := exists_abs_iteratedDeriv_sin_eq_one i
    rw [← hx, ← hval]
    exact (f.iteratedFDeriv i).norm_coe_le_norm x

/-- The `C^{k,α}` norm of `sin` is `k + 1 + [Dᵏ sin]_α`: each of the `k + 1` supremum norms is
`1`. -/
theorem norm_eq_of_coe_eq_sin {f : CkHolderSpace k α ℝ ℝ} (hf : ⇑f = sin) :
    ‖f‖ = k + 1 + nnHolderNorm α (_root_.iteratedFDeriv ℝ k sin) := by
  rw [norm_eq, hf]
  simp [norm_iteratedFDeriv_eq_one_of_coe_eq_sin hf]

/-- For `α ≤ 1`, the `C^{k,α}` norm of `sin` is at most `k + 3`. -/
theorem norm_le_add_three_of_coe_eq_sin (hα : α ≤ 1) {f : CkHolderSpace k α ℝ ℝ}
    (hf : ⇑f = sin) : ‖f‖ ≤ k + 3 := by
  have h : (2 : ℝ) ^ (1 - (α : ℝ)) ≤ 2 ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by simp)
  rw [norm_eq_of_coe_eq_sin hf]
  linarith [nnHolderNorm_iteratedFDeriv_sin_le hα k, Real.rpow_one (2 : ℝ)]

/-- The `C^{k,α}` norm of `sin` exceeds `k + 2` when `π^α < 2`, that is for small `α`. -/
theorem add_two_lt_norm_of_coe_eq_sin (hα : π ^ (α : ℝ) < 2) {f : CkHolderSpace k α ℝ ℝ}
    (hf : ⇑f = sin) : k + 2 < ‖f‖ := by
  have hα₁ : α ≤ 1 := by
    by_contra h
    have : π ^ (1 : ℝ) < π ^ (α : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith [two_le_pi]) (by exact_mod_cast not_le.1 h)
    rw [Real.rpow_one] at this
    linarith [two_le_pi]
  have h : 1 < 2 / π ^ (α : ℝ) := by
    rw [one_lt_div (by positivity)]
    exact hα
  rw [norm_eq_of_coe_eq_sin hf]
  linarith [two_div_pi_rpow_le_nnHolderNorm_iteratedFDeriv_sin hα₁ k]

/-- At `k = 1` the sum norm of `sin` is its `C1HolderSpace` norm plus one. So the sum norm of
`C_b^{1,α}(ℝ)` and the maximum norm of `C1HolderSpace` are never equal on `sin`, although they are
equivalent with constants `1` and `2`. -/
theorem norm_eq_norm_equivC1HolderSpace_add_one_of_coe_eq_sin {f : CkHolderSpace 1 α ℝ ℝ}
    (hf : ⇑f = sin) : ‖f‖ = ‖equivC1HolderSpace f‖ + 1 := by
  have hbcf : C1HolderSpace.toBoundedContinuousFunction (equivC1HolderSpace f) =
      f.toBoundedContinuousFunction := BoundedContinuousFunction.ext fun x ↦ by
    rw [C1HolderSpace.toBoundedContinuousFunction_apply, equivC1HolderSpace_apply,
      coe_toBoundedContinuousFunction]
  have hA : ‖C1HolderSpace.toBoundedContinuousFunction (equivC1HolderSpace f)‖ = 1 := by
    rw [hbcf, norm_toBoundedContinuousFunction, norm_iteratedFDeriv_eq_one_of_coe_eq_sin hf]
  -- The smaller of the two terms is the supremum norm `1`, since the other is at least `1`.
  have hnorm := norm_eq_of_coe_eq_sin hf
  rw [Nat.cast_one] at hnorm
  have hmin := norm_eq_norm_equivC1HolderSpace_add_min f
  rw [hA, min_eq_left] at hmin
  · exact hmin
  · linarith [norm_eq_norm_add_norm_fderiv f,
      (nnHolderNorm α (_root_.iteratedFDeriv ℝ 1 sin)).coe_nonneg]

/-- The function `x ↦ x²` is not a bounded `C^{k,α}` map on `ℝ`, being unbounded. -/
theorem not_exists_coe_eq_sq : ¬∃ f : CkHolderSpace k α ℝ ℝ, ⇑f = fun x ↦ x ^ 2 := by
  rintro ⟨f, hf⟩
  have h := f.norm_apply_le (‖f‖ + 1)
  rw [hf, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  nlinarith [norm_nonneg f]

end CkHolderSpace

end TauCeti
