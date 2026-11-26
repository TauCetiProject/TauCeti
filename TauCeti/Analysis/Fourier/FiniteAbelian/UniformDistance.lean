/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Distance to the uniform distribution through characters

For a function `f` on a finite commutative group `A`, Fourier inversion over the characters
`ψ : A → ℂ` reads

`|A| f(a) = ∑_ψ f̂(ψ) ψ(-a)`, with `f̂(ψ) = ∑_b f(b) ψ(b)`.

The trivial character contributes `f̂(0) = ∑_b f(b)`, so the deviation of `f` from its mean is
carried by the nontrivial characters alone, each value `ψ(-a)` having norm `1`. Summing over `a`
bounds the `ℓ¹` distance from the mean by the total size of the nontrivial Fourier coefficients:

`∑_a ‖f(a) - (∑_b f(b)) / |A|‖ ≤ ∑_{ψ ≠ 0} ‖f̂(ψ)‖`.

For a probability distribution this is an `ℓ¹` distance to the uniform distribution, and it is how
equidistribution on a finite group is proved: bound every nontrivial Fourier coefficient.

## Main results

* `TauCeti.card_mul_eq_sum_addChar`: Fourier inversion, `|A| f(a) = ∑_ψ f̂(ψ) ψ(-a)`.
* `TauCeti.sum_norm_sub_mean_le_sum_norm_fourier`: the `ℓ¹` bound above.

## References

* E. M. Stein and R. Shakarchi, *Fourier Analysis: An Introduction*, Chapter 7, §2, for Fourier
  inversion on a finite abelian group.
-/

public section

namespace TauCeti

open Finset

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- **Fourier inversion on a finite commutative group**:
`|A| f(a) = ∑_ψ (∑_b f(b) ψ(b)) ψ(-a)`, the sum running over the characters `ψ : A → ℂ`. -/
theorem card_mul_eq_sum_addChar (f : A → ℂ) (a : A) :
    (Fintype.card A : ℂ) * f a = ∑ ψ : AddChar A ℂ, (∑ b, f b * ψ b) * ψ (-a) := by
  classical
  simp_rw [sum_mul, mul_assoc, ← AddChar.map_add_eq_mul]
  rw [sum_comm]
  simp_rw [← mul_sum, AddChar.sum_apply_eq_ite, mul_ite, mul_zero, ← sub_eq_add_neg, sub_eq_zero,
    sum_ite_eq', mem_univ, ite_true, mul_comm]

/-- **The `ℓ¹` distance from the mean is bounded by the nontrivial Fourier coefficients**: for
`f` on a finite commutative group,

`∑_a ‖f(a) - (∑_b f(b)) / |A|‖ ≤ ∑_{ψ ≠ 0} ‖∑_b f(b) ψ(b)‖`.

For a probability distribution `f` the left side is the `ℓ¹` distance to the uniform
distribution. -/
theorem sum_norm_sub_mean_le_sum_norm_fourier (f : A → ℂ) :
    ∑ a, ‖f a - (∑ b, f b) / Fintype.card A‖ ≤
      ∑ ψ ∈ univ.erase (0 : AddChar A ℂ), ‖∑ b, f b * ψ b‖ := by
  classical
  -- Each deviation is `|A|⁻¹` times the inversion sum with the trivial character removed.
  have hdev (a : A) : f a - (∑ b, f b) / Fintype.card A =
      (Fintype.card A : ℂ)⁻¹ * ∑ ψ ∈ univ.erase (0 : AddChar A ℂ), (∑ b, f b * ψ b) * ψ (-a) := by
    have h := card_mul_eq_sum_addChar f a
    rw [← add_sum_erase _ _ (mem_univ (0 : AddChar A ℂ))] at h
    simp only [AddChar.zero_apply, mul_one] at h
    field_simp
    linear_combination h
  have hterm (a : A) : ‖f a - (∑ b, f b) / Fintype.card A‖ ≤
      (Fintype.card A : ℝ)⁻¹ * ∑ ψ ∈ univ.erase (0 : AddChar A ℂ), ‖∑ b, f b * ψ b‖ := by
    rw [hdev, norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    refine (norm_sum_le _ _).trans_eq (sum_congr rfl fun ψ _ ↦ ?_)
    rw [norm_mul, AddChar.norm_apply, mul_one]
  refine (sum_le_sum fun a _ ↦ hterm a).trans_eq ?_
  rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

end TauCeti
