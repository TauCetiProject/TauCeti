/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.GaussSum

/-!
# The absolute value of a complex Gauss sum

Let `χ` be a nontrivial multiplicative character and `ψ` a primitive additive character of a
finite field `F`, both with complex values. Mathlib's `gaussSum_mul_gaussSum_eq_card` computes
`g(χ, ψ) g(χ⁻¹, ψ⁻¹) = #F`, and `star_gaussSum_eq` identifies `g(χ⁻¹, ψ⁻¹)` with the complex
conjugate of `g(χ, ψ)`. Together they give the classical absolute value `|g(χ, ψ)| = √#F`.

## Main results

* `TauCeti.norm_gaussSum`: `‖g(χ, ψ)‖ = √#F`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §2,
  Proposition 8.2.2.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F]

/-- **A complex Gauss sum has absolute value `√#F`.** If `χ` is a nontrivial multiplicative
character and `ψ` a primitive additive character of a finite field `F`, both with values in `ℂ`,
then `‖g(χ, ψ)‖ = √#F`. -/
theorem norm_gaussSum {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = √(Fintype.card F) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq, ← starRingEnd_apply, Complex.mul_conj'] at h
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact congrArg Real.sqrt (by exact_mod_cast h)

end TauCeti
