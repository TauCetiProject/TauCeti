/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.JacobiSum.Basic
public import TauCeti.FieldTheory.Finite.PowerSum
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Absolute value and reduction of Jacobi sums

This file adds two classical facts about Jacobi sums `J(χ, φ)` of multiplicative characters of a
finite field `F` with `q` elements to Mathlib's theory in `Mathlib.NumberTheory.JacobiSum.Basic`.

If `χ`, `φ` and `χ φ` are nontrivial and complex valued, Mathlib's `jacobiSum_mul_jacobiSum_inv`
computes `J(χ, φ) J(χ⁻¹, φ⁻¹) = q`, and `J(χ⁻¹, φ⁻¹)` is the complex conjugate of `J(χ, φ)`
because the values of a character are roots of unity. Hence `|J(χ, φ)| = √q`.

If a ring homomorphism `f` from the coefficient ring to `F` reduces `χ` and `φ` to the power maps
`x ↦ x ^ a` and `x ↦ x ^ b`, then `f (J(χ, φ)) = ∑ x, x ^ a (1 - x) ^ b`, which vanishes when
`a + b < q - 1`. For the power residue characters of a prime `P` of a number field this says that
`P` divides the Jacobi sum, which together with the absolute value identifies the Jacobi sum of the
cubic and quartic residue characters with a generator of `P`.

## Main results

* `TauCeti.norm_jacobiSum`: `‖J(χ, φ)‖ = √q` for complex characters with `χ`, `φ`, `χ φ`
  nontrivial.
* `TauCeti.map_jacobiSum_eq_zero`: `f (J(χ, φ)) = 0` when `f ∘ χ` and `f ∘ φ` are the power maps
  `x ↦ x ^ a` and `x ↦ x ^ b` with `a + b < q - 1`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §3,
  Theorem 1 and the proof of Proposition 8.3.4.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F]

/-- **A complex Jacobi sum has absolute value `√#F`.** If `χ`, `φ` and `χ φ` are nontrivial
multiplicative characters of a finite field `F` with values in `ℂ`, then `‖J(χ, φ)‖ = √#F`. -/
theorem norm_jacobiSum {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ = √(Fintype.card F) := by
  have h := jacobiSum_mul_jacobiSum_inv
    (by simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm) hχ hφ hχφ
  rw [← MulChar.star_eq_inv, ← MulChar.star_eq_inv] at h
  have hstar : jacobiSum (star χ) (star φ) = starRingEnd ℂ (jacobiSum χ φ) := by
    simp [jacobiSum, map_sum]
  rw [hstar, Complex.mul_conj'] at h
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact congrArg Real.sqrt (by exact_mod_cast h)

/-- **Reduction of a Jacobi sum to a power sum.** Let `χ` and `φ` be multiplicative characters of
a finite field `F` with values in a commutative ring `R`, and `f : R →+* F` a ring homomorphism
with `f (χ x) = x ^ a` and `f (φ x) = x ^ b` for all `x`. If `a + b < #F - 1`, then
`f (J(χ, φ)) = 0`. -/
theorem map_jacobiSum_eq_zero {R : Type*} [CommRing R] {χ φ : MulChar F R} (f : R →+* F)
    {a b : ℕ} (hχ : ∀ x, f (χ x) = x ^ a) (hφ : ∀ x, f (φ x) = x ^ b)
    (hab : a + b < Fintype.card F - 1) :
    f (jacobiSum χ φ) = 0 := by
  simp only [jacobiSum, map_sum, map_mul, hχ, hφ]
  exact FiniteField.sum_pow_mul_one_sub_pow_eq_zero hab

end TauCeti
