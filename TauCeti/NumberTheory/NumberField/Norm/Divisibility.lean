/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Norm
public import TauCeti.Analysis.SpecialFunctions.Log.ProdPowDvd
public import TauCeti.RingTheory.Norm.Divisibility

/-!
# Integral norms: scalar divisibility, embedding bounds and prime-sum upper bounds

This file collects the comparisons that turn a nonzero algebraic integer with bounded conjugates,
whose integral norm is divisible by prime powers, into an upper bound for a sum of prime
logarithms; equivalently, the prime powers give a lower bound for the logarithm of the norm.

For a number field `K`, divisibility of `a ∈ 𝓞 K` by `(m : 𝓞 K) ^ e` gives
`m ^ (finrank ℚ K * e) ∣ Algebra.norm ℤ a`, the number-field case of
`Algebra.pow_finrank_mul_dvd_norm_of_algebraMap_pow_dvd`. The integral norm of `a` is the product
of the complex conjugates of `a`, so bounds `‖σ a‖ ≤ C σ` give `|norm a| ≤ ∏ σ, C σ`. On the other
side, finitely many prime powers `p ^ e p` dividing the nonzero integer `norm a` give
`∑ p ∈ P, e p * log p ≤ log |norm a|` (`Int.sum_mul_log_le_log_abs`).

Nonvanishing of the integral norm of a nonzero `a ∈ 𝓞 K` is Mathlib's `Algebra.norm_ne_zero_iff`,
and the field norm as a product over embeddings is Mathlib's `Algebra.norm_eq_prod_embeddings`.

## Main results

* `NumberField.RingOfIntegers.pow_finrank_mul_dvd_norm`: `m ^ (finrank ℚ K * e) ∣ norm ℤ a`
  whenever `(m : 𝓞 K) ^ e ∣ a`.
* `NumberField.RingOfIntegers.intCast_norm_eq_prod_embeddings`: the integral norm as the product
  of the complex conjugates.
* `NumberField.RingOfIntegers.abs_norm_le_prod`, `NumberField.RingOfIntegers.abs_norm_le_pow`:
  bounds on the integral norm from bounds on the conjugates.
* `NumberField.RingOfIntegers.sum_mul_log_le_finrank_mul_log`: for nonzero `δ ∈ 𝓞 K` with
  conjugates bounded by `C` and `∏ p ∈ P, p ^ e p ∣ norm δ`, `∑ p ∈ P, e p * log p ≤ n * log C`.

## References

* J. S. Milne, *Algebraic Number Theory*, Chapter 2, p. 31 and Corollary 2.20.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, §10.2.
-/

public section

open Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- If every complex embedding `σ : K →+* ℂ` satisfies `‖σ x‖ ≤ C σ`, then the field norm of `x` has
absolute value at most `∏ σ, C σ`. -/
theorem abs_norm_le_prod (x : K) {C : (K →+* ℂ) → ℝ} (hC : ∀ σ, ‖σ x‖ ≤ C σ) :
    |(Algebra.norm ℚ x : ℝ)| ≤ ∏ σ, C σ := by
  have h : |(Algebra.norm ℚ x : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖)
      fun _ => rfl, ← norm_prod, ← Algebra.norm_eq_prod_embeddings, eq_ratCast,
      Complex.norm_ratCast]
  rw [h]
  gcongr with σ
  exact hC σ

/-- If every complex conjugate of `x ∈ K` has absolute value at most `C`, then the field norm of
`x` has absolute value at most `C ^ finrank ℚ K`. -/
theorem abs_norm_le_pow (x : K) {C : ℝ} (hC : ∀ σ : K →+* ℂ, ‖σ x‖ ≤ C) :
    |(Algebra.norm ℚ x : ℝ)| ≤ C ^ finrank ℚ K := by
  simpa [Embeddings.card] using abs_norm_le_prod x hC

namespace RingOfIntegers

/-- If `(m : 𝓞 K) ^ e` divides `a` for an integer `m`, then `m ^ (finrank ℚ K * e)` divides the
integral norm of `a`. -/
theorem pow_finrank_mul_dvd_norm {m : ℤ} {e : ℕ} {a : 𝓞 K} (h : (m : 𝓞 K) ^ e ∣ a) :
    m ^ (finrank ℚ K * e) ∣ Algebra.norm ℤ a := by
  rw [← RingOfIntegers.rank]
  exact Algebra.pow_finrank_mul_dvd_norm_of_algebraMap_pow_dvd (by simpa using h)

/-- The integral norm of `a ∈ 𝓞 K` is the product of the complex conjugates of `a`. -/
theorem intCast_norm_eq_prod_embeddings (a : 𝓞 K) :
    ((Algebra.norm ℤ a : ℤ) : ℂ) = ∏ σ : K →ₐ[ℚ] ℂ, σ a := by
  rw [← Algebra.norm_eq_prod_embeddings, ← Algebra.coe_norm_int, eq_ratCast, Rat.cast_intCast]

/-- If every complex embedding `σ : K →+* ℂ` satisfies `‖σ a‖ ≤ C σ`, then the integral norm of `a`
has absolute value at most `∏ σ, C σ`. -/
theorem abs_norm_le_prod (a : 𝓞 K) {C : (K →+* ℂ) → ℝ} (hC : ∀ σ, ‖σ a‖ ≤ C σ) :
    |(Algebra.norm ℤ a : ℝ)| ≤ ∏ σ, C σ := by
  have h : (Algebra.norm ℤ a : ℝ) = (Algebra.norm ℚ (a : K) : ℝ) := by
    rw [← Algebra.coe_norm_int, Rat.cast_intCast]
  exact h ▸ NumberField.abs_norm_le_prod (a : K) hC

/-- If every complex conjugate of `a ∈ 𝓞 K` has absolute value at most `C`, then the integral norm
of `a` has absolute value at most `C ^ finrank ℚ K`. -/
theorem abs_norm_le_pow (a : 𝓞 K) {C : ℝ} (hC : ∀ σ : K →+* ℂ, ‖σ a‖ ≤ C) :
    |(Algebra.norm ℤ a : ℝ)| ≤ C ^ finrank ℚ K := by
  simpa [Embeddings.card] using abs_norm_le_prod a hC

end RingOfIntegers

end NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- If a nonzero `δ ∈ 𝓞 K` has every complex conjugate of absolute value at most `C` and
`∏ p ∈ P, p ^ e p` divides its integral norm, then `∑ p ∈ P, e p * log p ≤ finrank ℚ K * log C`. -/
theorem sum_mul_log_le_finrank_mul_log {δ : 𝓞 K} (hδ : δ ≠ 0) {C : ℝ}
    (hC : ∀ σ : K →+* ℂ, ‖σ δ‖ ≤ C) {P : Finset ℕ} (e : ℕ → ℕ)
    (h : ∏ p ∈ P, (p : ℤ) ^ e p ∣ Algebra.norm ℤ δ) :
    ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ finrank ℚ K * Real.log C := by
  have hz : Algebra.norm ℤ δ ≠ 0 := Algebra.norm_ne_zero_iff.2 hδ
  calc ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ Real.log |(Algebra.norm ℤ δ : ℝ)| :=
        Int.sum_mul_log_le_log_abs e hz h
    _ ≤ Real.log (C ^ finrank ℚ K) :=
        Real.log_le_log (abs_pos.2 (by exact_mod_cast hz)) (abs_norm_le_pow δ hC)
    _ = finrank ℚ K * Real.log C := Real.log_pow _ _

end NumberField.RingOfIntegers
