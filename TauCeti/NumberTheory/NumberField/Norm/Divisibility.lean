/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Integral norms: scalar divisibility, embedding bounds and prime-sum lower bounds

This file collects the comparisons that turn a nonzero algebraic integer, divisible by a rational
scalar power and with bounded conjugates, into a lower bound for a sum of prime logarithms.

For a free algebra `S` of rank `n` over `R`, divisibility of `a` by `algebraMap R S r ^ e` gives
`r ^ (n * e) ∣ Algebra.norm R a`. For a number field `K`, the integral norm of `a ∈ 𝓞 K` is the
product of the complex conjugates of `a`, so bounds `‖σ a‖ ≤ C σ` give `|norm a| ≤ ∏ σ, C σ`. On
the other side, finitely many prime powers `p ^ e p` dividing a nonzero integer `z` give
`∑ p ∈ P, e p * log p ≤ log |z|`.

Nonvanishing of the integral norm of a nonzero `a ∈ 𝓞 K` is Mathlib's `Algebra.norm_ne_zero_iff`,
and the field norm as a product over embeddings is Mathlib's `Algebra.norm_eq_prod_embeddings`.

## Main results

* `Algebra.pow_finrank_mul_dvd_norm_of_algebraMap_pow_dvd`: `r ^ (finrank R S * e) ∣ norm R a`
  whenever `algebraMap R S r ^ e ∣ a`.
* `NumberField.RingOfIntegers.pow_finrank_mul_dvd_norm`: `m ^ (finrank ℚ K * e) ∣ norm ℤ a`
  whenever `(m : 𝓞 K) ^ e ∣ a`.
* `NumberField.RingOfIntegers.intCast_norm_eq_prod_embeddings`: the integral norm as the product
  of the complex conjugates.
* `NumberField.RingOfIntegers.abs_norm_le_prod`, `NumberField.RingOfIntegers.abs_norm_le_pow`:
  bounds on the integral norm from bounds on the conjugates.
* `Finset.prod_primes_pow_dvd`: prime powers dividing `z` combine to their product.
* `Int.sum_mul_log_le_log_abs`: `∑ p ∈ P, e p * log p ≤ log |z|` when `∏ p ∈ P, p ^ e p ∣ z ≠ 0`.
* `NumberField.RingOfIntegers.sum_mul_log_le_finrank_mul_log`: for nonzero `δ ∈ 𝓞 K` with
  conjugates bounded by `C` and `∏ p ∈ P, p ^ e p ∣ norm δ`, `∑ p ∈ P, e p * log p ≤ n * log C`.

## References

* J. S. Milne, *Algebraic Number Theory*, Chapter 2, p. 31 and Corollary 2.20.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, §10.2.
-/

public section

open Module

namespace Algebra

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] [Free R S]

/-- If `algebraMap R S r` divides `a` in a free `R`-algebra `S`, then `r ^ finrank R S` divides the
norm of `a`. -/
theorem pow_finrank_dvd_norm_of_algebraMap_dvd {r : R} {a : S} (h : algebraMap R S r ∣ a) :
    r ^ finrank R S ∣ norm R a := by
  simpa using map_dvd (norm R) h

/-- If `algebraMap R S r ^ e` divides `a` in a free `R`-algebra `S`, then `r ^ (finrank R S * e)`
divides the norm of `a`. -/
theorem pow_finrank_mul_dvd_norm_of_algebraMap_pow_dvd {r : R} {e : ℕ} {a : S}
    (h : algebraMap R S r ^ e ∣ a) : r ^ (finrank R S * e) ∣ norm R a := by
  rw [mul_comm, pow_mul]
  exact pow_finrank_dvd_norm_of_algebraMap_dvd (by simpa using h)

end Algebra

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

/-- If `(p : R) ^ e p` divides `z` for each prime `p` in a finite set `P`, then so does the product
`∏ p ∈ P, (p : R) ^ e p`: distinct primes give pairwise coprime prime powers. -/
theorem Finset.prod_primes_pow_dvd {R : Type*} [CommRing R] {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℕ) {z : R} (h : ∀ p ∈ P, (p : R) ^ e p ∣ z) :
    ∏ p ∈ P, (p : R) ^ e p ∣ z :=
  Finset.prod_dvd_of_coprime (fun p hp q hq hpq =>
    (((Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq).cast).pow) h

/-- If `∏ p ∈ P, p ^ e p` divides a nonzero integer `z`, then `∑ p ∈ P, e p * log p ≤ log |z|`. -/
theorem Int.sum_mul_log_le_log_abs {P : Finset ℕ} (e : ℕ → ℕ) {z : ℤ} (hz : z ≠ 0)
    (h : ∏ p ∈ P, (p : ℤ) ^ e p ∣ z) :
    ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ Real.log |(z : ℝ)| := by
  have hd : ∏ p ∈ P, (p : ℤ) ^ e p ≠ 0 := ne_zero_of_dvd_ne_zero hz h
  have hle : ∏ p ∈ P, (p : ℝ) ^ e p ≤ |(z : ℝ)| := by
    exact_mod_cast Int.le_of_dvd (abs_pos.2 hz) ((dvd_abs _ _).2 h)
  have hpos : 0 < ∏ p ∈ P, (p : ℝ) ^ e p :=
    (Finset.prod_nonneg fun _ _ => by positivity).lt_of_ne' (by exact_mod_cast hd)
  calc ∑ p ∈ P, (e p : ℝ) * Real.log p = Real.log (∏ p ∈ P, (p : ℝ) ^ e p) := by
        rw [Real.log_prod fun p hp => (Finset.prod_ne_zero_iff.1 hpos.ne' p hp)]
        simp [Real.log_pow]
    _ ≤ Real.log |(z : ℝ)| := Real.log_le_log hpos hle

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
