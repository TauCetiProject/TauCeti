/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Norm
public import TauCeti.Analysis.SpecialFunctions.Log.ProdPowDvd
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Norm.Divisibility

/-!
# Norms of algebraic integers

The norm `N(α) = Algebra.norm ℚ α` of a nonzero algebraic integer `α` is a nonzero integer, so
`1 ≤ |N(α)|`. The norm of a rational integer `m` is `m ^ [K : ℚ]`, so divisibility between
rational integers is the same in `𝓞 K` as in `ℤ`; in particular `𝓞 K / n 𝓞 K` has
characteristic `n`.

Divisibility of `a ∈ 𝓞 K` by `(m : 𝓞 K) ^ e` gives `m ^ (finrank ℚ K * e) ∣ Algebra.norm ℤ a`,
the number-field case of `Algebra.pow_finrank_mul_dvd_norm_of_algebraMap_pow_dvd`. The absolute
value of the norm is the product of the absolute values of the complex conjugates, so bounds
`‖σ a‖ ≤ C σ` give `|N(a)| ≤ ∏ σ, C σ`. Finitely many prime powers `p ^ e p` dividing the nonzero
integer `N(a)` give `∑ p ∈ P, e p * log p ≤ log |N(a)|` (`Int.sum_mul_log_le_log_abs`), so a
nonzero algebraic integer with bounded conjugates bounds such a sum of prime logarithms.

## Main results

* `NumberField.RingOfIntegers.one_le_abs_norm`: `1 ≤ |N(α)|` for every nonzero `α : 𝓞 K`.
* `NumberField.RingOfIntegers.dvd_natAbs_norm`: every `α : 𝓞 K` divides `|N(α)|`.
* `NumberField.RingOfIntegers.intCast_dvd_intCast`: `(m : 𝓞 K) ∣ n ↔ m ∣ n` for `m n : ℤ`.
* `NumberField.RingOfIntegers.natCast_dvd_natCast`: `(m : 𝓞 K) ∣ n ↔ m ∣ n` for `m n : ℕ`.
* `NumberField.RingOfIntegers.charP_quotient_span_natCast`: `𝓞 K / n 𝓞 K` has characteristic `n`.
* `NumberField.prod_norm_embedding_eq_abs_norm`: `∏ σ, ‖σ x‖ = |N(x)|` for `x : K`.
* `NumberField.RingOfIntegers.pow_finrank_mul_dvd_norm`: `m ^ (finrank ℚ K * e) ∣ norm ℤ a`
  whenever `(m : 𝓞 K) ^ e ∣ a`.
* `NumberField.abs_norm_le_prod`, `NumberField.abs_norm_le_pow` and their `RingOfIntegers`
  versions: bounds on the norm from bounds on the conjugates.
* `NumberField.RingOfIntegers.sum_mul_log_le_finrank_mul_log`: for nonzero `δ ∈ 𝓞 K` with
  conjugates bounded by `C` and `∏ p ∈ P, p ^ e p ∣ norm δ`, `∑ p ∈ P, e p * log p ≤ n * log C`.

## References

* J. S. Milne, *Algebraic Number Theory*, Chapter 2, p. 31 and Corollary 2.20.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, §10.2.
-/

public section

open Module
open scoped NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute value of the norm of a nonzero algebraic integer is at least one. -/
theorem one_le_abs_norm {α : 𝓞 K} (hα : α ≠ 0) :
    (1 : ℝ) ≤ |(Algebra.norm ℚ (α : K) : ℝ)| := by
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hα)

/-- An element `α` of `𝓞 K` divides the absolute value of its norm. -/
theorem dvd_natAbs_norm (α : 𝓞 K) : α ∣ ((Algebra.norm ℤ α).natAbs : 𝓞 K) := by
  rw [← Ideal.absNorm_span_singleton, ← Ideal.mem_span_singleton]
  exact Ideal.absNorm_mem _

/-- Divisibility between rational integers is the same in `𝓞 K` as in `ℤ`. -/
@[simp, norm_cast]
theorem intCast_dvd_intCast {m n : ℤ} : (m : 𝓞 K) ∣ (n : 𝓞 K) ↔ m ∣ n := by
  refine ⟨fun h ↦ ?_, Int.cast_dvd_cast _ _⟩
  simpa only [Algebra.norm_algebraMap, Int.pow_dvd_pow_iff Module.finrank_pos.ne'] using
    map_dvd (Algebra.norm ℤ) (show algebraMap ℤ (𝓞 K) m ∣ algebraMap ℤ (𝓞 K) n by simpa using h)

/-- Divisibility between natural numbers is the same in `𝓞 K` as in `ℕ`. -/
@[simp, norm_cast]
theorem natCast_dvd_natCast {m n : ℕ} : (m : 𝓞 K) ∣ (n : 𝓞 K) ↔ m ∣ n := by
  simpa using (intCast_dvd_intCast (K := K) (m := m) (n := n)).trans Int.natCast_dvd_natCast

variable (K) in
/-- The residue ring `𝓞 K / n 𝓞 K` has characteristic `n`. -/
instance charP_quotient_span_natCast (n : ℕ) : CharP (𝓞 K ⧸ Ideal.span {(n : 𝓞 K)}) n :=
  ⟨fun m ↦ by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, natCast_dvd_natCast]⟩

/-- If `(m : 𝓞 K) ^ e` divides `a` for an integer `m`, then `m ^ (finrank ℚ K * e)` divides the
integral norm of `a`. -/
theorem pow_finrank_mul_dvd_norm {m : ℤ} {e : ℕ} {a : 𝓞 K} (h : (m : 𝓞 K) ^ e ∣ a) :
    m ^ (finrank ℚ K * e) ∣ Algebra.norm ℤ a := by
  rw [← RingOfIntegers.rank]
  exact Algebra.pow_finrank_mul_dvd_norm_of_algebraMap_pow_dvd (by simpa using h)

end NumberField.RingOfIntegers

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute values of the complex conjugates of `x ∈ K` have product `|N(x)|`. -/
theorem prod_norm_embedding_eq_abs_norm (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |(Algebra.norm ℚ x : ℝ)| := by
  -- Reindex the product by `ℚ`-algebra embeddings, which act on `x` as the ring embeddings do.
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ (fun τ => ‖τ x‖)
    fun σ => by simp [RingHom.equivRatAlgHom_apply]]
  -- The conjugates `τ x` multiply to the field norm, and the complex norm is multiplicative.
  simp [← norm_prod, ← Algebra.norm_eq_prod_embeddings]

/-- If every complex embedding `σ : K →+* ℂ` satisfies `‖σ x‖ ≤ C σ`, then the field norm of `x` has
absolute value at most `∏ σ, C σ`. -/
theorem abs_norm_le_prod (x : K) {C : (K →+* ℂ) → ℝ} (hC : ∀ σ, ‖σ x‖ ≤ C σ) :
    |(Algebra.norm ℚ x : ℝ)| ≤ ∏ σ, C σ := by
  rw [← prod_norm_embedding_eq_abs_norm]
  gcongr with σ
  exact hC σ

/-- If every complex conjugate of `x ∈ K` has absolute value at most `C`, then the field norm of
`x` has absolute value at most `C ^ finrank ℚ K`. -/
theorem abs_norm_le_pow (x : K) {C : ℝ} (hC : ∀ σ : K →+* ℂ, ‖σ x‖ ≤ C) :
    |(Algebra.norm ℚ x : ℝ)| ≤ C ^ finrank ℚ K := by
  simpa [Embeddings.card] using abs_norm_le_prod x hC

namespace RingOfIntegers

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

end RingOfIntegers

end NumberField
