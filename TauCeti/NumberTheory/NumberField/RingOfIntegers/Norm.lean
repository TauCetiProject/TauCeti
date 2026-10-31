/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norms of algebraic integers

The norm `N(α) = Algebra.norm ℚ α` of a nonzero algebraic integer `α` is a nonzero integer, so
`1 ≤ |N(α)|`; equivalently, the product of the absolute values of its complex conjugates is at
least `1`. The norm of a rational integer `m` is `m ^ [K : ℚ]`, so divisibility between
rational integers is the same in `𝓞 K` as in `ℤ`; in particular `𝓞 K / n 𝓞 K` has
characteristic `n`.

## Main results

* `NumberField.RingOfIntegers.one_le_abs_norm`: `1 ≤ |N(α)|` for every nonzero `α : 𝓞 K`.
* `NumberField.RingOfIntegers.one_le_prod_norm_embeddings`: `1 ≤ ∏ σ, |σ α|` over the embeddings
  `σ : K →ₐ[ℚ] ℂ`, for every nonzero `α : 𝓞 K`.
* `NumberField.RingOfIntegers.one_le_norm_mul_pow_of_forall_norm_le`: if every conjugate of a
  nonzero `α : 𝓞 K` has absolute value at most `b`, then `1 ≤ |σ₀ α| b ^ ([K : ℚ] - 1)`.
* `NumberField.RingOfIntegers.intCast_dvd_intCast`: `(m : 𝓞 K) ∣ n ↔ m ∣ n` for `m n : ℤ`.
* `NumberField.RingOfIntegers.natCast_dvd_natCast`: `(m : 𝓞 K) ∣ n ↔ m ∣ n` for `m n : ℕ`.
* `NumberField.RingOfIntegers.charP_quotient_span_natCast`: `𝓞 K / n 𝓞 K` has characteristic `n`.
-/

public section

open scoped NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute value of the norm of a nonzero algebraic integer is at least one. -/
theorem one_le_abs_norm {α : 𝓞 K} (hα : α ≠ 0) :
    (1 : ℝ) ≤ |(Algebra.norm ℚ (α : K) : ℝ)| := by
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hα)

/-- The product of the absolute values of the complex conjugates of a nonzero algebraic integer
is at least one: it is the absolute value of the norm. -/
theorem one_le_prod_norm_embeddings {α : 𝓞 K} (hα : α ≠ 0) :
    1 ≤ ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ := by
  rw [← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ, eq_ratCast, Complex.norm_ratCast]
  exact one_le_abs_norm hα

/-- If every complex conjugate of a nonzero algebraic integer `α` has absolute value at most `b`,
then each conjugate `σ₀ α` is bounded below: `1 ≤ |σ₀ α| b ^ ([K : ℚ] - 1)`. -/
theorem one_le_norm_mul_pow_of_forall_norm_le {α : 𝓞 K} (hα : α ≠ 0) (σ₀ : K →ₐ[ℚ] ℂ) {b : ℝ}
    (hb : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ≤ b) : 1 ≤ ‖σ₀ α‖ * b ^ (Module.finrank ℚ K - 1) := by
  classical
  refine (one_le_prod_norm_embeddings hα).trans ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ σ₀), ← AlgHom.card ℚ K ℂ, ← Finset.card_univ,
    ← Finset.card_erase_of_mem (Finset.mem_univ σ₀), ← Finset.prod_const]
  gcongr with σ
  exact hb σ

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

end NumberField.RingOfIntegers
