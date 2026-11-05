/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Norm

/-!
# Norms of algebraic integers

The norm `N(α) = Algebra.norm ℚ α` of a nonzero algebraic integer `α` is a nonzero integer, so
`1 ≤ |N(α)|`. The norm of a rational integer `m` is `m ^ [K : ℚ]`, so divisibility between
rational integers is the same in `𝓞 K` as in `ℤ`; in particular `𝓞 K / n 𝓞 K` has
characteristic `n`.

## Main results

* `NumberField.RingOfIntegers.one_le_abs_norm`: `1 ≤ |N(α)|` for every nonzero `α : 𝓞 K`.
* `NumberField.RingOfIntegers.intCast_dvd_intCast`: `(m : 𝓞 K) ∣ n ↔ m ∣ n` for `m n : ℤ`.
* `NumberField.RingOfIntegers.natCast_dvd_natCast`: `(m : 𝓞 K) ∣ n ↔ m ∣ n` for `m n : ℕ`.
* `NumberField.RingOfIntegers.isUnit_intCast`: `IsUnit (m : 𝓞 K) ↔ IsUnit m` for `m : ℤ`.
* `NumberField.RingOfIntegers.isCoprime_intCast`: `IsCoprime (m : 𝓞 K) (n : 𝓞 K) ↔ IsCoprime m n`
  for `m n : ℤ`.
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

/-- A rational integer is a unit in `𝓞 K` if and only if it is a unit in `ℤ`. -/
@[simp, norm_cast]
theorem isUnit_intCast {m : ℤ} : IsUnit (m : 𝓞 K) ↔ IsUnit m := by
  rw [isUnit_iff_dvd_one, ← Int.cast_one (R := 𝓞 K), intCast_dvd_intCast, ← isUnit_iff_dvd_one]

/-- Coprimality between rational integers is the same in `𝓞 K` as in `ℤ`. -/
@[simp, norm_cast]
theorem isCoprime_intCast {m n : ℤ} : IsCoprime (m : 𝓞 K) (n : 𝓞 K) ↔ IsCoprime m n := by
  refine ⟨fun h ↦ Int.isCoprime_iff_gcd_eq_one.mpr ?_, IsCoprime.intCast⟩
  have hu : IsUnit ((m.gcd n : ℤ) : 𝓞 K) :=
    h.isUnit_of_dvd' (intCast_dvd_intCast.mpr (Int.gcd_dvd_left m n))
      (intCast_dvd_intCast.mpr (Int.gcd_dvd_right m n))
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp (isUnit_iff_dvd_one.mp (isUnit_intCast.mp hu)))

variable (K) in
/-- The residue ring `𝓞 K / n 𝓞 K` has characteristic `n`. -/
instance charP_quotient_span_natCast (n : ℕ) : CharP (𝓞 K ⧸ Ideal.span {(n : 𝓞 K)}) n :=
  ⟨fun m ↦ by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, natCast_dvd_natCast]⟩

end NumberField.RingOfIntegers
