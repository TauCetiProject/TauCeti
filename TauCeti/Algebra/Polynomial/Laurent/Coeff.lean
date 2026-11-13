/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Coefficients of Laurent polynomials

Multiplying a Laurent polynomial on the left by `T n` shifts its coefficients by `n`, and
multiplying it by a constant, in particular by a natural number, scales every coefficient. The
constant `1` has a single coefficient, at exponent `0`, and `LaurentPolynomial.trunc` retains
every coefficient of nonnegative exponent. These hold over an arbitrary semiring.

## Main results

* `LaurentPolynomial.coeff_T_mul`: `(T n * f).coeff d = f.coeff (d - n)`.
* `LaurentPolynomial.coeff_C_mul` and `LaurentPolynomial.coeff_natCast_mul`: constants scale
  coefficients.
* `LaurentPolynomial.coeff_one`: the coefficients of `1`.
* `LaurentPolynomial.coeff_trunc`: `(trunc f).coeff n = f.coeff (n : ℤ)`.
* `LaurentPolynomial.leadingCoeff_toLaurent_mul_T`: multiplication by a Laurent monomial
  preserves the leading coefficient of an ordinary polynomial.
-/

public section

namespace LaurentPolynomial

section Semiring

variable {R : Type*} [Semiring R]

/-- Left multiplication by `T n` shifts coefficients by `n`. This is not a `simp` lemma: `simp`
moves `T n` to the right with `LaurentPolynomial.T_mul`. -/
theorem coeff_T_mul (n : ℤ) (f : R[T;T⁻¹]) (d : ℤ) : (T n * f).coeff d = f.coeff (d - n) := by
  simpa only [T, one_mul, sub_eq_add_neg, add_comm] using
    AddMonoidAlgebra.coeff_single_mul_apply f (1 : R) n d

/-- Left multiplication by a constant scales every coefficient. -/
@[simp]
theorem coeff_C_mul (t : R) (f : R[T;T⁻¹]) (d : ℤ) : (C t * f).coeff d = t * f.coeff d := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_single_zero_mul f t d

/-- Left multiplication by a natural number scales every coefficient. -/
@[simp]
theorem coeff_natCast_mul (m : ℕ) (f : R[T;T⁻¹]) (d : ℤ) :
    ((m : R[T;T⁻¹]) * f).coeff d = m * f.coeff d := by
  rw [← map_natCast (C : R →+* R[T;T⁻¹]) m, coeff_C_mul]

/-- The constant Laurent polynomial `1` has coefficient `1` at exponent `0` and `0` elsewhere. -/
@[simp]
theorem coeff_one (d : ℤ) : (1 : R[T;T⁻¹]).coeff d = if d = 0 then 1 else 0 := by
  rw [← map_one (C : R →+* R[T;T⁻¹]), C_apply]

/-- Truncation retains every coefficient of nonnegative exponent. -/
@[simp]
theorem coeff_trunc (f : R[T;T⁻¹]) (n : ℕ) : (trunc f).coeff n = f.coeff (n : ℤ) := (rfl)

end Semiring

section LeadingCoeff

open AddMonoidAlgebra

variable {R : Type*} [Semiring R]

/-- The leading coefficient of a constant is its value. -/
@[simp]
theorem leadingCoeff_C (r : R) :
    (C r).leadingCoeff ((↑) : ℤ → WithBot ℤ) = r := by
  rw [← single_eq_C]
  exact leadingCoeff_single WithBot.coe_injective 0 r

/-- A Laurent monomial has leading coefficient one, over every semiring. -/
@[simp]
theorem leadingCoeff_T (n : ℤ) :
    (T n : LaurentPolynomial R).leadingCoeff ((↑) : ℤ → WithBot ℤ) = 1 := by
  rw [T, leadingCoeff_single WithBot.coe_injective]

/-- The polynomial inclusion preserves its leading coefficient. -/
@[simp]
theorem leadingCoeff_toLaurent (p : Polynomial R) :
    p.toLaurent.leadingCoeff ((↑) : ℤ → WithBot ℤ) = p.leadingCoeff := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  have hc (k : ℕ) : p.toLaurent.coeff (k : ℤ) = p.coeff k := by
    rw [← coeff_trunc, Polynomial.trunc_toLaurent]
  have hd : p.toLaurent.supDegree ((↑) : ℤ → WithBot ℤ) = ↑(p.natDegree : ℤ) := by
    apply supDegree_eq_of_max ⟨_, rfl⟩
    · rw [Function.leftInverse_invFun WithBot.coe_injective (p.natDegree : ℤ),
        Finsupp.mem_support_iff, hc]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    · intro a ha
      rw [support_coeff_toLaurent] at ha
      obtain ⟨k, hk, he⟩ := Finset.mem_map.1 ha
      rw [Nat.castEmbedding_apply] at he
      have hkn := Polynomial.le_natDegree_of_mem_supp k hk
      exact WithBot.coe_le_coe.mpr (by omega)
  rw [leadingCoeff, hd,
    Function.leftInverse_invFun WithBot.coe_injective (p.natDegree : ℤ), hc]
  rfl

/-- Shifting an arbitrary Laurent polynomial preserves its highest coefficient. -/
@[simp]
theorem leadingCoeff_mul_T (f : LaurentPolynomial R) (n : ℤ) :
    (f * T n).leadingCoeff ((↑) : ℤ → WithBot ℤ) =
      f.leadingCoeff ((↑) : ℤ → WithBot ℤ) := by
  by_cases hf : f = 0
  · simp [hf]
  classical
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support ((↑) : ℤ → WithBot ℤ) hf
  have hc (b : ℤ) : (f * T n).coeff (b + n) = f.coeff b := by
    rw [T, coeff_mul_single_add, mul_one]
  have hd : (f * T n).supDegree ((↑) : ℤ → WithBot ℤ) = ↑(a + n) := by
    apply supDegree_eq_of_max ⟨_, rfl⟩
    · rw [Function.leftInverse_invFun WithBot.coe_injective (a + n),
        Finsupp.mem_support_iff, hc]
      exact Finsupp.mem_support_iff.mp ha
    · intro b hb
      have hcoef := Finsupp.mem_support_iff.mp hb
      rw [← T_mul, coeff_T_mul] at hcoef
      have hb' : b - n ∈ f.coeff.support := Finsupp.mem_support_iff.mpr hcoef
      have hle : ((b - n : ℤ) : WithBot ℤ) ≤ ↑a := he ▸ Finset.le_sup hb'
      exact WithBot.coe_le_coe.mpr (by have := WithBot.coe_le_coe.mp hle; omega)
  rw [leadingCoeff, hd, Function.leftInverse_invFun WithBot.coe_injective (a + n),
    hc, leadingCoeff, he, Function.leftInverse_invFun WithBot.coe_injective a]

/-- Shifting an ordinary polynomial by any Laurent monomial preserves its leading coefficient. -/
theorem leadingCoeff_toLaurent_mul_T (p : Polynomial R) (n : ℤ) :
    (p.toLaurent * T n).leadingCoeff ((↑) : ℤ → WithBot ℤ) = p.leadingCoeff := by
  rw [leadingCoeff_mul_T, leadingCoeff_toLaurent]

end LeadingCoeff

end LaurentPolynomial
