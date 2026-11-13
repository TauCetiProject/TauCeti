/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Degree
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

/-- Shifting an ordinary polynomial by any Laurent monomial preserves its leading coefficient. -/
theorem leadingCoeff_toLaurent_mul_T (p : Polynomial R) (n : ℤ) :
    (p.toLaurent * T n).leadingCoeff ((↑) : ℤ → WithBot ℤ) = p.leadingCoeff := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  have hc (k : ℕ) : (p.toLaurent * T n).coeff (k + n) = p.coeff k := by
    rw [T, coeff_mul_single_add, mul_one, coeff_toLaurent]
    -- `Polynomial.toLaurent` transports coefficients along `Nat.castEmbedding`.
    -- Expose this representation to apply injectivity at the embedded natural exponent.
    change p.coeff.mapDomain Nat.castEmbedding (Nat.castEmbedding k) = p.coeff k
    rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective]
  have hd : (p.toLaurent * T n).supDegree ((↑) : ℤ → WithBot ℤ) =
      ↑((p.natDegree : ℤ) + n) := by
    apply supDegree_eq_of_max ⟨_, rfl⟩
    · rw [Function.leftInverse_invFun WithBot.coe_injective (_ + n),
        Finsupp.mem_support_iff, hc]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    · intro a ha
      have hcoef := Finsupp.mem_support_iff.1 ha
      rw [← LaurentPolynomial.T_mul, coeff_T_mul] at hcoef
      have hm : a - n ∈ p.support.map Nat.castEmbedding := by
        rw [← support_coeff_toLaurent]
        exact Finsupp.mem_support_iff.2 hcoef
      obtain ⟨k, hk, he⟩ := Finset.mem_map.1 hm
      have hkn := Polynomial.le_natDegree_of_mem_supp k hk
      have he' : (k : ℤ) = a - n := he
      have ha_le : a ≤ (p.natDegree : ℤ) + n := by omega
      exact WithBot.coe_le_coe.mpr ha_le
  rw [leadingCoeff, hd, Function.leftInverse_invFun WithBot.coe_injective (_ + n), hc]
  rfl

end LeadingCoeff

end LaurentPolynomial
