/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

import TauCeti.Algebra.MonoidAlgebra.Eigenvector

/-!
# Coefficients of Laurent polynomials

Multiplying a Laurent polynomial on the left by `T n` shifts its coefficients by `n`, and
multiplying it by a constant scales every coefficient. The constant `1` has a single coefficient,
at exponent `0`, and `LaurentPolynomial.trunc` retains every coefficient of nonnegative exponent.
For leading coefficients taken with respect to the degree map `ℤ → WithBot ℤ`, a constant has
its value as leading coefficient, every monomial `T n` has leading coefficient `1`, the inclusion
of ordinary polynomials preserves leading coefficients, and so does multiplication by `T n`. All of
this holds over an arbitrary semiring; only the statement about `invert`, which Mathlib defines
over commutative semirings, needs commutativity.

## Main results

* `LaurentPolynomial.coeff_T_mul`: `(T n * f).coeff d = f.coeff (d - n)`.
* `LaurentPolynomial.T_mul_eq_self_iff`: a nonzero Laurent polynomial is fixed by multiplication
  by `T n` only for `n = 0`.
* `LaurentPolynomial.invert_T_mul_eq_self_iff`: if a nonzero Laurent polynomial `f` is fixed by
  `invert`, then `T n * f` is fixed by `invert` only for `n = 0`.
* `LaurentPolynomial.coeff_C_mul`: constants scale coefficients. For natural-number constants
  this file tags Mathlib's `AddMonoidAlgebra.coeff_natCast_mul` as a `simp` lemma, matching
  `Polynomial.coeff_natCast_mul` and `PowerSeries.coeff_natCast_mul`.
* `LaurentPolynomial.coeff_one`: the coefficients of `1`.
* `LaurentPolynomial.coeff_trunc`: `(trunc f).coeff n = f.coeff (n : ℤ)`.
* `LaurentPolynomial.leadingCoeff_toLaurent` and `LaurentPolynomial.leadingCoeff_mul_T`: the
  polynomial inclusion and multiplication by a Laurent monomial preserve leading coefficients;
  `LaurentPolynomial.leadingCoeff_toLaurent_mul_T` combines them.
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

/-- A Laurent polynomial is fixed by left multiplication by `T n` only when `n = 0` or it is
zero: otherwise its coefficients repeat with period `n`, and its support would be infinite. -/
theorem T_mul_eq_self_iff {n : ℤ} {f : R[T;T⁻¹]} : T n * f = f ↔ n = 0 ∨ f = 0 := by
  refine ⟨fun h => or_iff_not_imp_left.mpr fun hn => ?_, ?_⟩
  · -- `R[T;T⁻¹]` is `AddMonoidAlgebra R ℤ`, in which `T n` is the monomial `single n 1`.
    rw [T_mul, T] at h
    exact TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinAddOrder
      (mt (isOfFinAddOrder_iff_eq_zero n).mp hn) h
  · rintro (rfl | rfl) <;> simp [T_zero]

/-- Left multiplication by a constant scales every coefficient. -/
@[simp]
theorem coeff_C_mul (t : R) (f : R[T;T⁻¹]) (d : ℤ) : (C t * f).coeff d = t * f.coeff d := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_single_zero_mul f t d

-- Natural-number constants scale coefficients too. Mathlib states this for every additive monoid
-- algebra but does not tag it `simp`; tag it so that `simp` normalizes `(↑m * f).coeff d` as it
-- does `(C t * f).coeff d`, and as Mathlib does for polynomials and power series.
attribute [simp] AddMonoidAlgebra.coeff_natCast_mul

/-- The constant Laurent polynomial `1` has coefficient `1` at exponent `0` and `0` elsewhere. -/
@[simp]
theorem coeff_one (d : ℤ) : (1 : R[T;T⁻¹]).coeff d = if d = 0 then 1 else 0 := by
  rw [← map_one (C : R →+* R[T;T⁻¹]), C_apply]

/-- Truncation retains every coefficient of nonnegative exponent. -/
@[simp]
theorem coeff_trunc (f : R[T;T⁻¹]) (n : ℕ) : (trunc f).coeff n = f.coeff (n : ℤ) := (rfl)

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- A Laurent polynomial fixed by `invert` stays fixed by `invert` after multiplication by `T n`
only when `n = 0` or it is zero: `invert (T n * f) = T (-n) * f`, so `T (n + n)` fixes `f`. -/
theorem invert_T_mul_eq_self_iff {n : ℤ} {f : R[T;T⁻¹]} (hf : invert f = f) :
    invert (T n * f) = T n * f ↔ n = 0 ∨ f = 0 := by
  rw [map_mul, invert_T, hf]
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  -- Multiplying `T (-n) * f = T n * f` on the left by `T n` gives `f = T (n + n) * f`.
  have h2 : T (n + n) * f = f := by
    simpa [← mul_assoc, ← T_add] using congr_arg (T n * ·) h.symm
  exact (T_mul_eq_self_iff.mp h2).imp_left (by omega)

end CommSemiring

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
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hc (k : ℕ) : p.toLaurent.coeff (k : ℤ) = p.coeff k := by
    rw [← coeff_trunc, Polynomial.trunc_toLaurent]
  -- The exponent `p.natDegree` is in the support and bounds every exponent of the support.
  have hd : p.toLaurent.supDegree ((↑) : ℤ → WithBot ℤ) = ↑(p.natDegree : ℤ) := by
    refine supDegree_eq_of_isMaxOn ?_ (isMaxOn_iff.mpr fun a ha => ?_)
    · rw [Finsupp.mem_support_iff, hc]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    · rw [support_coeff_toLaurent] at ha
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 ha
      exact WithBot.coe_le_coe.mpr (Nat.cast_le.mpr (Polynomial.le_natDegree_of_mem_supp k hk))
  rw [leadingCoeff, hd, Function.leftInverse_invFun WithBot.coe_injective, hc,
    Polynomial.coeff_natDegree]

/-- Shifting an arbitrary Laurent polynomial preserves its highest coefficient. -/
@[simp]
theorem leadingCoeff_mul_T (f : LaurentPolynomial R) (n : ℤ) :
    (f * T n).leadingCoeff ((↑) : ℤ → WithBot ℤ) =
      f.leadingCoeff ((↑) : ℤ → WithBot ℤ) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support ((↑) : ℤ → WithBot ℤ) hf
  have hc (b : ℤ) : (f * T n).coeff b = f.coeff (b - n) := by
    rw [← T_mul, coeff_T_mul]
  -- The exponent `a + n` is in the support and bounds every exponent of the support.
  have hd : (f * T n).supDegree ((↑) : ℤ → WithBot ℤ) = ↑(a + n) := by
    refine supDegree_eq_of_isMaxOn ?_ (isMaxOn_iff.mpr fun b hb => ?_)
    · simpa [hc] using ha
    · have hle : ((b - n : ℤ) : WithBot ℤ) ≤ ↑a := he ▸ Finset.le_sup (by simpa [hc] using hb)
      exact WithBot.coe_le_coe.mpr (by have := WithBot.coe_le_coe.mp hle; omega)
  simp only [leadingCoeff, hd, he, Function.leftInverse_invFun WithBot.coe_injective _, hc,
    add_sub_cancel_right]

/-- Shifting an ordinary polynomial by any Laurent monomial preserves its leading coefficient. -/
theorem leadingCoeff_toLaurent_mul_T (p : Polynomial R) (n : ℤ) :
    (p.toLaurent * T n).leadingCoeff ((↑) : ℤ → WithBot ℤ) = p.leadingCoeff := by
  rw [leadingCoeff_mul_T, leadingCoeff_toLaurent]

end LeadingCoeff

end LaurentPolynomial
