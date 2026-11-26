/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
-- Public: `TauCeti.Algebra.MonoidAlgebra.Basic` tags `AddMonoidAlgebra.coeff_natCast_mul` as a
-- `simp` lemma, and re-exporting it keeps that lemma in the `simp` set of this file's importers.
public import TauCeti.Algebra.MonoidAlgebra.Basic

import TauCeti.Algebra.MonoidAlgebra.Eigenvector

/-!
# Coefficients of Laurent polynomials

Multiplying a Laurent polynomial by `T n` shifts its coefficients by `n`, and
multiplying it by a constant scales every coefficient. The constant `1` has a single coefficient,
at exponent `0`, and `LaurentPolynomial.trunc` retains every coefficient of nonnegative exponent.
For leading coefficients taken with respect to the degree map `ℤ → WithBot ℤ`, a constant has
its value as leading coefficient, every monomial `T n` has leading coefficient `1`, the inclusion
of ordinary polynomials preserves leading coefficients, and so does multiplication by `T n`. All of
this holds over an arbitrary semiring; only the statement about `invert`, which Mathlib defines
over commutative semirings, needs commutativity.

## Main results

* `LaurentPolynomial.coeff_mul_T`: `(f * T n).coeff d = f.coeff (d - n)`.
* `LaurentPolynomial.T_mul_eq_self_iff`: a nonzero Laurent polynomial is fixed by multiplication
  by `T n` only for `n = 0`.
* `LaurentPolynomial.mul_T_eq_mul_T_iff`: cancelling a monomial from both sides of an equation.
* `LaurentPolynomial.invert_T_mul_eq_self_iff`: if a nonzero Laurent polynomial `f` is fixed by
  `invert`, then `T n * f` is fixed by `invert` only for `n = 0`.
* `LaurentPolynomial.eval₂_id_one_eq_sum_coeff`: evaluation at `T = 1` sums the coefficients.
* `LaurentPolynomial.coeff_C_mul`: constants scale coefficients. For natural-number constants
  this is Mathlib's `AddMonoidAlgebra.coeff_natCast_mul`, which
  `TauCeti.Algebra.MonoidAlgebra.Basic` tags as a `simp` lemma.
* `LaurentPolynomial.coeff_C_mul_T`: the coefficients of `a Tⁿ`.
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

/-- Multiplication by `T n` shifts coefficients by `n`. It is stated with `T n` on the right,
where `simp` puts it with `LaurentPolynomial.T_mul`; rewrite a left factor with `T_mul` first.
Low `simp` priority lets `coeff_C_mul` and `AddMonoidAlgebra.coeff_natCast_mul` act first on
scalar multiples of `T n`, preserving the `T_apply` normal form. -/
@[simp low]
theorem coeff_mul_T (f : R[T;T⁻¹]) (n d : ℤ) : (f * T n).coeff d = f.coeff (d - n) := by
  simpa only [T, mul_one, sub_eq_add_neg] using
    AddMonoidAlgebra.coeff_mul_single_apply f (1 : R) n d

/-- A Laurent polynomial is fixed by left multiplication by `T n` only when `n = 0` or it is
zero: otherwise its coefficients repeat with period `n`, and its support would be infinite. -/
theorem T_mul_eq_self_iff {n : ℤ} {f : R[T;T⁻¹]} : T n * f = f ↔ n = 0 ∨ f = 0 := by
  refine ⟨fun h => or_iff_not_imp_left.mpr fun hn => ?_, ?_⟩
  · -- `R[T;T⁻¹]` is `AddMonoidAlgebra R ℤ`, in which `T n` is the monomial `single n 1`.
    rw [T_mul, T] at h
    exact TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinAddOrder
      (mt (isOfFinAddOrder_iff_eq_zero n).mp hn) h
  · rintro (rfl | rfl) <;> simp [T_zero]

/-- Cancelling a monomial: `p * T c' = q * T c` exactly when `p = q * T (c - c')`. -/
theorem mul_T_eq_mul_T_iff {p q : R[T;T⁻¹]} {c c' : ℤ} :
    p * T c' = q * T c ↔ p = q * T (c - c') := by
  refine Iff.trans ?_ (isUnit_T c').mul_left_inj
  rw [mul_assoc q, ← T_add, sub_add_cancel]

/-- Left multiplication by a constant scales every coefficient. -/
@[simp]
theorem coeff_C_mul (t : R) (f : R[T;T⁻¹]) (d : ℤ) : (C t * f).coeff d = t * f.coeff d := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_single_zero_mul f t d

/-- The coefficient of degree `m` of `a Tⁿ` is `a` if `n = m` and `0` otherwise. -/
theorem coeff_C_mul_T (a : R) (n m : ℤ) : (C a * T n).coeff m = if n = m then a else 0 := by
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

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

/-- Evaluating a Laurent polynomial at `T = 1` sums its coefficients. -/
theorem eval₂_id_one_eq_sum_coeff (p : R[T;T⁻¹]) :
    eval₂ (RingHom.id R) 1 p = ∑ n ∈ p.coeff.support, p.coeff n := by
  rw [← Algebra.algebraMap_self, eval₂_eq_smeval, smeval_eq_sum, Finsupp.sum]
  simp

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
  -- Transport `p.degree` along the monotone map `WithBot.map Nat.cast`.
  have hd : p.toLaurent.supDegree ((↑) : ℤ → WithBot ℤ) =
      WithBot.map (Nat.cast : ℕ → ℤ) p.degree := by
    rw [← Polynomial.supDegree_eq_degree, supDegree, supDegree,
      Finset.apply_sup_eq_sup_comp_of_linearOrder (WithBot.map (Nat.cast : ℕ → ℤ))
        Nat.mono_cast.withBot_map (WithBot.map_bot _)]
    simp only [support_coeff_toLaurent, Finset.sup_map, Function.comp_def,
      Nat.castEmbedding_apply, WithBot.map_coe, Polynomial.support]
  rw [leadingCoeff, hd, Polynomial.degree_eq_natDegree hp, Nat.cast_withBot, WithBot.map_coe,
    Function.leftInverse_invFun WithBot.coe_injective, ← coeff_trunc, Polynomial.trunc_toLaurent,
    Polynomial.coeff_natDegree]

/-- Shifting an arbitrary Laurent polynomial preserves its highest coefficient. -/
@[simp]
theorem leadingCoeff_mul_T (f : LaurentPolynomial R) (n : ℤ) :
    (f * T n).leadingCoeff ((↑) : ℤ → WithBot ℤ) =
      f.leadingCoeff ((↑) : ℤ → WithBot ℤ) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  -- Transport `f.supDegree` along the monotone shift `WithBot.map (· + n)`.
  have hd : (f * T n).supDegree ((↑) : ℤ → WithBot ℤ) =
      WithBot.map (· + n) (f.supDegree ((↑) : ℤ → WithBot ℤ)) := by
    rw [supDegree, supDegree,
      Finset.apply_sup_eq_sup_comp_of_linearOrder (WithBot.map (· + n))
        (Monotone.withBot_map fun _ _ h => add_le_add_left h n) (WithBot.map_bot _)]
    simp only [T, support_coeff_mul_single f 1 (by simp) n, Finset.sup_map,
      Function.comp_def, addRightEmbedding_apply, WithBot.map_coe]
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support ((↑) : ℤ → WithBot ℤ) hf
  simp only [leadingCoeff, hd, he, WithBot.map_coe,
    Function.leftInverse_invFun WithBot.coe_injective _, coeff_mul_T, add_sub_cancel_right]

/-- Shifting an ordinary polynomial by any Laurent monomial preserves its leading coefficient. -/
theorem leadingCoeff_toLaurent_mul_T (p : Polynomial R) (n : ℤ) :
    (p.toLaurent * T n).leadingCoeff ((↑) : ℤ → WithBot ℤ) = p.leadingCoeff := by
  rw [leadingCoeff_mul_T, leadingCoeff_toLaurent]

end LeadingCoeff

end LaurentPolynomial
