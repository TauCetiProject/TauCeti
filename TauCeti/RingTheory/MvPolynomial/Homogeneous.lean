/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Scaling the variables of a homogeneous polynomial

Evaluating a homogeneous polynomial of degree `n` after multiplying every variable by `a`
multiplies its value by `a ^ n`. This permits normalizing linear substitutions without
expanding the polynomial.

The results live in `MvPolynomial.IsHomogeneous`, so a homogeneity proof supports dot
notation such as `hp.eval₂_const_mul`, `hp.aeval_smul`, and `hp.eval_smul`.

The file also records `MvPolynomial.isHomogeneous_coeff_prod_X_sub_C`: the coefficients of a
product of linear factors `X - C Ψ` with homogeneous `Ψ` of degree `m` are homogeneous.
-/

public section

namespace MvPolynomial.IsHomogeneous

/-- Scaling all variables by `a` scales the value of a degree-`n` homogeneous polynomial
by `a ^ n`, after any change of coefficient ring.

This is not a global `simp` lemma: the degree `n` cannot be inferred from its left-hand side. -/
theorem eval₂_const_mul {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (g : σ → S) (a : S) :
    _root_.MvPolynomial.eval₂ f (fun i ↦ a * g i) p =
      a ^ n * _root_.MvPolynomial.eval₂ f g p := by
  classical
  simp only [_root_.MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ i ∈ d.support, d i = n := (hp.degree_eq_sum_deg_support hd).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- Scaling the variables of a homogeneous polynomial by a scalar scales its algebra
evaluation by the corresponding power of that scalar. The scalar algebra may differ
from the coefficient algebra. -/
theorem aeval_smul {σ R S A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A] [Algebra R A] [Algebra S A]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (g : σ → A) (a : S) :
    _root_.MvPolynomial.aeval (a • g) p = a ^ n • _root_.MvPolynomial.aeval g p := by
  rw [Pi.smul_def]
  simpa only [_root_.MvPolynomial.aeval_def, Algebra.smul_def, map_pow] using
    hp.eval₂_const_mul (algebraMap R A) g (algebraMap S A a)

/-- Scaling the variables of a homogeneous polynomial scales its evaluation by the
corresponding power of the scalar. -/
theorem eval_smul {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (g : σ → R) (a : R) :
    _root_.MvPolynomial.eval (a • g) p = a ^ n • _root_.MvPolynomial.eval g p := by
  simpa only [_root_.MvPolynomial.eval, coe_eval₂Hom, Pi.smul_def, smul_eq_mul] using
    hp.eval₂_const_mul (RingHom.id R) g a

end MvPolynomial.IsHomogeneous

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The coefficient of `X ^ k` in a product of linear factors `X - C Ψ`, whose constant terms `Ψ`
are all homogeneous of degree `m`, is homogeneous of degree `m * (s.card - k)`. -/
theorem isHomogeneous_coeff_prod_X_sub_C {ι : Type*} (s : Finset ι)
    (Ψ : ι → MvPolynomial σ R) {m : ℕ} (hΨ : ∀ i ∈ s, (Ψ i).IsHomogeneous m) (k : ℕ) :
    ((∏ i ∈ s, (Polynomial.X - Polynomial.C (Ψ i))).coeff k).IsHomogeneous
      (m * (s.card - k)) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rw [Finset.prod_empty, Polynomial.coeff_one]
    split_ifs
    · simpa using isHomogeneous_one σ R
    · exact isHomogeneous_zero σ R _
  | insert a s ha ih =>
    have hs (k : ℕ) := ih (fun i hi => hΨ i (Finset.mem_insert_of_mem hi)) k
    have ha' := hΨ a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    rcases k with _ | j
    · rw [Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
        Polynomial.coeff_C_zero, zero_sub, Nat.sub_zero, mul_add_one]
      have h0 := hs 0
      rw [Nat.sub_zero] at h0
      exact h0.mul ha'.neg
    · rw [Polynomial.coeff_mul_X_sub_C, Nat.add_sub_add_right]
      refine (hs j).sub ?_
      by_cases hj : j + 1 ≤ s.card
      · have hdeg : s.card - j = s.card - (j + 1) + 1 := by omega
        rw [hdeg, mul_add_one]
        exact (hs (j + 1)).mul ha'
      · have hle : (∏ i ∈ s, (Polynomial.X - Polynomial.C (Ψ i))).natDegree ≤ s.card := by
          refine (Polynomial.natDegree_prod_le _ _).trans ?_
          simpa using Finset.sum_le_card_nsmul s _ 1 fun i _ =>
            Polynomial.natDegree_X_sub_C_le (Ψ i)
        have hlt : (∏ i ∈ s, (Polynomial.X - Polynomial.C (Ψ i))).natDegree < j + 1 := by
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
        exact isHomogeneous_zero σ R _

end MvPolynomial
