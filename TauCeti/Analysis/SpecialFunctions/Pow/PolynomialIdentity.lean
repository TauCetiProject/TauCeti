/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial identities along real powers

A finite sum `∑ i, (μ i ^ t) • c i` with real bases is determined by its values at
natural exponents: if all these values vanish, it vanishes at every real exponent. Repeated
bases are allowed. The proof uses `Polynomial.exists_eval_eq_iff` to interpolate the function
`x ↦ x ^ t` on the finitely many bases, so each real-exponent value is a linear combination of
natural-exponent values.

The same principle applies to polynomial equations in powers of nonnegative real bases and in finite
linear combinations of those powers. In particular, the entries of the real powers of a
positive semidefinite matrix have this form after diagonalization. These results allow polynomial
membership equations valid on all natural powers to extend to real powers.
-/

public section

open scoped BigOperators

namespace Finset

/-- A finite sum of real powers with coefficients in a real module vanishes at every
real exponent if it vanishes at all natural exponents. The bases need not be distinct. -/
theorem sum_rpow_smul_eq_zero_of_forall_pow {ι E : Type*}
    [AddCommMonoid E] [Module ℝ E] (s : Finset ι) (μ : ι → ℝ) (c : ι → E)
    (h : ∀ n : ℕ, ∑ i ∈ s, μ i ^ n • c i = 0) (t : ℝ) :
    ∑ i ∈ s, μ i ^ t • c i = 0 := by
  classical
  obtain ⟨q, hq⟩ := (Polynomial.exists_eval_eq_iff (fun i : s ↦ μ i)
    (fun i : s ↦ μ i ^ t)).2 (fun i j hij ↦ by rw [hij])
  calc
    ∑ i ∈ s, μ i ^ t • c i = ∑ i ∈ s, q.eval (μ i) • c i :=
      Finset.sum_congr rfl fun i hi ↦ congrArg (· • c i) (hq ⟨i, hi⟩).symm
    _ = ∑ k ∈ q.support, q.coeff k • (∑ i ∈ s, μ i ^ k • c i) := by
      simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_smul, mul_smul,
        Finset.smul_sum]
      exact Finset.sum_comm
    _ = 0 := by simp [h]

end Finset

namespace MvPolynomial

/-- A polynomial equation in powers of nonnegative real numbers holds at every real exponent if
it holds at every natural exponent. Coefficients may lie in any commutative real algebra. -/
theorem eval_rpow_eq_zero_of_forall_pow {ι A : Type*} [CommSemiring A] [Algebra ℝ A]
    (p : MvPolynomial ι A) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (h : ∀ n : ℕ, MvPolynomial.eval (fun i ↦ algebraMap ℝ A (μ i ^ n)) p = 0)
    (t : ℝ) : MvPolynomial.eval (fun i ↦ algebraMap ℝ A (μ i ^ t)) p = 0 := by
  classical
  let b (d : ι →₀ ℕ) : ℝ := ∏ i ∈ d.support, μ i ^ d i
  have heval (s : ℝ) :
      MvPolynomial.eval (fun i ↦ algebraMap ℝ A (μ i ^ s)) p =
        ∑ d ∈ p.support, b d ^ s • p.coeff d := by
    rw [MvPolynomial.eval_eq]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Algebra.smul_def, mul_comm]
    congr 1
    dsimp only [b]
    rw [← Real.finsetProd_rpow _ _ (fun i _ ↦ pow_nonneg (hμ i) _) s, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← map_pow, ← Real.rpow_natCast_mul (hμ i),
      ← Real.rpow_mul_natCast (hμ i), mul_comm]
  rw [heval]
  apply Finset.sum_rpow_smul_eq_zero_of_forall_pow
  intro n
  have hn := heval (n : ℝ)
  simp only [Real.rpow_natCast] at hn
  exact hn.symm.trans (h n)

/-- Polynomial equations in finite linear combinations of nonnegative real powers extend from
natural exponents to all real exponents. This includes the spectral expansions of matrix entries. -/
theorem eval_sum_rpow_eq_zero_of_forall_pow {ι σ A : Type*} [Fintype ι]
    [CommSemiring A] [Algebra ℝ A] (p : MvPolynomial σ A) (μ : ι → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (c : σ → ι → A)
    (h : ∀ n : ℕ, MvPolynomial.eval
      (fun j ↦ ∑ i, algebraMap ℝ A (μ i ^ n) * c j i) p = 0) (t : ℝ) :
    MvPolynomial.eval (fun j ↦ ∑ i, algebraMap ℝ A (μ i ^ t) * c j i) p = 0 := by
  classical
  let q : MvPolynomial ι A := p.eval₂ MvPolynomial.C
    (fun j ↦ ∑ i, MvPolynomial.C (c j i) * MvPolynomial.X i)
  have hq (x : ι → A) : MvPolynomial.eval x q =
      MvPolynomial.eval (fun j ↦ ∑ i, x i * c j i) p := by
    simp [q, ← MvPolynomial.eval_assoc, Function.comp_def, mul_comm]
  rw [← hq]
  exact eval_rpow_eq_zero_of_forall_pow q μ hμ (fun n ↦ (hq _).trans (h n)) t

end MvPolynomial
