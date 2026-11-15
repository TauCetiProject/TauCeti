/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Factorial
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Quantum divided powers and Serre polynomials over a field

For `q` in a field `K` and `x` in a `K`-algebra `A`, we define the quantum divided power
`quantumDividedPower q x r = ([r]_q!)⁻¹ • x^r` and the length-`N` quantum Serre polynomial
`serreElement q N x y = ∑_{r+s=N} (-1)^r • (x^(r)_q * y * x^(s)_q)`, and prove the divided-power
product rule and `q²`-commuting antidiagonal binomial theorem.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §1.3.
* K. McGerty, *Generalized q-Schur algebras and quantum Frobenius*, Adv. Math. 214 (2007), §2.
-/

public noncomputable section

open Finset

namespace TauCeti

variable {K A B : Type*} [Field K] [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]

/-- The `r`-th quantum divided power `x^(r)_q = ([r]_q!)⁻¹ • x^r` in a `K`-algebra. -/
def quantumDividedPower (q : K) (x : A) (r : ℕ) : A := (quantumFactorial q r)⁻¹ • x ^ r

theorem quantumDividedPower_def (q : K) (x : A) (r : ℕ) :
    quantumDividedPower q x r = (quantumFactorial q r)⁻¹ • x ^ r := (rfl)
@[simp] theorem quantumDividedPower_zero (q : K) (x : A) : quantumDividedPower q x 0 = 1 := by
  simp [quantumDividedPower_def]
@[simp] theorem quantumDividedPower_one {q : K} (hq : q - q⁻¹ ≠ 0) (x : A) :
    quantumDividedPower q x 1 = x := by simp [quantumDividedPower_def, hq]
@[simp] theorem quantumDividedPower_inv (q : K) (x : A) (r : ℕ) :
    quantumDividedPower q⁻¹ x r = quantumDividedPower q x r := by simp [quantumDividedPower_def]
@[simp] theorem quantumDividedPower_zero_elem (q : K) {r : ℕ} (hr : r ≠ 0) :
    quantumDividedPower q (0 : A) r = 0 := by simp [quantumDividedPower_def, zero_pow hr]
theorem quantumDividedPower_smul (q c : K) (x : A) (r : ℕ) :
    quantumDividedPower q (c • x) r = c ^ r • quantumDividedPower q x r := by
  rw [quantumDividedPower_def, quantumDividedPower_def, smul_pow, smul_comm]
@[simp] theorem map_quantumDividedPower {F : Type*} [FunLike F A B] [AlgHomClass F K A B]
    (f : F) (q : K) (x : A) (r : ℕ) :
    f (quantumDividedPower q x r) = quantumDividedPower q (f x) r := by
  simp [quantumDividedPower_def]
@[simp] theorem op_quantumDividedPower (q : K) (x : A) (r : ℕ) :
    MulOpposite.op (quantumDividedPower q x r) = quantumDividedPower q (MulOpposite.op x) r := by
  simp [quantumDividedPower_def, MulOpposite.op_pow]

theorem quantumDividedPower_mul_quantumDividedPower {q : K} (x : A) {a b : ℕ}
    (hn : quantumFactorial q (a + b) ≠ 0) :
    quantumDividedPower q x a * quantumDividedPower q x b =
      quantumBinomial q (a + b) a • quantumDividedPower q x (a + b) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, quantumDividedPower_def,
    smul_mul_smul_comm, ← pow_add, smul_smul, quantumBinomial_eq_div hn (Nat.le_add_right a b),
    Nat.add_sub_cancel_left]
  congr 1; rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hn, one_mul, mul_inv]

theorem quantumDividedPower_add {q : K} {a b : A} (hba : b * a = q ^ 2 • (a * b)) {n : ℕ}
    (hn : quantumFactorial q n ≠ 0) :
    quantumDividedPower q (a + b) n =
      ∑ p ∈ antidiagonal n,
        q ^ (p.1 * p.2) • (quantumDividedPower q a p.1 * quantumDividedPower q b p.2) := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact inv_quantumFactorial_smul_add_pow hba hn

/-- The quantum Serre polynomial `∑_{r+s=N} (-1)^r • (x^(r)_q * y * x^(s)_q)`. -/
def serreElement (q : K) (N : ℕ) (x y : A) : A :=
  ∑ p ∈ antidiagonal N,
    (-1 : K) ^ p.1 • (quantumDividedPower q x p.1 * y * quantumDividedPower q x p.2)

theorem serreElement_def (q : K) (N : ℕ) (x y : A) :
    serreElement q N x y = ∑ p ∈ antidiagonal N,
      (-1 : K) ^ p.1 • (quantumDividedPower q x p.1 * y * quantumDividedPower q x p.2) := (rfl)
@[simp] theorem serreElement_zero_right (q : K) (N : ℕ) (x : A) : serreElement q N x 0 = 0 := by
  simp [serreElement_def]
@[simp] theorem map_serreElement {F : Type*} [FunLike F A B] [AlgHomClass F K A B]
    (f : F) (q : K) (N : ℕ) (x y : A) :
    f (serreElement q N x y) = serreElement q N (f x) (f y) := by simp [serreElement_def]
theorem serreElement_add_right (q : K) (N : ℕ) (x y₁ y₂ : A) :
    serreElement q N x (y₁ + y₂) = serreElement q N x y₁ + serreElement q N x y₂ := by
  simp [serreElement_def, mul_add, add_mul, smul_add, sum_add_distrib]
theorem serreElement_smul (q c₁ c₂ : K) (N : ℕ) (x y : A) :
    serreElement q N (c₁ • x) (c₂ • y) = (c₁ ^ N * c₂) • serreElement q N x y := by
  rw [serreElement_def, serreElement_def, smul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  simp only [quantumDividedPower_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← mem_antidiagonal.mp hp, pow_add]; congr 1; ring
theorem serreElement_one {R : Type*} [Ring R] [Algebra K R] {q : K} (hq : q - q⁻¹ ≠ 0)
    (x y : R) : serreElement q 1 x y = y * x - x * y := by
  rw [serreElement_def, Nat.sum_antidiagonal_succ, Nat.antidiagonal_zero]
  simp [quantumDividedPower_one hq, neg_smul, sub_eq_add_neg]
end TauCeti
