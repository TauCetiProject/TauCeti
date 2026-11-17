/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Factorial
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Quantum divided powers and denominator-free quantum Serre polynomials

We define the quantum divided power `quantumDividedPower q x r = ([r]_q!)⁻¹ • x^r` over a field `K`
(vanishing by Lean's total inverse `0⁻¹ = 0` when `[r]_q! = 0`) and prove its product rule and
`q²`-commuting antidiagonal binomial theorem under `[n]_q! ≠ 0`.

Over any commutative ring `K` with `Inv K`, we define the **denominator-free** quantum Serre
polynomial `serreElement q N x y = ∑_{r+s=N} ((-1)^r * [N choose r]_q) • (x^r * y * x^s)`. It stays
faithful at roots of unity where `[N]_q! = 0` (e.g. `q^2 = -1` gives `x^2 * y + y * x^2`), agrees
with the classical adjoint Serre polynomial at `q = 1`, and equals `[N]_q!` times the divided-power
sum whenever `[N]_q! ≠ 0` (`serreElement_eq_quantumFactorial_smul_dividedPower`).

## References
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §1.3.
* K. McGerty, *Generalized q-Schur algebras and quantum Frobenius*, Adv. Math. 214 (2007), §2.
-/

public section
open Finset
namespace TauCeti

section DividedPower
variable {K A B : Type*} [Field K] [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]

/-- The `r`-th quantum divided power `x^(r)_q = ([r]_q!)⁻¹ • x^r` in a `K`-algebra (vanishing when
`quantumFactorial q r = 0` by Lean's total inverse convention `0⁻¹ = 0`). -/
noncomputable def quantumDividedPower (q : K) (x : A) (r : ℕ) : A :=
  (quantumFactorial q r)⁻¹ • x ^ r
theorem quantumDividedPower_def (q : K) (x : A) (r : ℕ) :
    quantumDividedPower q x r = (quantumFactorial q r)⁻¹ • x ^ r := (rfl)
@[simp] theorem quantumDividedPower_zero (q : K) (x : A) :
    quantumDividedPower q x 0 = 1 := by simp [quantumDividedPower_def]
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

/-- Multiplication law `x^(a)_q * x^(b)_q = [a + b choose a]_q • x^(a + b)_q` for `[a+b]_q! ≠ 0`. -/
theorem quantumDividedPower_mul_quantumDividedPower {q : K} (x : A) {a b : ℕ}
    (hn : quantumFactorial q (a + b) ≠ 0) :
    quantumDividedPower q x a * quantumDividedPower q x b =
      quantumBinomial q (a + b) a • quantumDividedPower q x (a + b) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, quantumDividedPower_def,
    smul_mul_smul_comm, ← pow_add, smul_smul, quantumBinomial_eq_div hn (Nat.le_add_right a b),
    Nat.add_sub_cancel_left]
  congr 1; rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hn, one_mul, mul_inv]

/-- Divided-power `q`-binomial theorem for `b * a = q² • (a * b)` when `[n]_q! ≠ 0`. -/
theorem quantumDividedPower_add {q : K} {a b : A} (hba : b * a = q ^ 2 • (a * b)) {n : ℕ}
    (hn : quantumFactorial q n ≠ 0) :
    quantumDividedPower q (a + b) n = ∑ p ∈ antidiagonal n,
      q ^ (p.1 * p.2) • (quantumDividedPower q a p.1 * quantumDividedPower q b p.2) := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]; exact inv_quantumFactorial_smul_add_pow hba hn
end DividedPower

section SerreElement
variable {K A B : Type*} [CommRing K] [Inv K] [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]

/-- The denominator-free quantum Serre polynomial
`∑_{r+s=N} ((-1)^r * [N choose r]_q) • (x^r * y * x^s)`. -/
def serreElement (q : K) (N : ℕ) (x y : A) : A :=
  ∑ p ∈ antidiagonal N, ((-1 : K) ^ p.1 * quantumBinomial q N p.1) • (x ^ p.1 * y * x ^ p.2)
theorem serreElement_def (q : K) (N : ℕ) (x y : A) :
    serreElement q N x y = ∑ p ∈ antidiagonal N,
      ((-1 : K) ^ p.1 * quantumBinomial q N p.1) • (x ^ p.1 * y * x ^ p.2) := (rfl)
@[simp] theorem serreElement_zero (q : K) (x y : A) :
    serreElement q 0 x y = y := by simp [serreElement_def]
@[simp] theorem serreElement_zero_right (q : K) (N : ℕ) (x : A) :
    serreElement q N x 0 = 0 := by simp [serreElement_def]
@[simp] theorem map_serreElement {F : Type*} [FunLike F A B] [AlgHomClass F K A B]
    (f : F) (q : K) (N : ℕ) (x y : A) :
    f (serreElement q N x y) = serreElement q N (f x) (f y) := by simp [serreElement_def]
theorem serreElement_add_right (q : K) (N : ℕ) (x y₁ y₂ : A) :
    serreElement q N x (y₁ + y₂) = serreElement q N x y₁ + serreElement q N x y₂ := by
  simp [serreElement_def, mul_add, add_mul, smul_add, sum_add_distrib]
theorem serreElement_smul (q c₁ c₂ : K) (N : ℕ) (x y : A) :
    serreElement q N (c₁ • x) (c₂ • y) = (c₁ ^ N * c₂) • serreElement q N x y := by
  rw [serreElement_def, serreElement_def, smul_sum]; refine sum_congr rfl fun p hp ↦ ?_
  simp only [smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← mem_antidiagonal.mp hp, pow_add]; congr 1; ring
/-- The length-1 quantum Serre polynomial is `y * x - x * y`, unconditionally. -/
theorem serreElement_one {R : Type*} [Ring R] [Algebra K R] (q : K) (x y : R) :
    serreElement q 1 x y = y * x - x * y := by
  rw [serreElement_def, Nat.sum_antidiagonal_succ, Nat.antidiagonal_zero]
  simp [neg_smul, sub_eq_add_neg]
/-- The length-2 quantum Serre polynomial is `x^2 * y - (q + q⁻¹) • (x * y * x) + y * x^2`. -/
theorem serreElement_two {R : Type*} [Ring R] [Algebra K R] (q : K) (x y : R) :
    serreElement q 2 x y = x ^ 2 * y - (q + q⁻¹) • (x * y * x) + y * x ^ 2 := by
  have h21 : quantumBinomial q 2 1 = q + q⁻¹ := by simp [quantumBinomial_succ_succ]
  rw [serreElement_def, Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ, Nat.antidiagonal_zero]
  simp [h21, sub_eq_add_neg, add_comm, add_left_comm, ← neg_smul]
end SerreElement

section SerreElementField
variable {K A : Type*} [Field K] [Semiring A] [Algebra K A]

@[simp] theorem serreElement_inv (q : K) (N : ℕ) (x y : A) :
    serreElement q⁻¹ N x y = serreElement q N x y := by simp [serreElement_def]
/-- When `q^2 = -1` (e.g. `q = i ∈ ℂ`), `serreElement q 2 x y = x^2 * y + y * x^2`. -/
theorem serreElement_two_of_sq_eq_neg_one {R : Type*} [Ring R] [Algebra K R] {q : K}
    (hq : q ^ 2 = -1) (x y : R) : serreElement q 2 x y = x ^ 2 * y + y * x ^ 2 := by
  have hinv : q⁻¹ = -q := inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← sq, hq, neg_neg])
  simp [serreElement_two, hinv]
/-- When `[N]_q! ≠ 0`, `serreElement q N x y` equals `[N]_q!` times the divided-power Serre sum. -/
theorem serreElement_eq_quantumFactorial_smul_dividedPower {q : K} {N : ℕ}
    (hN : quantumFactorial q N ≠ 0) (x y : A) :
    serreElement q N x y = quantumFactorial q N • ∑ p ∈ antidiagonal N,
      (-1 : K) ^ p.1 • (quantumDividedPower q x p.1 * y * quantumDividedPower q x p.2) := by
  rw [serreElement_def, smul_sum]; refine sum_congr rfl fun p hp ↦ ?_
  have hps := mem_antidiagonal.mp hp
  simp only [quantumDividedPower_def, smul_mul_assoc, mul_smul_comm, smul_smul]; congr 1
  rw [quantumBinomial_eq_div hN (by omega : p.1 ≤ N), ← hps, Nat.add_sub_cancel_left,
    div_eq_mul_inv, mul_inv]; ring
/-- When `[N]_q! ≠ 0`, rescaling `serreElement` by `([N]_q!)⁻¹` gives the divided-power sum. -/
theorem inv_quantumFactorial_smul_serreElement {q : K} {N : ℕ} (hN : quantumFactorial q N ≠ 0)
    (x y : A) : (quantumFactorial q N)⁻¹ • serreElement q N x y = ∑ p ∈ antidiagonal N,
      (-1 : K) ^ p.1 • (quantumDividedPower q x p.1 * y * quantumDividedPower q x p.2) := by
  rw [serreElement_eq_quantumFactorial_smul_dividedPower hN, smul_smul, inv_mul_cancel₀ hN,
    one_smul]
end SerreElementField
end TauCeti
