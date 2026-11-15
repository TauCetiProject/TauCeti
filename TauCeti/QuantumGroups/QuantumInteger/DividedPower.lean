/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Factorial
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Quantum divided powers in an algebra over a field

For a parameter `q` in a field `K` and an element `x` of a `K`-algebra `A`, the `r`-th quantum
divided power is `x^(r)_q = ([r]_q!)⁻¹ • x^r`. When `[r]_q! ≠ 0`, these elements satisfy the
divided-power product law `x^(a)_q x^(b)_q = [a + b choose a]_q • x^(a + b)_q` and, for
`q`-commuting summands `y x = q² x y`, the divided-power `q`-binomial expansion
`(x + y)^(n)_q = ∑_{a+b=n} q^(ab) • (x^(a)_q * y^(b)_q)`.

Defining `quantumDividedPower` unconditionally across all field parameters lets the Serre elements
of a quantized enveloping algebra be written uniformly without carrying genericity proofs inside
the presentation.

## Main definitions

* `TauCeti.quantumDividedPower q x r`: the quantum divided power `([r]_q!)⁻¹ • x^r`.

## Main results

* `TauCeti.AlgHomClass.map_quantumDividedPower`: algebra homomorphisms preserve quantum divided
  powers.
* `TauCeti.quantumDividedPower_mul_quantumDividedPower`: the product formula
  `x^(a)_q * x^(b)_q = [a + b choose a]_q • x^(a + b)_q` when `[a + b]_q! ≠ 0`.
* `TauCeti.quantumDividedPower_add`: the antidiagonal `q`-binomial formula for `(x + y)^(n)_q`
  when `y x = q² x y` and `[n]_q! ≠ 0`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.3.
-/

public noncomputable section

open Finset

namespace TauCeti

variable {K A B : Type*} [Field K] [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]

/-- The `r`-th quantum divided power `x^(r)_q = ([r]_q!)⁻¹ • x^r` of an element `x` in a
`K`-algebra. -/
def quantumDividedPower (q : K) (x : A) (r : ℕ) : A :=
  (quantumFactorial q r)⁻¹ • x ^ r

/-- Explicit formula for `quantumDividedPower`. -/
theorem quantumDividedPower_def (q : K) (x : A) (r : ℕ) :
    quantumDividedPower q x r = (quantumFactorial q r)⁻¹ • x ^ r := (rfl)

/-- The zeroth quantum divided power is `1`. -/
@[simp]
theorem quantumDividedPower_zero (q : K) (x : A) : quantumDividedPower q x 0 = 1 := by
  simp [quantumDividedPower_def]

/-- When `q - q⁻¹ ≠ 0`, the first quantum divided power of `x` is `x`. -/
@[simp]
theorem quantumDividedPower_one {q : K} (hq : q - q⁻¹ ≠ 0) (x : A) :
    quantumDividedPower q x 1 = x := by
  simp [quantumDividedPower_def, hq]

/-- Replacing `q` by `q⁻¹` leaves every quantum divided power unchanged. -/
@[simp]
theorem quantumDividedPower_inv (q : K) (x : A) (r : ℕ) :
    quantumDividedPower q⁻¹ x r = quantumDividedPower q x r := by
  simp [quantumDividedPower_def]

/-- For a positive index, the quantum divided power of `0` is `0`. -/
@[simp]
theorem quantumDividedPower_zero_elem (q : K) {r : ℕ} (hr : r ≠ 0) :
    quantumDividedPower q (0 : A) r = 0 := by
  simp [quantumDividedPower_def, zero_pow hr]

/-- Multiplying a quantum divided power by a scalar inside the base scales by `c^r`. -/
theorem quantumDividedPower_smul (q c : K) (x : A) (r : ℕ) :
    quantumDividedPower q (c • x) r = c ^ r • quantumDividedPower q x r := by
  rw [quantumDividedPower_def, quantumDividedPower_def, smul_pow, smul_comm]

/-- Algebra homomorphisms preserve quantum divided powers. -/
@[simp]
theorem AlgHomClass.map_quantumDividedPower {F : Type*} [FunLike F A B] [AlgHomClass F K A B]
    (f : F) (q : K) (x : A) (r : ℕ) :
    f (quantumDividedPower q x r) = quantumDividedPower q (f x) r := by
  simp [quantumDividedPower_def]

/-- In the opposite algebra, `quantumDividedPower` commutes with `MulOpposite.op`. -/
@[simp]
theorem op_quantumDividedPower (q : K) (x : A) (r : ℕ) :
    MulOpposite.op (quantumDividedPower q x r) = quantumDividedPower q (MulOpposite.op x) r := by
  simp [quantumDividedPower_def, MulOpposite.op_pow]

/-- **Product of quantum divided powers**: when `[a + b]_q! ≠ 0`,
`x^(a)_q * x^(b)_q = [a + b choose a]_q • x^(a + b)_q`. -/
theorem quantumDividedPower_mul_quantumDividedPower {q : K} (x : A) {a b : ℕ}
    (hab : quantumFactorial q (a + b) ≠ 0) :
    quantumDividedPower q x a * quantumDividedPower q x b =
      quantumBinomial q (a + b) a • quantumDividedPower q x (a + b) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, quantumDividedPower_def,
    smul_mul_smul_comm, ← pow_add, smul_smul,
    quantumBinomial_eq_div hab (Nat.le_add_right a b), Nat.add_sub_cancel_left]
  congr 1
  rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hab, one_mul, mul_inv]

/-- **Antidiagonal `q`-binomial theorem for divided powers**: if `y * x = q² • (x * y)` and
`[n]_q! ≠ 0`, then `(x + y)^(n)_q = ∑_{a+b=n} q^(ab) • (x^(a)_q * y^(b)_q)`. -/
theorem quantumDividedPower_add {q : K} {x y : A} (h : y * x = q ^ 2 • (x * y)) {n : ℕ}
    (hn : quantumFactorial q n ≠ 0) :
    quantumDividedPower q (x + y) n =
      ∑ p ∈ antidiagonal n,
        q ^ (p.1 * p.2) • (quantumDividedPower q x p.1 * quantumDividedPower q y p.2) := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact inv_quantumFactorial_smul_add_pow h hn

/-- The quantum Serre polynomial `∑_{r+s=N} (-1)^r • (x^(r)_q * y * x^(s)_q)` of length `N` at
parameter `q` in a `K`-algebra. -/
def serreElement (q : K) (N : ℕ) (x y : A) : A :=
  ∑ p ∈ antidiagonal N,
    (-1 : K) ^ p.1 • (quantumDividedPower q x p.1 * y * quantumDividedPower q x p.2)

/-- Explicit sum formula for `serreElement`. -/
theorem serreElement_def (q : K) (N : ℕ) (x y : A) :
    serreElement q N x y =
      ∑ p ∈ antidiagonal N,
        (-1 : K) ^ p.1 • (quantumDividedPower q x p.1 * y * quantumDividedPower q x p.2) :=
  (rfl)

/-- The quantum Serre polynomial vanishes when its middle argument is zero. -/
@[simp]
theorem serreElement_zero_right (q : K) (N : ℕ) (x : A) :
    serreElement q N x 0 = 0 := by
  simp [serreElement_def]

/-- Algebra homomorphisms preserve quantum Serre polynomials. -/
@[simp]
theorem AlgHomClass.map_serreElement {F : Type*} [FunLike F A B] [AlgHomClass F K A B]
    (f : F) (q : K) (N : ℕ) (x y : A) :
    f (serreElement q N x y) = serreElement q N (f x) (f y) := by
  simp [serreElement_def]

/-- The quantum Serre polynomial is additive in its middle argument. -/
theorem serreElement_add_right (q : K) (N : ℕ) (x y₁ y₂ : A) :
    serreElement q N x (y₁ + y₂) = serreElement q N x y₁ + serreElement q N x y₂ := by
  simp [serreElement_def, mul_add, add_mul, smul_add, Finset.sum_add_distrib]

/-- Scaling the arguments of `serreElement q N` by `c₁` and `c₂` scales the polynomial by
`c₁ ^ N * c₂`. -/
theorem serreElement_smul (q c₁ c₂ : K) (N : ℕ) (x y : A) :
    serreElement q N (c₁ • x) (c₂ • y) = (c₁ ^ N * c₂) • serreElement q N x y := by
  rw [serreElement_def, serreElement_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpN : p.1 + p.2 = N := Finset.mem_antidiagonal.mp hp
  simp only [quantumDividedPower_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [← hpN, pow_add]
  ring

/-- At length `1` and `q - q⁻¹ ≠ 0`, the quantum Serre polynomial is the commutator `y * x - x * y`.
-/
theorem serreElement_one {R : Type*} [Ring R] [Algebra K R] {q : K} (hq : q - q⁻¹ ≠ 0)
    (x y : R) : serreElement q 1 x y = y * x - x * y := by
  rw [serreElement_def, Nat.sum_antidiagonal_succ, Nat.antidiagonal_zero]
  simp [quantumDividedPower_one hq, neg_smul, sub_eq_add_neg]

end TauCeti
