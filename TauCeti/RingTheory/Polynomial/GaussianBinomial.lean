/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
public import TauCeti.Algebra.Ring.QPochhammer
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Gaussian polynomials and Gaussian binomial coefficients

The Gaussian polynomial `[n k] ∈ ℕ[t]` is defined by the successor recursion
`[n+1 k+1] = [n k] + t^(k+1) [n k+1]`, with `[n 0] = 1` and `[0 k+1] = 0`, and the Gaussian
binomial coefficient `[n k]_t` is its evaluation at an element `t` of a semiring. Defining the
coefficient by evaluating a polynomial with natural coefficients keeps every identity
denominator-free: it holds over every commutative (semi)ring, in particular at roots of unity, in
positive characteristic, and at the integer `q` counting the elements of a finite field.

The polynomial identities are proved without division. Over a commutative ring the coefficient
satisfies `[n k]_t (t;t)_k = ∏_{i<k} (1 - t^(n-i))`, where `(t;t)_k = ∏_{i<k} (1 - t^(i+1))` is
the q-Pochhammer product `TauCeti.qPochhammer t t k`, and for `k ≤ n` the factorial form
`[n k]_t (t;t)_k (t;t)_(n-k) = (t;t)_n`. Over a field these give the classical quotient formula
`[n k]_t = ∏_{i=1}^{k} (1 - t^(n-k+i)) / (1 - t^i)` for `k ≤ n`, whenever its denominators are
nonzero. The factorial form, applied in the domain `ℤ[t]`, gives the symmetry
`[n n-k] = [n k]`.

The Gaussian coefficient is the non-symmetric normalization of `TauCeti.quantumBinomial`; the
comparison is in `TauCeti.QuantumGroups.QuantumInteger.Gaussian`.

## Main definitions

* `TauCeti.gaussianPoly n k`: the Gaussian polynomial `[n k] ∈ ℕ[t]`.
* `TauCeti.gaussianBinomial t n k`: the Gaussian binomial coefficient `[n k]_t`, the value of
  `gaussianPoly n k` at `t`.

## Main results

* `TauCeti.gaussianBinomial_succ_succ`, `TauCeti.gaussianBinomial_succ_succ'`: the successor
  recursion and its mirror image.
* `TauCeti.gaussianBinomial_eq_zero_of_lt`, `TauCeti.gaussianBinomial_self`: `[n k]_t = 0` for
  `n < k`, and `[n n]_t = 1`.
* `TauCeti.gaussianBinomial_one`: `[n k]_1 = n.choose k`.
* `TauCeti.gaussianBinomial_symm`: `[n n-k]_t = [n k]_t` for `k ≤ n`.
* `TauCeti.gaussianBinomial_mul_qPochhammer` and
  `TauCeti.gaussianBinomial_mul_qPochhammer_mul_qPochhammer`: the denominator-free product
  formulas.
* `TauCeti.gaussianBinomial_eq_prod_div`: the quotient formula over a field.
* `TauCeti.prod_one_add_pow_mul_eq_sum_gaussianBinomial`: **Cauchy's `q`-binomial theorem**
  `∏_{i<n} (1 + t^i z) = ∑_{k ≤ n} t^(k(k-1)/2) [n k]_t z^k` over every commutative semiring.
* `TauCeti.gaussianBinomial_add_succ_eq_sum`: the column recursion
  `[e+j+1 j+1]_t = ∑_{i ≤ e} t^i [i+j j]_t`.
* `TauCeti.gaussianBinomial_add_le_pow`, `TauCeti.gaussianBinomial_add_le_succ_pow_mul_pow`: the
  bounds `[e+j j]_q ≤ q^(e(j+1))` for `q ≥ 2` and `[e+j j]_q ≤ (e+1)^j q^(ej)` for `q ≥ 1`, at a
  natural number `q`.

## References

* R. P. Stanley, *Enumerative Combinatorics, Volume 1*, 2nd ed., Section 1.7 (Gaussian
  coefficients, their recursion and polynomiality) and Section 1.8 (the `q`-binomial theorem).
* G. Gasper and M. Rahman, *Basic Hypergeometric Series*, 2nd ed., Section 1.3.
-/

public section

open Finset Polynomial

namespace TauCeti

/-- The **Gaussian polynomial** `[n k] ∈ ℕ[t]`, defined by `[n 0] = 1`, `[0 k+1] = 0` and the
successor recursion `[n+1 k+1] = [n k] + t^(k+1) [n k+1]`. -/
noncomputable def gaussianPoly : ℕ → ℕ → ℕ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussianPoly n k + X ^ (k + 1) * gaussianPoly n (k + 1)

/-- `[n 0] = 1`. -/
@[simp]
theorem gaussianPoly_zero_right (n : ℕ) : gaussianPoly n 0 = 1 := by
  cases n <;> rfl

/-- `[0 k+1] = 0`. -/
theorem gaussianPoly_zero_succ (k : ℕ) : gaussianPoly 0 (k + 1) = 0 := (rfl)

/-- The successor recursion `[n+1 k+1] = [n k] + t^(k+1) [n k+1]`. -/
theorem gaussianPoly_succ_succ (n k : ℕ) :
    gaussianPoly (n + 1) (k + 1) = gaussianPoly n k + X ^ (k + 1) * gaussianPoly n (k + 1) :=
  (rfl)

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The **Gaussian binomial coefficient** `[n k]_t`: the Gaussian polynomial `[n k]` evaluated at
an element `t` of a semiring. -/
noncomputable def gaussianBinomial (t : R) (n k : ℕ) : R :=
  aeval t (gaussianPoly n k)

/-- `[n k]_t` is the value of the Gaussian polynomial `[n k]` at `t`. -/
theorem gaussianBinomial_def (t : R) (n k : ℕ) :
    gaussianBinomial t n k = aeval t (gaussianPoly n k) :=
  (rfl)

/-- Evaluating the Gaussian polynomial at the variable returns it. -/
@[simp]
theorem gaussianBinomial_X (n k : ℕ) : gaussianBinomial (X : ℕ[X]) n k = gaussianPoly n k :=
  aeval_X_left_apply _

/-- `[n 0]_t = 1`. -/
@[simp]
theorem gaussianBinomial_zero_right (t : R) (n : ℕ) : gaussianBinomial t n 0 = 1 := by
  simp [gaussianBinomial_def]

/-- `[0 k+1]_t = 0`. -/
theorem gaussianBinomial_zero_succ (t : R) (k : ℕ) : gaussianBinomial t 0 (k + 1) = 0 := by
  simp [gaussianBinomial_def, gaussianPoly_zero_succ]

/-- The successor recursion `[n+1 k+1]_t = [n k]_t + t^(k+1) [n k+1]_t`. -/
theorem gaussianBinomial_succ_succ (t : R) (n k : ℕ) :
    gaussianBinomial t (n + 1) (k + 1) =
      gaussianBinomial t n k + t ^ (k + 1) * gaussianBinomial t n (k + 1) := by
  simp [gaussianBinomial_def, gaussianPoly_succ_succ]

/-- `[n k]_t = 0` for `n < k`. -/
@[simp]
theorem gaussianBinomial_eq_zero_of_lt (t : R) {n k : ℕ} (h : n < k) :
    gaussianBinomial t n k = 0 := by
  induction n generalizing k with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero h.ne'
    exact gaussianBinomial_zero_succ t k
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : k ≠ 0)
    rw [gaussianBinomial_succ_succ, ih (by omega), ih (by omega), mul_zero, add_zero]

/-- `[n n]_t = 1`. -/
@[simp]
theorem gaussianBinomial_self (t : R) (n : ℕ) : gaussianBinomial t n n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [gaussianBinomial_succ_succ, ih, gaussianBinomial_eq_zero_of_lt t n.lt_succ_self,
      mul_zero, add_zero]

/-- `[n k] = 0` for `n < k`. -/
@[simp]
theorem gaussianPoly_eq_zero_of_lt {n k : ℕ} (h : n < k) : gaussianPoly n k = 0 := by
  rw [← gaussianBinomial_X, gaussianBinomial_eq_zero_of_lt _ h]

/-- `[n n] = 1`. -/
@[simp]
theorem gaussianPoly_self (n : ℕ) : gaussianPoly n n = 1 := by
  rw [← gaussianBinomial_X, gaussianBinomial_self]

/-- At `t = 1` the Gaussian binomial coefficient is the binomial coefficient. -/
@[simp]
theorem gaussianBinomial_one (n k : ℕ) : gaussianBinomial (1 : R) n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [gaussianBinomial_succ_succ, ih, Nat.choose_succ_succ]

/-- Semiring homomorphisms commute with Gaussian binomial coefficients. -/
@[simp]
theorem map_gaussianBinomial {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (t : R)
    (n k : ℕ) : f (gaussianBinomial t n k) = gaussianBinomial (f t) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [gaussianBinomial_succ_succ, ih]

/-- The image of the Gaussian polynomial `[n k] ∈ ℕ[t]` under a coefficient map `ℕ →+* R` is the
Gaussian binomial coefficient `[n k]_t` at the variable of `R[t]`. -/
@[simp]
theorem map_gaussianPoly (f : ℕ →+* R) (n k : ℕ) :
    (gaussianPoly n k).map f = gaussianBinomial (X : R[X]) n k := by
  rw [← gaussianBinomial_X, ← coe_mapRingHom, map_gaussianBinomial, coe_mapRingHom, map_X]

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

/-- The denominator-free product formula `[n k]_t (t;t)_k = ∏_{i<k} (1 - t^(n-i))`, where
`(t;t)_k = ∏_{i<k} (1 - t^(i+1))`, valid for all `n` and `k` over every commutative ring: for
`k > n` both sides vanish. -/
theorem gaussianBinomial_mul_qPochhammer (t : R) (n k : ℕ) :
    gaussianBinomial t n k * qPochhammer t t k = ∏ i ∈ range k, (1 - t ^ (n - i)) := by
  rw [qPochhammer_self]
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [prod_range_succ']
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have e₁ := ih k
      have e₂ := ih (k + 1)
      rw [prod_range_succ, prod_range_succ] at e₂
      rw [gaussianBinomial_succ_succ, prod_range_succ, prod_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      rcases le_or_gt k n with hkn | hkn
      · have hpow : t ^ (k + 1) * t ^ (n - k) = t ^ (n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        linear_combination (1 - t ^ (k + 1)) * e₁ + t ^ (k + 1) * e₂ -
          (∏ i ∈ range k, (1 - t ^ (n - i))) * hpow
      · have hzero : ∏ i ∈ range k, (1 - t ^ (n - i)) = 0 :=
          prod_eq_zero (mem_range.2 hkn) (by simp)
        rw [hzero] at e₁ e₂ ⊢
        linear_combination (1 - t ^ (k + 1)) * e₁ + t ^ (k + 1) * e₂

/-- The factorial form of the product formula: for `k ≤ n`,
`[n k]_t (t;t)_k (t;t)_(n-k) = (t;t)_n`. -/
theorem gaussianBinomial_mul_qPochhammer_mul_qPochhammer (t : R) {n k : ℕ} (h : k ≤ n) :
    gaussianBinomial t n k * qPochhammer t t k * qPochhammer t t (n - k) =
      qPochhammer t t n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [gaussianBinomial_mul_qPochhammer, Nat.add_sub_cancel_left, qPochhammer_self,
    qPochhammer_self, add_comm k m, prod_range_add, mul_comm,
    prod_range_add_sub_eq (fun j ↦ 1 - t ^ j)]

/-- The subspace-counting form of the product formula
`[n k]_t ∏_{i<k} (t^k - t^i) = ∏_{i<k} (t^n - t^i)`; for `k > n` both sides vanish. At the
cardinality `t = q` of a finite field the products count the linearly independent `k`-tuples in
spaces of dimensions `k` and `n`. -/
theorem gaussianBinomial_mul_prod_pow_sub_pow (t : R) (n k : ℕ) :
    gaussianBinomial t n k * ∏ i ∈ range k, (t ^ k - t ^ i) = ∏ i ∈ range k, (t ^ n - t ^ i) := by
  rcases lt_or_ge n k with h | h
  · rw [gaussianBinomial_eq_zero_of_lt t h, zero_mul, prod_eq_zero (mem_range.2 h) (sub_self _)]
  -- Factor `t^m - t^i = -t^i (1 - t^(m-i))` for `i < k ≤ m`.
  have hfactor {m : ℕ} (hm : k ≤ m) : ∏ i ∈ range k, (t ^ m - t ^ i) =
      (∏ i ∈ range k, -t ^ i) * ∏ i ∈ range k, (1 - t ^ (m - i)) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i hi ↦ ?_
    rw [mem_range] at hi
    rw [← pow_mul_pow_sub t (hi.le.trans hm)]
    ring
  have hreflect : ∏ i ∈ range k, (1 - t ^ (k - i)) = qPochhammer t t k := by
    simpa [qPochhammer_self] using prod_range_add_sub_eq (fun j ↦ 1 - t ^ j) 0 k
  rw [hfactor le_rfl, hfactor h, hreflect, mul_left_comm, gaussianBinomial_mul_qPochhammer]

end CommRing

/-- The Gaussian polynomials are symmetric: `[n n-k] = [n k]` for `k ≤ n`. -/
theorem gaussianPoly_symm {n k : ℕ} (h : k ≤ n) : gaussianPoly n (n - k) = gaussianPoly n k := by
  -- Both sides satisfy the factorial form of the product formula in the domain `ℤ[t]`, whose
  -- factors `1 - t^(i+1)` are nonzero.
  let φ : ℕ[X] →+* ℤ[X] := mapRingHom (Nat.castRingHom ℤ)
  have hφ : Function.Injective φ := map_injective _ Nat.cast_injective
  have hmap (j : ℕ) : φ (gaussianPoly n j) = gaussianBinomial (X : ℤ[X]) n j :=
    map_gaussianPoly _ n j
  have hP (m : ℕ) : qPochhammer (X : ℤ[X]) X m ≠ 0 := by
    rintro h0
    obtain ⟨i, -, hi⟩ := qPochhammer_eq_zero_iff.1 h0
    simpa using congrArg (eval 0) hi
  apply hφ
  rw [hmap, hmap]
  have e₁ := gaussianBinomial_mul_qPochhammer_mul_qPochhammer (X : ℤ[X]) h
  have e₂ := gaussianBinomial_mul_qPochhammer_mul_qPochhammer (X : ℤ[X]) (Nat.sub_le n k)
  rw [Nat.sub_sub_self h] at e₂
  refine mul_right_cancel₀ (mul_ne_zero (hP k) (hP (n - k))) ?_
  linear_combination e₂ - e₁

/-- The Gaussian binomial coefficients are symmetric: `[n n-k]_t = [n k]_t` for `k ≤ n`. -/
theorem gaussianBinomial_symm {R : Type*} [Semiring R] (t : R) {n k : ℕ} (h : k ≤ n) :
    gaussianBinomial t n (n - k) = gaussianBinomial t n k := by
  rw [gaussianBinomial_def, gaussianPoly_symm h, gaussianBinomial_def]

/-- The mirrored successor recursion `[n+1 k+1]_t = t^(n-k) [n k]_t + [n k+1]_t`. It holds for all
`n` and `k`: for `k > n` both sides vanish. -/
theorem gaussianBinomial_succ_succ' {R : Type*} [Semiring R] (t : R) (n k : ℕ) :
    gaussianBinomial t (n + 1) (k + 1) =
      t ^ (n - k) * gaussianBinomial t n k + gaussianBinomial t n (k + 1) := by
  rcases lt_or_ge n k with hnk | hkn
  · rw [gaussianBinomial_eq_zero_of_lt t (by omega), gaussianBinomial_eq_zero_of_lt t hnk,
      gaussianBinomial_eq_zero_of_lt t (by omega), mul_zero, add_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rcases m with _ | m
  · simp
  -- Reflect `k ↦ n - k` in all three coefficients and apply the defining recursion.
  rw [← gaussianBinomial_symm t (by omega : k + 1 ≤ k + (m + 1) + 1),
    ← gaussianBinomial_symm t (by omega : k ≤ k + (m + 1)),
    ← gaussianBinomial_symm t (by omega : k + 1 ≤ k + (m + 1)),
    show k + (m + 1) + 1 - (k + 1) = m + 1 by omega, show k + (m + 1) - k = m + 1 by omega,
    show k + (m + 1) - (k + 1) = m by omega, gaussianBinomial_succ_succ, add_comm]

/-- The mirrored successor recursion `[n+1 k+1] = t^(n-k) [n k] + [n k+1]`. -/
theorem gaussianPoly_succ_succ' (n k : ℕ) :
    gaussianPoly (n + 1) (k + 1) = X ^ (n - k) * gaussianPoly n k + gaussianPoly n (k + 1) := by
  simpa using gaussianBinomial_succ_succ' (X : ℕ[X]) n k

/-- The quotient formula `[n k]_t = ∏_{i=1}^{k} (1 - t^(n-k+i)) / (1 - t^i)` over a field, for
`k ≤ n` and whenever none of the denominators `1 - t^i`, `1 ≤ i ≤ k`, vanishes. -/
theorem gaussianBinomial_eq_prod_div {K : Type*} [Field K] {t : K} {n k : ℕ} (h : k ≤ n)
    (ht : ∀ i ∈ range k, t ^ (i + 1) ≠ 1) :
    gaussianBinomial t n k = ∏ i ∈ range k, (1 - t ^ (n - k + i + 1)) / (1 - t ^ (i + 1)) := by
  have hden : qPochhammer t t k ≠ 0 := fun h0 ↦ by
    obtain ⟨i, hi, hi1⟩ := qPochhammer_eq_zero_iff.1 h0
    exact ht i (mem_range.2 hi) (by rwa [pow_succ'])
  rw [prod_div_distrib, ← qPochhammer_self, eq_div_iff hden, gaussianBinomial_mul_qPochhammer,
    ← prod_range_add_sub_eq (fun j ↦ 1 - t ^ j), Nat.sub_add_cancel h]

/-- **Cauchy's `q`-binomial theorem**: over every commutative semiring,
`∏_{i<n} (1 + t^i z) = ∑_{k ≤ n} t^(k(k-1)/2) [n k]_t z^k`, where `k(k-1)/2 = k.choose 2`. Taking
the coefficients in a polynomial ring and `z` the variable gives the polynomial identity. -/
theorem prod_one_add_pow_mul_eq_sum_gaussianBinomial {R : Type*} [CommSemiring R] (t z : R)
    (n : ℕ) :
    ∏ i ∈ range n, (1 + t ^ i * z) =
      ∑ k ∈ range (n + 1), t ^ k.choose 2 * gaussianBinomial t n k * z ^ k := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    -- Split off the factor `1 + z`; the remaining factors are those for `n` at `t z`.
    have hprod : ∏ i ∈ range (n + 1), (1 + t ^ i * z) =
        (1 + z) * ∏ i ∈ range n, (1 + t ^ i * (t * z)) := by
      rw [prod_range_succ', mul_comm]
      simp [pow_succ, mul_assoc]
    have hc (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
      simp [Nat.choose_succ_succ, add_comm]
    -- The constant term of `∑_k t^(k choose 2) [n k]_t (t z)^k` is `1`, and its top term vanishes.
    have hshift : ∑ k ∈ range (n + 1), t ^ k.choose 2 * gaussianBinomial t n k * (t * z) ^ k =
        1 + ∑ k ∈ range (n + 1),
          t ^ (k + 1).choose 2 * gaussianBinomial t n (k + 1) * (t * z) ^ (k + 1) := by
      rw [sum_range_succ' _ n, sum_range_succ _ n,
        gaussianBinomial_eq_zero_of_lt t n.lt_succ_self]
      simp [add_comm]
    -- Each term for `n + 1` splits by the successor recursion into terms for `n` at `t z`.
    have hterm (k : ℕ) : t ^ (k + 1).choose 2 * gaussianBinomial t (n + 1) (k + 1) * z ^ (k + 1) =
        t ^ (k + 1).choose 2 * gaussianBinomial t n (k + 1) * (t * z) ^ (k + 1) +
          z * (t ^ k.choose 2 * gaussianBinomial t n k * (t * z) ^ k) := by
      rw [gaussianBinomial_succ_succ, hc k]
      ring
    have hzero : t ^ (0 : ℕ).choose 2 * gaussianBinomial t (n + 1) 0 * z ^ 0 = 1 := by simp
    rw [hprod, ih, add_mul, one_mul, mul_sum, hshift, sum_range_succ' _ (n + 1),
      sum_congr rfl fun k _ ↦ hterm k, sum_add_distrib, hzero]
    ring

/-- The column recursion `[e+j+1 j+1]_t = ∑_{i ≤ e} t^i [i+j j]_t`. -/
theorem gaussianBinomial_add_succ_eq_sum {R : Type*} [Semiring R] (t : R) (e j : ℕ) :
    gaussianBinomial t (e + j + 1) (j + 1) =
      ∑ i ∈ range (e + 1), t ^ i * gaussianBinomial t (i + j) j := by
  -- Iterate the mirrored successor recursion `TauCeti.gaussianBinomial_succ_succ'`.
  induction e with
  | zero => simp [gaussianBinomial_self]
  | succ e ih =>
    rw [gaussianBinomial_succ_succ', sum_range_succ, show e + 1 + j - j = e + 1 by omega,
      show e + 1 + j = e + j + 1 by omega, ih, add_comm]

section Bounds

/-- For a nonzero natural number `q`, `[e+j j]_q ≤ (e+1)^j q^(ej)`. -/
theorem gaussianBinomial_add_le_succ_pow_mul_pow {q : ℕ} (hq : q ≠ 0) (e j : ℕ) :
    gaussianBinomial q (e + j) j ≤ (e + 1) ^ j * q ^ (e * j) := by
  -- Each of the at most `(e+1)^j` terms of the iterated column recursion is at most `q^(ej)`.
  induction j generalizing e with
  | zero => simp [gaussianBinomial_zero_right]
  | succ j ih =>
    rw [← add_assoc, gaussianBinomial_add_succ_eq_sum]
    calc ∑ i ∈ range (e + 1), q ^ i * gaussianBinomial q (i + j) j
      _ ≤ ∑ _i ∈ range (e + 1), (e + 1) ^ j * q ^ (e * (j + 1)) := by
        refine sum_le_sum fun i hi ↦ ?_
        have hie : i ≤ e := Nat.lt_succ_iff.1 (mem_range.1 hi)
        calc q ^ i * gaussianBinomial q (i + j) j
          _ ≤ q ^ i * ((i + 1) ^ j * q ^ (i * j)) := Nat.mul_le_mul_left _ (ih i)
          _ = (i + 1) ^ j * q ^ (i * (j + 1)) := by ring
          _ ≤ (e + 1) ^ j * q ^ (e * (j + 1)) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) j)
              (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq) (Nat.mul_le_mul_right _ hie))
      _ = (e + 1) ^ (j + 1) * q ^ (e * (j + 1)) := by
        rw [sum_const, card_range, smul_eq_mul, pow_succ', mul_assoc]

/-- For a natural number `q ≥ 2`, `[e+j j]_q ≤ q^(e(j+1))`. -/
theorem gaussianBinomial_add_le_pow {q : ℕ} (hq : 2 ≤ q) (e j : ℕ) :
    gaussianBinomial q (e + j) j ≤ q ^ (e * (j + 1)) := by
  -- By symmetry `[e+j j]_q = [e+j e]_q`, and in the product formula
  -- `[e+j e]_q ∏_{i<e} (q^e - q^i) = ∏_{i<e} (q^(e+j) - q^i)` each factor on the right is at
  -- most `q^(j+1)` times the corresponding factor on the left.
  rw [← gaussianBinomial_symm _ (Nat.le_add_left j e), Nat.add_sub_cancel]
  have hfactor (i : ℕ) (hi : i < e) :
      (q : ℤ) ^ (e + j) - q ^ i ≤ q ^ (j + 1) * (q ^ e - q ^ i) := by
    have h1 : (q : ℤ) ^ (i + j + 1) ≤ q ^ (e + j) := pow_le_pow_right₀ (by omega) (by omega)
    have h2 : (0 : ℤ) ≤ q ^ i := by positivity
    have h3 : (0 : ℤ) ≤ (q - 2) * q ^ (e + j) := mul_nonneg (by omega) (by positivity)
    have h4 : (q : ℤ) ^ (j + 1) * (q ^ e - q ^ i) = q * q ^ (e + j) - q ^ (i + j + 1) := by ring
    rw [h4]
    nlinarith
  have hpos : (0 : ℤ) < ∏ i ∈ range e, ((q : ℤ) ^ e - q ^ i) :=
    prod_pos fun i hi ↦ sub_pos.2 (pow_lt_pow_right₀ (by omega) (mem_range.1 hi))
  have hprod := gaussianBinomial_mul_prod_pow_sub_pow (q : ℤ) (e + j) e
  have hle : ∏ i ∈ range e, ((q : ℤ) ^ (e + j) - q ^ i) ≤
      ∏ i ∈ range e, ((q : ℤ) ^ (j + 1) * (q ^ e - q ^ i)) :=
    prod_le_prod₀ (fun i hi ↦ sub_nonneg.2 (pow_le_pow_right₀ (by omega)
      (by have := mem_range.1 hi; omega))) fun i hi ↦ hfactor i (mem_range.1 hi)
  rw [prod_mul_distrib, prod_const, card_range, ← hprod] at hle
  have hcast : ((gaussianBinomial q (e + j) e : ℕ) : ℤ) = gaussianBinomial (q : ℤ) (e + j) e := by
    exact map_gaussianBinomial (Nat.castRingHom ℤ) q (e + j) e
  have : ((gaussianBinomial q (e + j) e : ℕ) : ℤ) ≤ (q : ℤ) ^ (e * (j + 1)) := by
    rw [hcast, mul_comm e, pow_mul]
    exact le_of_mul_le_mul_right hle hpos
  exact_mod_cast this

end Bounds

end TauCeti
