/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# q-factorials and q-Pochhammer products

For a parameter `q` in a commutative semiring, the q-integer `[n]_q = ∑_{i < n} q ^ i` is
Mathlib's finite geometric sum; `mul_neg_geom_sum` gives `(1 - q) [n]_q = 1 - q ^ n` and
`one_geom_sum` gives `[n]_1 = n`. This file defines the two products built from it,

* the q-factorial `[n]_q! = ∏_{i = 1}^{n} [i]_q`, and
* the finite q-Pochhammer product `(x; q)_n = ∏_{i < n} (1 - x q ^ i)`,

and proves the elementary identities relating them. Everything is an identity of ring
elements, with no division, so it holds in positive characteristic and at roots of unity, and
with coefficient ring `R[q]` and `q = X` it gives polynomial identities. In particular
`(q; q)_N = ∏_{i = 1}^{N} (1 - q ^ i)` is the factorial polynomial whose multiples define the
cyclotomic (Habiro) completion of `R[q]`.

For a unit `q` the product also extends to integer indices, by
`(a; q)_{-n} = 1 / ((1 - a q⁻¹) ⋯ (1 - a q⁻ⁿ)) = 1 / (a q⁻ⁿ; q)_n`. This is defined only on an
explicit domain, the indices for which every such factor is a unit, so the inverse of a non-unit
is never given a junk value. The integer-indexed products are the coefficients of bilateral basic
hypergeometric series and of the regular quotients `(a; q)_j / (b; q)_j` at negative `j`.

These are the asymmetric (Gaussian) conventions of basic hypergeometric series. The q-integers
here are not the symmetric quantum integers `TauCeti.qInt` (at a loop parameter) or
`TauCeti.quantumInteger`, and `TauCeti.qFactorial` is not built from them; see
`TauCeti.quantumFactorial` and `TauCeti.laurentQuantumFactorial` for the symmetric quantum
factorial.

## Main definitions

* `TauCeti.qFactorial q n`: the q-factorial `[n]_q! = ∏_{i < n} ∑_{j ≤ i} q ^ j`.
* `TauCeti.qPochhammer x q n`: the finite q-Pochhammer product `(x; q)_n`.
* `TauCeti.qPochhammerIntDomain a q`: for a unit `q`, the integers `j` at which `(a; q)_j` is
  defined, namely those for which `1 - a q ^ i` is a unit whenever `j ≤ i < 0`.
* `TauCeti.qPochhammerInt a q j hj`: the integer-indexed q-Pochhammer product `(a; q)_j` for
  `j` in that domain.

## Main results

* `TauCeti.qFactorial_base_one`: `[n]_1! = n!`.
* `TauCeti.map_qFactorial`, `TauCeti.map_qPochhammer`: both products commute with ring
  homomorphisms; `Polynomial.map_qFactorial`, `Polynomial.map_qPochhammer` and the `eval`
  versions are the coefficient-change and evaluation forms on `R[X]`.
* `TauCeti.qPochhammer_add`: concatenation, `(x; q)_{m + n} = (x; q)_m (x q ^ m; q)_n`, with
  the shift law `TauCeti.qPochhammer_succ'`: `(x; q)_{n + 1} = (1 - x) (x q; q)_n`.
* `TauCeti.one_sub_pow_mul_qFactorial`: `(1 - q) ^ n [n]_q! = (q; q)_n`.
* `TauCeti.qPochhammer_base_one`: at base `q = 1`, `(x; 1)_n = (1 - x) ^ n`.
* `TauCeti.qPochhammer_eq_zero_iff`: without zero divisors, `(x; q)_n = 0` exactly when
  `x q ^ i = 1` for some `i < n`.
* `TauCeti.qPochhammer_inv`, `TauCeti.qPochhammer_inv_self`: for units `x` and `q`,
  `(x⁻¹; q⁻¹)_n = (-1) ^ n x⁻ⁿ q^{-n(n-1)/2} (x; q)_n`, and in particular
  `(q⁻¹; q⁻¹)_n = (-1) ^ n q^{-n(n+1)/2} (q; q)_n`.
* `TauCeti.qPochhammerInt_natCast`: on natural indices `(a; q)_j` is the finite product.
* `TauCeti.qPochhammerInt_neg_natCast_mul`: `(a; q)_{-n} (a q⁻ⁿ; q)_n = 1`.
* `TauCeti.qPochhammerInt_add`: concatenation `(a; q)_{i + j} = (a; q)_i (a q ^ i; q)_j` for all
  integers `i`, `j` with the three products defined.
* `TauCeti.map_qPochhammerInt`: ring homomorphisms preserve the integer-indexed product.

## References

* G. Gasper, M. Rahman, *Basic Hypergeometric Series*, 2nd ed., Encyclopedia of Mathematics and
  its Applications 96, Cambridge University Press, 2004, §1.2 and Appendix I.
* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*, Bonn,
  winter 2024/25, Definition 1.1, Table 1 and Proposition 2.1.
-/

public section

open Finset

open scoped Nat

namespace TauCeti

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The q-factorial `[n]_q! = [1]_q [2]_q ⋯ [n]_q`, where `[i]_q = ∑_{j < i} q ^ j` is the
q-integer. This is the asymmetric (Gaussian) q-factorial; it is not built from the symmetric
quantum integer `TauCeti.qInt`, and `TauCeti.quantumFactorial` is the symmetric convention. -/
def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, ∑ j ∈ range (i + 1), q ^ j

/-- The defining product formula for the q-factorial. -/
theorem qFactorial_def (q : R) (n : ℕ) :
    qFactorial q n = ∏ i ∈ range n, ∑ j ∈ range (i + 1), q ^ j :=
  (rfl)

/-- `[0]_q! = 1`. -/
@[simp]
theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 := by
  simp [qFactorial_def]

/-- `[n + 1]_q! = [n]_q! [n + 1]_q`. -/
theorem qFactorial_succ (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * ∑ j ∈ range (n + 1), q ^ j := by
  simp [qFactorial_def, prod_range_succ]

/-- `[1]_q! = 1`. -/
@[simp]
theorem qFactorial_one (q : R) : qFactorial q 1 = 1 := by
  simp [qFactorial_def]

/-- At `q = 1` the q-factorial is the ordinary factorial: `[n]_1! = n!`. -/
@[simp]
theorem qFactorial_base_one (n : ℕ) : qFactorial (1 : R) n = n ! := by
  simp [qFactorial_def, ← prod_range_add_one_eq_factorial]

/-- The q-factorial commutes with ring homomorphisms. -/
@[simp]
theorem map_qFactorial {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (q : R)
    (n : ℕ) : f (qFactorial q n) = qFactorial (f q) n := by
  simp [qFactorial_def, map_prod, map_sum]

end CommSemiring

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The finite q-Pochhammer product `(x; q)_n = (1 - x) (1 - x q) ⋯ (1 - x q ^ (n - 1))` with
base `q`. -/
def qPochhammer (x q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, (1 - x * q ^ i)

/-- The defining product formula for the finite q-Pochhammer product. -/
theorem qPochhammer_def (x q : R) (n : ℕ) :
    qPochhammer x q n = ∏ i ∈ range n, (1 - x * q ^ i) :=
  (rfl)

/-- The empty q-Pochhammer product is one: `(x; q)_0 = 1`. -/
@[simp]
theorem qPochhammer_zero (x q : R) : qPochhammer x q 0 = 1 := by
  simp [qPochhammer_def]

/-- `(x; q)_1 = 1 - x`. -/
@[simp]
theorem qPochhammer_one (x q : R) : qPochhammer x q 1 = 1 - x := by
  simp [qPochhammer_def]

/-- Splitting off the last factor: `(x; q)_{n + 1} = (x; q)_n (1 - x q ^ n)`. -/
theorem qPochhammer_succ (x q : R) (n : ℕ) :
    qPochhammer x q (n + 1) = qPochhammer x q n * (1 - x * q ^ n) := by
  simp [qPochhammer_def, prod_range_succ]

/-- Concatenation of q-Pochhammer products: `(x; q)_{m + n} = (x; q)_m (x q ^ m; q)_n`. -/
theorem qPochhammer_add (x q : R) (m n : ℕ) :
    qPochhammer x q (m + n) = qPochhammer x q m * qPochhammer (x * q ^ m) q n := by
  simp [qPochhammer_def, prod_range_add, pow_add, mul_assoc]

/-- The shift law, splitting off the first factor: `(x; q)_{n + 1} = (1 - x) (x q; q)_n`. -/
theorem qPochhammer_succ' (x q : R) (n : ℕ) :
    qPochhammer x q (n + 1) = (1 - x) * qPochhammer (x * q) q n := by
  rw [add_comm, qPochhammer_add, qPochhammer_one, pow_one]

/-- With `x = 0` every factor is one: `(0; q)_n = 1`. -/
@[simp]
theorem qPochhammer_zero_left (q : R) (n : ℕ) : qPochhammer 0 q n = 1 := by
  simp [qPochhammer_def]

/-- At `q = 1` the q-Pochhammer product is a power: `(x; 1)_n = (1 - x) ^ n`. -/
@[simp]
theorem qPochhammer_base_one (x : R) (n : ℕ) : qPochhammer x 1 n = (1 - x) ^ n := by
  simp [qPochhammer_def]

/-- `(q; q)_n = ∏_{i = 1}^{n} (1 - q ^ i)`, the form in which `(q; q)_n` is the factorial
polynomial. -/
theorem qPochhammer_self (q : R) (n : ℕ) :
    qPochhammer q q n = ∏ i ∈ range n, (1 - q ^ (i + 1)) := by
  simp [qPochhammer_def, pow_succ']

/-- The finite q-Pochhammer product commutes with ring homomorphisms. -/
@[simp]
theorem map_qPochhammer {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (x q : R)
    (n : ℕ) : f (qPochhammer x q n) = qPochhammer (f x) (f q) n := by
  simp [qPochhammer_def, map_prod]

/-- The q-factorial and the q-Pochhammer product are related by
`(1 - q) ^ n [n]_q! = (q; q)_n`. -/
theorem one_sub_pow_mul_qFactorial (q : R) (n : ℕ) :
    (1 - q) ^ n * qFactorial q n = qPochhammer q q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ, qPochhammer_succ, ← ih, ← pow_succ', ← mul_neg_geom_sum]
    ring

/-- A q-Pochhammer product vanishes as soon as one of its factors does: if `x q ^ i = 1` for
some `i < n`, then `(x; q)_n = 0`. -/
theorem qPochhammer_eq_zero_of_mul_pow_eq_one {x q : R} {n i : ℕ} (hi : i < n)
    (h : x * q ^ i = 1) : qPochhammer x q n = 0 :=
  prod_eq_zero (mem_range.mpr hi) (by rw [h, sub_self])

/-- Without zero divisors, `(x; q)_n = 0` exactly when `x q ^ i = 1` for some `i < n`. -/
theorem qPochhammer_eq_zero_iff [NoZeroDivisors R] [Nontrivial R] {x q : R} {n : ℕ} :
    qPochhammer x q n = 0 ↔ ∃ i < n, x * q ^ i = 1 := by
  simp [qPochhammer_def, prod_eq_zero_iff, sub_eq_zero, eq_comm (a := (1 : R))]

/-- The inverse-parameter formula: for units `x` and `q`,
`(x⁻¹; q⁻¹)_n = (-1) ^ n x⁻ⁿ q^{-n(n-1)/2} (x; q)_n`. -/
theorem qPochhammer_inv (x q : Rˣ) (n : ℕ) :
    qPochhammer (↑x⁻¹ : R) ↑q⁻¹ n =
      (-1) ^ n * (↑x⁻¹ : R) ^ n * (↑q⁻¹ : R) ^ (n * (n - 1) / 2) * qPochhammer (x : R) q n := by
  -- Each factor is `1 - x⁻¹ q⁻ⁱ = (-1) x⁻¹ q⁻ⁱ (1 - x qⁱ)`.
  have hfactor (i : ℕ) :
      1 - (↑x⁻¹ : R) * ↑q⁻¹ ^ i = -1 * ↑x⁻¹ * ↑q⁻¹ ^ i * (1 - x * q ^ i) := by
    have hx : (↑x⁻¹ : R) * x = 1 := x.inv_mul
    have hq : (↑q⁻¹ : R) ^ i * q ^ i = 1 := by rw [← mul_pow, q.inv_mul, one_pow]
    linear_combination -((↑q⁻¹ : R) ^ i * q ^ i) * hx - hq
  simp only [qPochhammer_def, hfactor, prod_mul_distrib, prod_const, card_range]
  rw [prod_pow_eq_pow_sum (range n) (fun i ↦ i), sum_range_id]

/-- The inverse-parameter formula for `(q; q)_n`: for a unit `q`,
`(q⁻¹; q⁻¹)_n = (-1) ^ n q^{-n(n+1)/2} (q; q)_n`. -/
theorem qPochhammer_inv_self (q : Rˣ) (n : ℕ) :
    qPochhammer (↑q⁻¹ : R) ↑q⁻¹ n =
      (-1) ^ n * (↑q⁻¹ : R) ^ (n * (n + 1) / 2) * qPochhammer (q : R) q n := by
  have hexp : n * (n + 1) / 2 = n + n * (n - 1) / 2 := by
    simpa [mul_comm, add_comm] using Nat.triangle_succ n
  rw [qPochhammer_inv, hexp, pow_add, mul_assoc ((-1 : R) ^ n)]

end CommRing

/-! ### Integer-indexed q-Pochhammer products

For a unit `q`, the finite product extends to negative indices by
`(a; q)_{-n} = 1 / ((1 - a q⁻¹) (1 - a q⁻²) ⋯ (1 - a q⁻ⁿ))`, the reciprocal of
`(a q⁻ⁿ; q)_n`. This is defined only when every displayed factor is a unit; the domain is kept
explicit, so no inverse of a non-unit is ever assigned a value. -/

section Int

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The domain of the integer-indexed q-Pochhammer product `(a; q)_j` for a unit `q`: the
integers `j` such that every factor `1 - a q ^ i` with `j ≤ i < 0` is a unit. Every `j ≥ 0` lies
in it. -/
def qPochhammerIntDomain (a : R) (q : Rˣ) : Set ℤ :=
  {j | ∀ i : ℤ, j ≤ i → i < 0 → IsUnit (1 - a * ↑(q ^ i))}

/-- Membership in the domain of `(a; q)_j`, unfolded. -/
theorem mem_qPochhammerIntDomain {a : R} {q : Rˣ} {j : ℤ} :
    j ∈ qPochhammerIntDomain a q ↔ ∀ i : ℤ, j ≤ i → i < 0 → IsUnit (1 - a * ↑(q ^ i)) :=
  Iff.rfl

/-- Every nonnegative index lies in the domain of the integer-indexed q-Pochhammer product. -/
theorem mem_qPochhammerIntDomain_of_nonneg {a : R} {q : Rˣ} {j : ℤ} (hj : 0 ≤ j) :
    j ∈ qPochhammerIntDomain a q :=
  fun _ hi hi₀ ↦ absurd (hj.trans hi) hi₀.not_ge

/-- Every natural index lies in the domain of the integer-indexed q-Pochhammer product. -/
@[simp]
theorem natCast_mem_qPochhammerIntDomain (a : R) (q : Rˣ) (n : ℕ) :
    (n : ℤ) ∈ qPochhammerIntDomain a q :=
  mem_qPochhammerIntDomain_of_nonneg n.cast_nonneg

/-- The domain of the integer-indexed q-Pochhammer product is closed upwards. -/
theorem mem_qPochhammerIntDomain_of_le {a : R} {q : Rˣ} {j k : ℤ} (hjk : j ≤ k)
    (hj : j ∈ qPochhammerIntDomain a q) : k ∈ qPochhammerIntDomain a q :=
  fun i hi hi₀ ↦ hj i (hjk.trans hi) hi₀

/-- `(↑(q ^ j) : R) * ↑q ^ m = ↑(q ^ (j + m))` for a unit `q`. -/
private theorem val_zpow_mul_pow (q : Rˣ) (j : ℤ) (m : ℕ) :
    (↑(q ^ j) : R) * ↑q ^ m = ↑(q ^ (j + m)) := by
  rw [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]

/-- An index `j` lies in the domain of `(a; q)_j` exactly when `(a q ^ j; q)_{-j}` is a unit,
where `-j` is truncated at zero; for `j = -n` this is the denominator `(a q⁻ⁿ; q)_n`. -/
theorem mem_qPochhammerIntDomain_iff_isUnit {a : R} {q : Rˣ} {j : ℤ} :
    j ∈ qPochhammerIntDomain a q ↔ IsUnit (qPochhammer (a * ↑(q ^ j)) q (-j).toNat) := by
  simp only [mem_qPochhammerIntDomain, qPochhammer_def, IsUnit.prod_iff, mem_range, mul_assoc,
    val_zpow_mul_pow]
  refine ⟨fun h m hm ↦ h _ (by omega) (by omega), fun h i hji hi ↦ ?_⟩
  have := h (i - j).toNat (by omega)
  rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this

/-- `-n` lies in the domain of `(a; q)_{-n}` exactly when `(a q⁻ⁿ; q)_n` is a unit. -/
theorem neg_natCast_mem_qPochhammerIntDomain_iff {a : R} {q : Rˣ} {n : ℕ} :
    -(n : ℤ) ∈ qPochhammerIntDomain a q ↔ IsUnit (qPochhammer (a * ↑(q ^ (-(n : ℤ)))) q n) := by
  rw [mem_qPochhammerIntDomain_iff_isUnit, neg_neg, Int.toNat_natCast]

/-- The **integer-indexed q-Pochhammer product** `(a; q)_j` for a unit `q` and an index `j` in
its domain. For `j ≥ 0` it is the finite product `(a; q)_j`; for `j = -n < 0` it is
`1 / ((1 - a q⁻¹) ⋯ (1 - a q⁻ⁿ)) = 1 / (a q⁻ⁿ; q)_n`, the inverse of a unit. -/
noncomputable def qPochhammerInt (a : R) (q : Rˣ) (j : ℤ) (hj : j ∈ qPochhammerIntDomain a q) :
    R :=
  if 0 ≤ j then qPochhammer a q j.toNat
  else ↑(mem_qPochhammerIntDomain_iff_isUnit.mp hj).unit⁻¹

variable {a : R} {q : Rˣ}

/-- For a nonnegative index the integer-indexed product is the finite product. -/
theorem qPochhammerInt_of_nonneg {j : ℤ} (hj₀ : 0 ≤ j) (hj : j ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q j hj = qPochhammer a q j.toNat :=
  ite_eq_left hj₀

/-- On natural indices the integer-indexed product agrees with the finite product. -/
@[simp]
theorem qPochhammerInt_natCast (n : ℕ) (hn : (n : ℤ) ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q n hn = qPochhammer a q n := by
  rw [qPochhammerInt_of_nonneg n.cast_nonneg, Int.toNat_natCast]

/-- `(a; q)_0 = 1`, for every `a`. -/
@[simp]
theorem qPochhammerInt_zero (h : (0 : ℤ) ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q 0 h = 1 :=
  qPochhammerInt_natCast 0 h

/-- For `j ≤ 0`, `(a; q)_j (a q ^ j; q)_{-j} = 1`. -/
private theorem qPochhammerInt_mul_qPochhammer_of_nonpos {j : ℤ} (hj₀ : j ≤ 0)
    (hj : j ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q j hj * qPochhammer (a * ↑(q ^ j)) q (-j).toNat = 1 := by
  rcases hj₀.lt_or_eq with hj₀ | rfl
  · rw [qPochhammerInt, ite_eq_right hj₀.not_ge, IsUnit.val_inv_mul]
  · simp

/-- `(a; q)_{-n} (a q⁻ⁿ; q)_n = 1`. -/
theorem qPochhammerInt_neg_natCast_mul (n : ℕ) (hn : -(n : ℤ) ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q (-n) hn * qPochhammer (a * ↑(q ^ (-(n : ℤ)))) q n = 1 := by
  simpa using qPochhammerInt_mul_qPochhammer_of_nonpos (by omega) hn

/-- The value of the integer-indexed product at a negative index:
`(a; q)_{-n} = Ring.inverse ((a q⁻ⁿ; q)_n)`, the inverse of a unit on the domain. -/
theorem qPochhammerInt_neg_natCast (n : ℕ) (hn : -(n : ℤ) ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q (-n) hn = Ring.inverse (qPochhammer (a * ↑(q ^ (-(n : ℤ)))) q n) := by
  rw [← one_mul (Ring.inverse _),
    Ring.eq_mul_inverse_iff_mul_eq _ _ _ (neg_natCast_mem_qPochhammerIntDomain_iff.mp hn)]
  exact qPochhammerInt_neg_natCast_mul n hn

/-- `(a; q)_j (a q ^ j; q)_N = (a; q)_{j + N}` when `j + N ≥ 0`. -/
private theorem qPochhammerInt_mul_qPochhammer_of_nonneg {j : ℤ}
    (hj : j ∈ qPochhammerIntDomain a q) (N : ℕ) (hjN : 0 ≤ j + N) :
    qPochhammerInt a q j hj * qPochhammer (a * ↑(q ^ j)) q N = qPochhammer a q (j + N).toNat := by
  rcases le_or_gt 0 j with hj₀ | hj₀
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj₀
    rw [qPochhammerInt_natCast, zpow_natCast, Units.val_pow_eq_pow_val, ← qPochhammer_add,
      ← Nat.cast_add, Int.toNat_natCast]
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hj₀.le
    obtain ⟨k, rfl⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
    rw [qPochhammer_add, ← mul_assoc, qPochhammerInt_neg_natCast_mul, one_mul, mul_assoc,
      val_zpow_mul_pow, neg_add_cancel, zpow_zero, Units.val_one, mul_one]
    congr 1
    omega

/-- **Concatenation with a natural second index**: `(a; q)_{i + N} = (a; q)_i (a q ^ i; q)_N`
for every integer `i` and natural `N` with both products defined. -/
theorem qPochhammerInt_add_natCast {i : ℤ} (N : ℕ) (hi : i ∈ qPochhammerIntDomain a q)
    (hiN : i + N ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q (i + N) hiN = qPochhammerInt a q i hi * qPochhammer (a * ↑(q ^ i)) q N := by
  rcases le_or_gt 0 (i + N) with h₀ | h₀
  · rw [qPochhammerInt_of_nonneg h₀, qPochhammerInt_mul_qPochhammer_of_nonneg hi N h₀]
  · -- Both sides are left inverses of the unit `(a q ^ (i + N); q)_{-(i + N)}`.
    refine (mem_qPochhammerIntDomain_iff_isUnit.mp hiN).mul_left_inj.mp ?_
    rw [qPochhammerInt_mul_qPochhammer_of_nonpos h₀.le, mul_assoc, ← val_zpow_mul_pow,
      ← mul_assoc a, ← qPochhammer_add, show N + (-(i + N)).toNat = (-i).toNat by omega,
      qPochhammerInt_mul_qPochhammer_of_nonpos (by omega)]

/-- The recursion `(a; q)_{j + 1} = (a; q)_j (1 - a q ^ j)`, for every integer `j` with both
products defined. -/
theorem qPochhammerInt_add_one {j : ℤ} (hj : j ∈ qPochhammerIntDomain a q)
    (hj₁ : j + 1 ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q (j + 1) hj₁ = qPochhammerInt a q j hj * (1 - a * ↑(q ^ j)) := by
  simpa using qPochhammerInt_add_natCast 1 hj (by simpa using hj₁)

/-- **Concatenation of integer-indexed q-Pochhammer products**:
`(a; q)_{i + j} = (a; q)_i (a q ^ i; q)_j` for all integers `i` and `j` such that the three
products are defined. -/
theorem qPochhammerInt_add {i j : ℤ} (hi : i ∈ qPochhammerIntDomain a q)
    (hj : j ∈ qPochhammerIntDomain (a * ↑(q ^ i)) q) (hij : i + j ∈ qPochhammerIntDomain a q) :
    qPochhammerInt a q (i + j) hij =
      qPochhammerInt a q i hi * qPochhammerInt (a * ↑(q ^ i)) q j hj := by
  rcases le_or_gt 0 j with hj₀ | hj₀
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hj₀
    rw [qPochhammerInt_natCast, qPochhammerInt_add_natCast N hi hij]
  · -- Both sides are left inverses of the unit `(a q ^ (i + j); q)_{-j}`.
    refine (mem_qPochhammerIntDomain_iff_isUnit.mp hj).mul_left_inj.mp ?_
    have hi' : i + j + ((-j).toNat : ℤ) ∈ qPochhammerIntDomain a q := by
      rwa [show i + j + ((-j).toNat : ℤ) = i by omega]
    rw [mul_assoc (qPochhammerInt a q i hi), qPochhammerInt_mul_qPochhammer_of_nonpos hj₀.le,
      mul_one, mul_assoc,
      ← Units.val_mul, ← zpow_add, ← qPochhammerInt_add_natCast _ hij hi']
    congr 1
    omega

/-- A ring homomorphism `f` maps the domain of `(a; q)_j` into that of `(f a; f q)_j`. -/
theorem map_mem_qPochhammerIntDomain {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)
    {j : ℤ} (h : j ∈ qPochhammerIntDomain a q) :
    j ∈ qPochhammerIntDomain (f a) (Units.map (f : R →* S) q) := fun i hi hi₀ ↦ by
  simpa [← map_zpow] using (h i hi hi₀).map f

/-- The integer-indexed q-Pochhammer product commutes with ring homomorphisms, which carry the
unit `q` to the unit `f q`. -/
@[simp]
theorem map_qPochhammerInt {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) {j : ℤ}
    (h : j ∈ qPochhammerIntDomain a q) :
    f (qPochhammerInt a q j h) =
      qPochhammerInt (f a) (Units.map (f : R →* S) q) j (map_mem_qPochhammerIntDomain f h) := by
  rcases le_or_gt 0 j with hj₀ | hj₀
  · simp [qPochhammerInt_of_nonneg hj₀]
  · -- Both sides are left inverses of the unit `(f a (f q) ^ j; f q)_{-j}`.
    have h' := map_mem_qPochhammerIntDomain f h
    refine (mem_qPochhammerIntDomain_iff_isUnit.mp h').mul_left_inj.mp ?_
    rw [qPochhammerInt_mul_qPochhammer_of_nonpos hj₀.le]
    simpa [← map_zpow] using congr_arg f (qPochhammerInt_mul_qPochhammer_of_nonpos hj₀.le h)

end Int

/-! ### Polynomial coefficients

With coefficient ring `R[X]` these give the coefficient-change and evaluation behaviour of the
polynomial products such as `(X; X)_n`. -/

section Polynomial

open Polynomial

/-- Coefficient change commutes with the q-factorial. -/
@[simp]
theorem _root_.Polynomial.map_qFactorial {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : R[X]) (n : ℕ) : (qFactorial q n).map f = qFactorial (q.map f) n :=
  TauCeti.map_qFactorial (mapRingHom f) q n

/-- Evaluation commutes with the q-factorial. -/
@[simp]
theorem _root_.Polynomial.eval_qFactorial {R : Type*} [CommSemiring R] (a : R) (q : R[X])
    (n : ℕ) : (qFactorial q n).eval a = qFactorial (q.eval a) n :=
  TauCeti.map_qFactorial (evalRingHom a) q n

/-- Coefficient change commutes with the finite q-Pochhammer product. -/
@[simp]
theorem _root_.Polynomial.map_qPochhammer {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x q : R[X]) (n : ℕ) : (qPochhammer x q n).map f = qPochhammer (x.map f) (q.map f) n :=
  TauCeti.map_qPochhammer (mapRingHom f) x q n

/-- Evaluation commutes with the finite q-Pochhammer product. -/
@[simp]
theorem _root_.Polynomial.eval_qPochhammer {R : Type*} [CommRing R] (a : R) (x q : R[X])
    (n : ℕ) : (qPochhammer x q n).eval a = qPochhammer (x.eval a) (q.eval a) n :=
  TauCeti.map_qPochhammer (evalRingHom a) x q n

end Polynomial

/-! ### Reference values -/

/-- `[3]_q! = (1 + q) (1 + q + q²)`. -/
example {R : Type*} [CommSemiring R] (q : R) : qFactorial q 3 = (1 + q) * (1 + q + q ^ 2) := by
  simp only [qFactorial_def, prod_range_succ, sum_range_succ, prod_range_zero, sum_range_zero]
  ring

/-- `[3]_1! = 6`. -/
example : qFactorial (1 : ℤ) 3 = 6 := by
  simp [Nat.factorial]

/-- `(q; q)_2 = (1 - q) (1 - q²)`. -/
example {R : Type*} [CommRing R] (q : R) : qPochhammer q q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [qPochhammer_self, prod_range_succ]

/-- `(x; 1)_3 = (1 - x) ^ 3`, with no division at `q = 1`. -/
example {R : Type*} [CommRing R] (x : R) : qPochhammer x 1 3 = (1 - x) ^ 3 :=
  qPochhammer_base_one x 3

/-- `(2; 3)_3 = (1 - 2) (1 - 6) (1 - 18) = -85`. -/
example : qPochhammer (2 : ℤ) 3 3 = -85 := by
  simp [qPochhammer_def, prod_range_succ]

/-- `x = 1` makes every positive product vanish: `(1; q)_n = 0` for `n > 0`. -/
example {R : Type*} [CommRing R] (q : R) {n : ℕ} (hn : 0 < n) : qPochhammer 1 q n = 0 :=
  qPochhammer_eq_zero_of_mul_pow_eq_one hn (by simp)

/-- `(3; 2)_{-1} = 1 / (1 - 3 / 2) = -2` over `ℚ`. -/
example (h : (-1 : ℤ) ∈ qPochhammerIntDomain (3 : ℚ) (Units.mk0 2 two_ne_zero)) :
    qPochhammerInt (3 : ℚ) (Units.mk0 2 two_ne_zero) (-1) h = -2 := by
  have := qPochhammerInt_neg_natCast 1 (by simpa using h)
  norm_num at this
  exact this

/-- The index `-1` does lie in the domain of `(3; 2)_j` over `ℚ`. -/
example : (-1 : ℤ) ∈ qPochhammerIntDomain (3 : ℚ) (Units.mk0 2 two_ne_zero) := by
  intro i hi hi₀
  obtain rfl : i = -1 := by omega
  norm_num

/-- `(a; q)_0 = 1` even for `a = 1`, although `(1; q)_n = 0` for every `n > 0`. -/
example {R : Type*} [CommRing R] (q : Rˣ) :
    qPochhammerInt (1 : R) q 0 (natCast_mem_qPochhammerIntDomain 1 q 0) = 1 :=
  qPochhammerInt_zero _

/-- Over `ℚ` the index `-1` is outside the domain of `(2; 2)_j`, since the factor `1 - 2 / 2`
vanishes: no value is assigned to the inverse of zero. -/
example : (-1 : ℤ) ∉ qPochhammerIntDomain (2 : ℚ) (Units.mk0 2 two_ne_zero) := fun h ↦ by
  have := h (-1) le_rfl (by norm_num)
  norm_num at this

end TauCeti
