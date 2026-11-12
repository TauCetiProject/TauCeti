/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Alternating forward differences and the discrete Leibniz rule

For functions from an additive commutative monoid to an additive commutative group, multiplying
the `n`-th forward difference by the integer `(-1) ^ n` gives the alternating difference. These
identities describe its successor step and its alternating binomial expansion, using Mathlib's
forward-difference operator and integer scalar multiplication. For ring-valued functions, the same
identities are stated using multiplication by the coefficients in the ring.

The discrete Leibniz rule computes differences of a scalar product from finitely many differences
of its factors. Its shifted form evaluates the second factor along the arithmetic progression
starting at the input point. Its unshifted form uses only differences at that point, of orders
at most the output order, so it also computes products in finite-difference coordinates.

The `k`-th forward difference of `t ↦ t ^ m` at `0` is `k! S(m, k)`, where `S` is the Stirling
number of the second kind. Expanding `(x + i h) ^ m` binomially then writes the `k`-th forward
difference of `y ↦ y ^ m` with any step `h` at any point `x` as `k!` times an integral
combination of the monomials `x ^ (m - l) h ^ l`, `k ≤ l ≤ m`. This explicit divisibility by `k!`
is what bounds forward differences of power series over ultrametric rings.

## Main declarations

* `TauCeti.neg_one_pow_smul_fwdDiff_iter_succ`: a negative forward difference advances the
  alternating iterate by one step.
* `TauCeti.neg_one_pow_smul_fwdDiff_iter_eq_alternating_sum`: the alternating iterate as a
  binomial sum of translates.
* `TauCeti.neg_one_pow_mul_fwdDiff_iter_succ` and
  `TauCeti.neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum`: the ring-valued forms.
* `TauCeti.sum_neg_one_pow_mul_choose_succ`: the successor step for alternating binomial sums.
* `TauCeti.fwdDiff_iter_smul`: the discrete Leibniz rule, with the second factor shifted by
  the order of the difference on the first factor.
* `TauCeti.fwdDiff_iter_pow_apply_zero`: `Δᵏ (t ↦ t ^ m) (0) = k! S(m, k)`.
* `TauCeti.fwdDiff_iter_pow_eq_sum`: the `k`-th difference of `y ↦ y ^ m` with step `h` at `x`
  as `∑ₗ C(m, l) x ^ (m - l) h ^ l k! S(l, k)`.
-/

public section

open scoped fwdDiff

namespace TauCeti

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

/-- Differencing once advances the alternating iterated forward difference by one step. -/
theorem neg_one_pow_smul_fwdDiff_iter_succ (n : ℕ) (F : M → G) (s : M) :
    (-1 : ℤ) ^ n • Δ_[s]^[n] (-Δ_[s] F)
      = (-1 : ℤ) ^ (n + 1) • Δ_[s]^[n + 1] F := by
  rw [Function.iterate_succ_apply, ← neg_one_zsmul (Δ_[s] F),
    fwdDiff_iter_const_smul, smul_smul, pow_succ]

/-- The alternating iterated forward difference as an explicit alternating binomial sum. -/
theorem neg_one_pow_smul_fwdDiff_iter_eq_alternating_sum (n : ℕ) (F : M → G) (s x : M) :
    (-1 : ℤ) ^ n • Δ_[s]^[n] F x
      = ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ k * n.choose k) • F (x + k • s) := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hexp : n + (n - k) = 2 * (n - k) + k := by omega
  have hsign : (-1 : ℤ) ^ n * (-1 : ℤ) ^ (n - k) = (-1 : ℤ) ^ k := by
    rw [← pow_add, hexp, pow_add, pow_mul]
    simp
  rw [smul_smul, ← mul_assoc, hsign]

variable {R : Type*} [Ring R]

/-- Differencing once advances the alternating iterated forward difference of a ring-valued
function by one step. -/
theorem neg_one_pow_mul_fwdDiff_iter_succ (n : ℕ) (F : M → R) (s : M) :
    (fun x : M => (-1 : R) ^ n * Δ_[s]^[n] (-Δ_[s] F) x)
      = fun x : M => (-1 : R) ^ (n + 1) * Δ_[s]^[n + 1] F x := by
  funext x
  have h := congrFun (neg_one_pow_smul_fwdDiff_iter_succ n F s) x
  simp only [Pi.smul_apply, zsmul_eq_mul] at h
  push_cast at h
  exact h

/-- The alternating iterated forward difference of a ring-valued function as an explicit
alternating binomial sum. -/
theorem neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum (n : ℕ) (F : M → R) (s x : M) :
    (-1 : R) ^ n * Δ_[s]^[n] F x
      = ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ k * n.choose k * F (x + k • s) := by
  have h := neg_one_pow_smul_fwdDiff_iter_eq_alternating_sum n F s x
  simp only [zsmul_eq_mul] at h
  push_cast at h
  exact h

/-- An alternating binomial sum of successor order is the alternating binomial sum of the
negative forward differences of consecutive values. -/
theorem sum_neg_one_pow_mul_choose_succ (n : ℕ) (f : ℕ → R) :
    (∑ k ∈ Finset.range (n + 2), (-1 : R) ^ k * (n + 1).choose k * f k) =
      ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ k * n.choose k * (f k - f (k + 1)) := by
  have h := congrFun (neg_one_pow_mul_fwdDiff_iter_succ n f 1) 0
  simpa only [neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum,
    smul_eq_mul, mul_one, zero_add, Pi.neg_apply, fwdDiff, neg_sub] using h.symm

/-- **Discrete Leibniz rule.** The `n`-th difference of a scalar product is a binomial sum
of products of differences. In the term with orders `i` and `j`, the second factor is evaluated
at `x + i • h`, where `i + j = n`. No commutativity of the scalar ring is required. -/
theorem fwdDiff_iter_smul [Module R G] (h : M) (f : M → R) (g : M → G) (n : ℕ) :
    Δ_[h]^[n] (f • g) = fun x ↦ ∑ ij ∈ Finset.antidiagonal n,
      n.choose ij.1 • (Δ_[h]^[ij.1] f x • Δ_[h]^[ij.2] g (x + ij.1 • h)) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext x
    rw [Finset.sum_antidiagonal_choose_succ_nsmul (M := G)
      (fun i j ↦ Δ_[h]^[i] f x • Δ_[h]^[j] g (x + i • h)) n]
    simp only [fwdDiff, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    have hc := Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hij).symm
    rw [← hc]
    simp only [Function.iterate_succ_apply', fwdDiff, add_nsmul, one_nsmul,
      add_assoc]
    simp only [smul_sub, sub_smul]
    abel_nf

/-- Range-indexed discrete Leibniz rule for a scalar product. -/
theorem fwdDiff_iter_smul_eq_sum_range [Module R G] (h : M) (f : M → R) (g : M → G)
    (n : ℕ) (x : M) :
    Δ_[h]^[n] (f • g) x = ∑ i ∈ Finset.range (n + 1),
      n.choose i • (Δ_[h]^[i] f x • Δ_[h]^[n - i] g (x + i • h)) := by
  rw [fwdDiff_iter_smul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ n.choose i • (Δ_[h]^[i] f x • Δ_[h]^[j] g (x + i • h))) n

/-- **Unshifted discrete Leibniz rule.** Expanding the shifted differences in the discrete
Leibniz rule by the Gregory–Newton formula expresses the result using differences at `x` only.
In particular, only orders at most `n` of each input occur. -/
theorem fwdDiff_iter_smul_eq_sum_range_sum_range [Module R G] (h : M) (f : M → R)
    (g : M → G) (n : ℕ) (x : M) :
    Δ_[h]^[n] (f • g) x = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
      (n.choose i * i.choose j) • (Δ_[h]^[i] f x • Δ_[h]^[n - i + j] g x) := by
  rw [fwdDiff_iter_smul_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [shift_eq_sum_fwdDiff_iter h (Δ_[h]^[n - i] g) i x, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Function.iterate_add_apply, Nat.add_comm j (n - i), smul_comm, smul_smul,
    smul_comm]

section Pow

open Finset

variable {R : Type*}

/-- **Forward differences of powers at zero.** The `k`-th forward difference of `t ↦ t ^ m` at
`0` is `k!` times the Stirling number of the second kind `S(m, k)`. In particular it vanishes for
`m < k` and equals `k!` for `m = k` (`fwdDiff_iter_eq_factorial`). -/
theorem fwdDiff_iter_pow_apply_zero [Ring R] (k m : ℕ) :
    Δ_[1]^[k] (fun t : R ↦ t ^ m) 0 = k.factorial * m.stirlingSecond k := by
  have h : (fun t : R ↦ t ^ m) =
      ∑ j ∈ range (m + 1), m.stirlingSecond j • fun t : R ↦ (descPochhammer R j).eval t := by
    funext t
    simp [pow_eq_sum_stirlingSecond_mul_descPochhammer_eval m t, nsmul_eq_mul]
  rw [h, fwdDiff_iter_finsetSum, Finset.sum_apply]
  simp only [fwdDiff_iter_const_smul, Pi.smul_apply, fwdDiff_iter_descPochhammer_eval]
  -- only the falling factorial of degree `k` contributes
  rw [sum_eq_single k (fun j _ hjk ↦ ?_) (fun hk ↦ ?_)]
  · simp only [Nat.descFactorial_self, tsub_self, descPochhammer_zero, Polynomial.eval_one,
      mul_one, nsmul_eq_mul]
    exact Nat.cast_comm _ _
  · rcases lt_or_gt_of_ne hjk with hj | hj
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hj]
    · simp [descPochhammer_ne_zero_eval_zero (R := R) (show j - k ≠ 0 by omega)]
  · simp [Nat.stirlingSecond_eq_zero_of_lt (show m < k by simpa using hk)]

/-- **Forward differences of powers with any step.** The `k`-th forward difference of
`y ↦ y ^ m` with step `h` at `x` is `∑ₗ C(m, l) x ^ (m - l) h ^ l k! S(l, k)`, where `S` is the
Stirling number of the second kind. Only the terms with `k ≤ l` are nonzero, and every term is
divisible by `k!`. -/
theorem fwdDiff_iter_pow_eq_sum [CommRing R] (h x : R) (k m : ℕ) :
    Δ_[h]^[k] (fun y : R ↦ y ^ m) x = ∑ l ∈ range (m + 1),
      x ^ (m - l) * h ^ l * m.choose l * (k.factorial * l.stirlingSecond k) := by
  simp_rw [← fwdDiff_iter_pow_apply_zero, fwdDiff_iter_eq_sum_shift, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [add_comm x, add_pow, smul_sum]
  refine sum_congr rfl fun l _ ↦ ?_
  simp only [zsmul_eq_mul, nsmul_eq_mul, zero_add, mul_one]
  ring

end Pow

end TauCeti
