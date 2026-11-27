/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.Binomial
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.NumberTheory.ArithmeticFunction.Defs
import TauCeti.NumberTheory.ArithmeticFunction.Misc
import TauCeti.RingTheory.Binomial

/-!
# The generalized divisor functions `d_z`

For an element `z` of a commutative binomial ring `R`, such as `ℂ`, the generalized divisor
function `d_z` is the multiplicative arithmetic function whose value at a prime power `p ^ k` is
the multiset coefficient

`Ring.multichoose z k = z (z + 1) ⋯ (z + k - 1) / k!`,

so `d_z(n) = ∏_{p ^ k ∥ n} Ring.multichoose z k` for `n ≥ 1` and `d_z(0) = 0`. These are the
coefficients of the formal power `ζ ^ z`: at each prime, `∑_k Ring.multichoose z k X ^ k` is the
binomial series of `(1 - X) ^ (-z)`. Accordingly `z ↦ d_z` turns addition into Dirichlet
convolution, `d_0` is the unit `1`, `d_1 = ζ`, `d_{-1} = μ`, and for `k : ℕ` the function `d_k`
is the `k`-fold divisor function `ζ ^ k`, which counts ordered factorizations into `k` factors.
For `z` in `ℝ` or `ℂ`, `‖d_z(n)‖ ≤ d_r(n)` whenever `‖z‖ ≤ r`, so `d_z` is dominated by the
divisor function `ζ ^ ⌈‖z‖⌉₊`; this bound gives the absolute convergence of the Dirichlet series
of `d_z` on `Re s > 1`, where it is the Euler-product power `ζ(s) ^ z`.

## Main definitions

* `TauCeti.ArithmeticFunction.generalizedDivisor z`: the generalized divisor function `d_z`.

## Main results

* `TauCeti.ArithmeticFunction.isMultiplicative_generalizedDivisor`: `d_z` is multiplicative.
* `TauCeti.ArithmeticFunction.generalizedDivisor_apply_prime_pow`:
  `d_z(p ^ k) = Ring.multichoose z k`.
* `TauCeti.ArithmeticFunction.generalizedDivisor_add`: `d_{z + w} = d_z * d_w`.
* `TauCeti.ArithmeticFunction.generalizedDivisor_zero`, `generalizedDivisor_one`,
  `generalizedDivisor_neg_one` and `generalizedDivisor_natCast`: `d_0 = 1`, `d_1 = ζ`,
  `d_{-1} = μ` and `d_k = ζ ^ k`.
* `TauCeti.ArithmeticFunction.norm_generalizedDivisor_le` and
  `TauCeti.ArithmeticFunction.norm_generalizedDivisor_le_zeta_pow`: `‖d_z(n)‖ ≤ d_r(n)` for
  `‖z‖ ≤ r`, and `‖d_z(n)‖ ≤ (ζ ^ ⌈‖z‖⌉₊)(n)`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, (1.25).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., Chapter II.5.
-/

public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace TauCeti.ArithmeticFunction

section CommSemiring

variable {R : Type*} [CommSemiring R] [BinomialRing R]

/-- The generalized divisor function `d_z`: the multiplicative arithmetic function with
`d_z(p ^ k) = Ring.multichoose z k = z (z + 1) ⋯ (z + k - 1) / k!` at prime powers, that is
`d_z(n) = ∏_{p ^ k ∥ n} Ring.multichoose z k` for `n ≠ 0`, and `d_z(0) = 0`. -/
noncomputable def generalizedDivisor (z : R) : ArithmeticFunction R :=
  ⟨fun n ↦ if n = 0 then 0 else n.factorization.prod fun _ k ↦ Ring.multichoose z k, by simp⟩

/-- Away from `0`, `d_z(n)` is the product of `Ring.multichoose z k` over the prime powers
`p ^ k` exactly dividing `n`. -/
theorem generalizedDivisor_apply (z : R) {n : ℕ} (hn : n ≠ 0) :
    generalizedDivisor z n = n.factorization.prod fun _ k ↦ Ring.multichoose z k := by
  simp [generalizedDivisor, hn]

/-- The generalized divisor function `d_z` is multiplicative. -/
@[arith_mult]
theorem isMultiplicative_generalizedDivisor (z : R) :
    IsMultiplicative (generalizedDivisor z) := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨?_, fun {m n} hm hn hmn ↦ ?_⟩
  · rw [generalizedDivisor_apply z one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  · rw [generalizedDivisor_apply z (mul_ne_zero hm hn), generalizedDivisor_apply z hm,
      generalizedDivisor_apply z hn, Nat.factorization_mul_of_coprime hmn,
      Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]

/-- `d_z(1) = 1`. -/
@[simp]
theorem generalizedDivisor_apply_one (z : R) : generalizedDivisor z 1 = 1 :=
  (isMultiplicative_generalizedDivisor z).map_one

/-- The value of `d_z` at a prime power: `d_z(p ^ k) = Ring.multichoose z k`. -/
@[simp]
theorem generalizedDivisor_apply_prime_pow (z : R) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    generalizedDivisor z (p ^ k) = Ring.multichoose z k := by
  rw [generalizedDivisor_apply z (pow_ne_zero k hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (by exact Ring.multichoose_zero_right z)]

/-- The value of `d_z` at a prime: `d_z(p) = z`. -/
@[simp]
theorem generalizedDivisor_apply_prime (z : R) {p : ℕ} (hp : p.Prime) :
    generalizedDivisor z p = z := by
  simpa using generalizedDivisor_apply_prime_pow z hp 1

/-- `d_0` is the unit `1` of Dirichlet convolution. -/
@[simp]
theorem generalizedDivisor_zero : generalizedDivisor (0 : R) = 1 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_generalizedDivisor _) _
    isMultiplicative_one).2 fun p k hp ↦ ?_
  rw [generalizedDivisor_apply_prime_pow _ hp, ArithmeticFunction.one_apply]
  cases k with
  | zero => simp
  | succ k => simp [Ring.multichoose_zero_succ, hp.ne_one]

/-- `d_1` is the constant function `ζ`. -/
@[simp]
theorem generalizedDivisor_one : generalizedDivisor (1 : R) = ζ := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_generalizedDivisor _) _
    isMultiplicative_zeta.natCast).2 fun p k hp ↦ ?_
  rw [generalizedDivisor_apply_prime_pow _ hp, Ring.multichoose_one, natCoe_apply,
    zeta_apply_ne (pow_ne_zero k hp.ne_zero), Nat.cast_one]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [BinomialRing R]

/-- **The convolution law** `d_{z + w} = d_z * d_w`. Both sides are multiplicative, and at a prime
power this is the Chu–Vandermonde identity for multiset coefficients. -/
theorem generalizedDivisor_add (z w : R) :
    generalizedDivisor (z + w) = generalizedDivisor z * generalizedDivisor w := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_generalizedDivisor _) _
    ((isMultiplicative_generalizedDivisor z).mul (isMultiplicative_generalizedDivisor w))).2
    fun p k hp ↦ ?_
  simp only [mul_apply_prime_pow _ _ hp, generalizedDivisor_apply_prime_pow _ hp]
  exact TauCeti.Ring.add_multichoose_eq k (Commute.all z w)

/-- For `k : ℕ`, `d_k` is the `k`-fold divisor function `ζ ^ k`, the number of ordered
factorizations into `k` positive factors. -/
theorem generalizedDivisor_natCast (k : ℕ) :
    generalizedDivisor (k : R) = ↑(ζ ^ k : ArithmeticFunction ℕ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, generalizedDivisor_add, ih, generalizedDivisor_one,
      natCoe_pow, natCoe_pow, pow_succ]

/-- `d_{-1}` is the Möbius function `μ`, the Dirichlet inverse of `d_1 = ζ`. -/
@[simp]
theorem generalizedDivisor_neg_one : generalizedDivisor (-1 : R) = μ := by
  have h : generalizedDivisor (-1 : R) * ζ = 1 := by
    rw [← generalizedDivisor_one, ← generalizedDivisor_add, neg_add_cancel, generalizedDivisor_zero]
  calc generalizedDivisor (-1 : R) = generalizedDivisor (-1 : R) * (ζ * μ) := by
        rw [coe_zeta_mul_coe_moebius, mul_one]
    _ = μ := by rw [← mul_assoc, h, one_mul]

end CommRing

section RCLike

variable {𝕂 : Type*} [RCLike 𝕂]

/-- `‖d_z(n)‖ ≤ d_r(n)` whenever `‖z‖ ≤ r`: at each prime power,
`‖Ring.multichoose z k‖ ≤ Ring.multichoose r k`. -/
theorem norm_generalizedDivisor_le {z : 𝕂} {r : ℝ} (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖generalizedDivisor z n‖ ≤ generalizedDivisor r n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [generalizedDivisor_apply z hn, generalizedDivisor_apply (r : ℝ) hn, Finsupp.prod,
    Finsupp.prod, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun _ _ ↦
    TauCeti.norm_multichoose_le_of_norm_le hz _

/-- The generalized divisor function `d_z` is dominated by the divisor function
`ζ ^ ⌈‖z‖⌉₊`. -/
theorem norm_generalizedDivisor_le_zeta_pow (z : 𝕂) (n : ℕ) :
    ‖generalizedDivisor z n‖ ≤ (ζ ^ ⌈‖z‖⌉₊ : ArithmeticFunction ℕ) n := by
  have h := norm_generalizedDivisor_le (Nat.le_ceil ‖z‖) n
  rwa [generalizedDivisor_natCast, natCoe_apply] at h

end RCLike

/-! ### Examples -/

/-- `d_{1/2}(p ^ 2) = 3/8`: the multiset coefficient `(1/2)(3/2)/2!`. -/
example {p : ℕ} (hp : p.Prime) : generalizedDivisor (2⁻¹ : ℂ) (p ^ 2) = 3 / 8 := by
  rw [generalizedDivisor_apply_prime_pow _ hp, TauCeti.Ring.multichoose_inv_two]
  norm_num [Nat.centralBinom, Nat.choose]

/-- `d_3(4) = 6`: the ordered factorizations of `4` into three factors are the three
arrangements of `4 · 1 · 1` and the three of `2 · 2 · 1`. -/
example : generalizedDivisor (3 : ℂ) 4 = 6 := by
  have h := generalizedDivisor_apply_prime_pow (3 : ℂ) Nat.prime_two 2
  rw [Ring.multichoose_eq, show (3 : ℂ) + (2 : ℕ) - 1 = (4 : ℕ) by norm_num,
    Ring.choose_natCast] at h
  norm_num [Nat.choose] at h
  exact h

end TauCeti.ArithmeticFunction
