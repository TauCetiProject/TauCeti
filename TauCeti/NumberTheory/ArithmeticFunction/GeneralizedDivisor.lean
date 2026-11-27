/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.Binomial
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.NumberTheory.ArithmeticFunction.Defs
import TauCeti.NumberTheory.ArithmeticFunction.Misc
import TauCeti.RingTheory.Binomial

/-!
# The generalized divisor functions `d_z`

For `z` in a commutative binomial ring `R` (for instance `ℂ`, `ℝ` or `ℤ`), the generalized divisor
function `d_z` is the multiplicative arithmetic function whose value at a prime power `p ^ a` is
the multiset coefficient `Ring.multichoose z a = z (z + 1) ⋯ (z + a - 1) / a!`. Thus
`d_z(n) = ∏_{p ^ a ∥ n} Ring.multichoose z a` for `n ≥ 1`, and `d_z(0) = 0`.

The family is a one-parameter group under Dirichlet convolution: `d_z * d_w = d_{z + w}`. At a
prime power this is the Chu--Vandermonde identity for multiset coefficients
(`TauCeti.Ring.add_multichoose_eq`), via `ArithmeticFunction.mul_apply_prime_pow`. Its first
values are `d_0 = 1`, the unit of Dirichlet convolution, and `d_1 = ζ`, the constant function `1`;
so `d_k = ζ ^ k` counts the ordered factorizations of `n` into `k` factors, and `d_{-1}`, the
convolution inverse of `ζ`, is the Möbius function. Over `ℝ` or `ℂ` the coefficients are bounded
by those of a real parameter: `‖d_z(n)‖ ≤ d_{‖z‖}(n) ≤ (ζ ^ k)(n)` for `‖z‖ ≤ k`. This is the
majorant that makes the Dirichlet series of `d_z` converge absolutely on `Re s > 1`, where it is
the Euler-product power `ζ(s) ^ z` (`TauCeti.NumberTheory.LSeries.Divisor.Generalized`).

## Main definitions

* `TauCeti.ArithmeticFunction.generalizedDivisor z`: the generalized divisor function `d_z`.

## Main results

* `TauCeti.ArithmeticFunction.isMultiplicative_generalizedDivisor` and
  `TauCeti.ArithmeticFunction.generalizedDivisor_apply_prime_pow`: `d_z` is multiplicative with
  `d_z(p ^ a) = Ring.multichoose z a`.
* `TauCeti.ArithmeticFunction.generalizedDivisor_add` and
  `TauCeti.ArithmeticFunction.generalizedDivisor_neg_mul_self`: `d_{z + w} = d_z * d_w`, so
  `d_{-z}` is the Dirichlet inverse of `d_z`.
* `TauCeti.ArithmeticFunction.generalizedDivisor_zero`,
  `TauCeti.ArithmeticFunction.generalizedDivisor_one`,
  `TauCeti.ArithmeticFunction.generalizedDivisor_natCast` and
  `TauCeti.ArithmeticFunction.generalizedDivisor_neg_one`: `d_0 = 1`, `d_1 = ζ`, `d_k = ζ ^ k` and
  `d_{-1} = μ`.
* `TauCeti.ArithmeticFunction.norm_generalizedDivisor_le_of_norm_le`,
  `TauCeti.ArithmeticFunction.norm_generalizedDivisor_le`,
  `TauCeti.ArithmeticFunction.norm_generalizedDivisor_le_zeta_pow` and
  `TauCeti.ArithmeticFunction.generalizedDivisor_le_zeta_pow`: `‖d_z(n)‖ ≤ d_r(n)` for real
  `r ≥ ‖z‖` (in particular `‖d_z(n)‖ ≤ d_{‖z‖}(n)`), `‖d_z(n)‖ ≤ (ζ ^ k)(n)` for `‖z‖ ≤ k`, and
  `d_r(n) ≤ (ζ ^ k)(n)` for real `|r| ≤ k`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, (1.25).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., Chapter II.5.
-/

public section

open Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace TauCeti.ArithmeticFunction

open _root_.ArithmeticFunction

section CommSemiring

variable {R : Type*} [CommSemiring R] [BinomialRing R]

/-- The **generalized divisor function** `d_z`: the multiplicative arithmetic function with
`d_z(p ^ a) = Ring.multichoose z a = z (z + 1) ⋯ (z + a - 1) / a!` at every prime power, that is
`d_z(n) = ∏_{p ^ a ∥ n} Ring.multichoose z a` for `n ≥ 1`, with value `0` at `0`. -/
noncomputable def generalizedDivisor (z : R) : ArithmeticFunction R :=
  ⟨fun n ↦ if n = 0 then 0 else n.factorization.prod fun _ a ↦ Ring.multichoose z a, by simp⟩

/-- Away from `0`, `d_z(n)` is the product of `Ring.multichoose z a` over the prime powers
`p ^ a` exactly dividing `n`. -/
theorem generalizedDivisor_apply (z : R) {n : ℕ} (hn : n ≠ 0) :
    generalizedDivisor z n = n.factorization.prod fun _ a ↦ Ring.multichoose z a := by
  simp [generalizedDivisor, hn]

/-- The generalized divisor function `d_z` is multiplicative. -/
@[arith_mult]
theorem isMultiplicative_generalizedDivisor (z : R) : IsMultiplicative (generalizedDivisor z) := by
  refine ⟨by simp [generalizedDivisor_apply], fun {m n} hmn ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [generalizedDivisor_apply z (mul_ne_zero hm hn), generalizedDivisor_apply z hm,
    generalizedDivisor_apply z hn, Nat.factorization_mul_of_coprime hmn,
    Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]

/-- `d_z(1) = 1`. -/
@[simp]
theorem generalizedDivisor_apply_one (z : R) : generalizedDivisor z 1 = 1 :=
  (isMultiplicative_generalizedDivisor z).map_one

/-- The value of `d_z` at a prime power: `d_z(p ^ a) = Ring.multichoose z a`. -/
@[simp]
theorem generalizedDivisor_apply_prime_pow (z : R) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    generalizedDivisor z (p ^ a) = Ring.multichoose z a := by
  rcases eq_or_ne a 0 with rfl | -
  · simp
  rw [generalizedDivisor_apply z (pow_ne_zero a hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (h := fun _ a ↦ Ring.multichoose z a)
      (Ring.multichoose_zero_right z)]

/-- The value of `d_z` at a prime: `d_z(p) = z`. -/
@[simp]
theorem generalizedDivisor_apply_prime (z : R) {p : ℕ} (hp : p.Prime) :
    generalizedDivisor z p = z := by
  simpa [Ring.multichoose_one_right] using generalizedDivisor_apply_prime_pow z hp 1

/-- `d_0` is the unit `δ₁` of Dirichlet convolution. -/
@[simp]
theorem generalizedDivisor_zero : generalizedDivisor (0 : R) = 1 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_generalizedDivisor 0) 1
    isMultiplicative_one).2 fun p a hp ↦ ?_
  rcases a with _ | a
  · simp
  · simp [hp, hp.ne_one, one_apply_ne]

/-- `d_1` is the constant function `ζ`. -/
@[simp]
theorem generalizedDivisor_one : generalizedDivisor (1 : R) = (ζ : ArithmeticFunction R) := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_generalizedDivisor 1) _
    isMultiplicative_zeta.natCast).2 fun p a hp ↦ ?_
  simp [hp, hp.ne_zero]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [BinomialRing R]

/-- **The convolution law** `d_{z + w} = d_z * d_w`. At a prime power it reads
`Ring.multichoose (z + w) a = ∑_{i + j = a} Ring.multichoose z i * Ring.multichoose w j`, the
Chu--Vandermonde identity for multiset coefficients. -/
theorem generalizedDivisor_add (z w : R) :
    generalizedDivisor (z + w) = generalizedDivisor z * generalizedDivisor w := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_generalizedDivisor _) _
    ((isMultiplicative_generalizedDivisor z).mul (isMultiplicative_generalizedDivisor w))).2
    fun p a hp ↦ ?_
  simp only [mul_apply_prime_pow _ _ hp, generalizedDivisor_apply_prime_pow _ hp,
    TauCeti.Ring.add_multichoose_eq a (Commute.all z w)]

/-- At a natural number `k`, `d_k = ζ ^ k`: `d_k(n)` is the number of ordered factorizations of
`n` into `k` positive factors. -/
@[simp]
theorem generalizedDivisor_natCast (k : ℕ) :
    generalizedDivisor (k : R) = (ζ : ArithmeticFunction R) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, generalizedDivisor_add, ih, generalizedDivisor_one, pow_succ]

/-- The numeric-literal form of `generalizedDivisor_natCast`: for instance `d_2 = ζ ^ 2`. -/
@[simp]
theorem generalizedDivisor_ofNat (k : ℕ) [k.AtLeastTwo] :
    generalizedDivisor (ofNat(k) : R) = (ζ : ArithmeticFunction R) ^ (ofNat(k) : ℕ) :=
  generalizedDivisor_natCast k

/-- `d_{-1}` is the Möbius function, the convolution inverse of `ζ = d_1`. -/
@[simp]
theorem generalizedDivisor_neg_one : generalizedDivisor (-1 : R) = (μ : ArithmeticFunction R) := by
  calc generalizedDivisor (-1 : R)
      = generalizedDivisor (-1 : R) * ((ζ : ArithmeticFunction R) * μ) := by
        rw [coe_zeta_mul_coe_moebius, mul_one]
    _ = μ := by
        rw [← mul_assoc, ← generalizedDivisor_one, ← generalizedDivisor_add, neg_add_cancel,
          generalizedDivisor_zero, one_mul]

/-- `d_{-z}` is the Dirichlet inverse of `d_z`. -/
theorem generalizedDivisor_neg_mul_self (z : R) :
    generalizedDivisor (-z) * generalizedDivisor z = 1 := by
  rw [← generalizedDivisor_add, neg_add_cancel, generalizedDivisor_zero]

end CommRing

/-! ### Bounds for real and complex parameters -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- For a real `r ≥ ‖z‖`, the coefficients of a real or complex parameter `z` are bounded by
those of `r`: `‖d_z(n)‖ ≤ d_r(n)`. -/
theorem norm_generalizedDivisor_le_of_norm_le {z : 𝕜} {r : ℝ} (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖generalizedDivisor z n‖ ≤ generalizedDivisor r n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [generalizedDivisor_apply _ hn, generalizedDivisor_apply _ hn, Finsupp.prod, Finsupp.prod]
  exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    fun _ _ ↦ norm_multichoose_le_of_norm_le hz _)

/-- The coefficients of a real or complex parameter are bounded by those of its modulus:
`‖d_z(n)‖ ≤ d_{‖z‖}(n)`. -/
theorem norm_generalizedDivisor_le (z : 𝕜) (n : ℕ) :
    ‖generalizedDivisor z n‖ ≤ generalizedDivisor ‖z‖ n :=
  norm_generalizedDivisor_le_of_norm_le le_rfl n

/-- For `‖z‖ ≤ k`, `‖d_z(n)‖ ≤ (ζ ^ k)(n)`: the coefficients of `d_z` are dominated by those of
the `k`-fold divisor function `d_k = ζ ^ k`. -/
theorem norm_generalizedDivisor_le_zeta_pow {z : 𝕜} {k : ℕ} (hz : ‖z‖ ≤ k) (n : ℕ) :
    ‖generalizedDivisor z n‖ ≤ ((ζ ^ k : ArithmeticFunction ℕ) n : ℝ) := by
  rw [← natCoe_apply, natCoe_pow, ← generalizedDivisor_natCast]
  exact norm_generalizedDivisor_le_of_norm_le hz n

/-- For real `r` with `|r| ≤ k`, `d_r(n) ≤ (ζ ^ k)(n)`, the number of ordered factorizations of
`n` into `k` factors. -/
theorem generalizedDivisor_le_zeta_pow {r : ℝ} {k : ℕ} (hr : |r| ≤ k) (n : ℕ) :
    generalizedDivisor r n ≤ ((ζ ^ k : ArithmeticFunction ℕ) n : ℝ) :=
  (Real.le_norm_self _).trans (norm_generalizedDivisor_le_zeta_pow (by rwa [Real.norm_eq_abs]) n)

end RCLike

end TauCeti.ArithmeticFunction
