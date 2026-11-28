/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Data.Int.LinearDiophantine.IntervalCount
import TauCeti.NumberTheory.PrimeCounting

/-!
# The multiplicative energy count of Burgess's method

Let `p` be a modulus, `𝒜` a finite set of positive integers at most `A` that are units modulo `p`,
and `I = (M, M + N]` an interval of `N` integers. For `x ∈ ZMod p` let `v(x)` be the number of
pairs `(a, n) ∈ 𝒜 × I` with `n ≡ a x (mod p)`. Burgess's method for character sums needs the
second moment `V₂ = ∑_x v(x)²`, the multiplicative energy of `𝒜` and `I` modulo `p`.

Since every `a ∈ 𝒜` is a unit modulo `p`, the pair `(a, n)` determines `x = n a⁻¹`, so sums over
`x` weighted by `v(x)` are sums over the pairs. In particular `v(x)²` counts the pairs `(a₁, n₁)`,
`(a₂, n₂)` with `n₁ ≡ a₁ x` and `n₂ ≡ a₂ x`, and `V₂` counts the quadruples with
`a₂ n₁ ≡ a₁ n₂ (mod p)`. If `2 A N ≤ p`, Treviño's count `Int.card_filter_mul_eq_mul_le_max` bounds
the solutions for one pair `(a₁, a₂)` by `N gcd(a₁, a₂) / max(a₁, a₂) + 1`, and for `a₁ = a₂` the
solutions are the `N` pairs `n₁ = n₂`. Summing over the pairs `(a₁, a₂)` bounds `V₂`; for the
primes up to `A`, where `gcd(a₁, a₂) = 1` for `a₁ ≠ a₂`, this is McGown's bound
`V₂ ≤ π(A) N + 2 N ∑_{a} (π(a) - 1) / a + 2 ∑_{a} (π(a) - 1)`, the sums over the primes `a ≤ A`.
For a prime modulus `p`, every `a` with `0 < a ≤ A` is a unit modulo `p` once `2 A N ≤ p` and
`N > 0`.

## Main results

* `TauCeti.burgessCount` and `TauCeti.burgessEnergy`: the count `v(x)` and the energy `V₂`.
* `TauCeti.sum_burgessCount_smul`: `∑_x v(x) • w(x)` is the sum of `w(n a⁻¹)` over the pairs
  `(a, n) ∈ 𝒜 × I`; `TauCeti.sum_burgessCount` is `V₁ = ∑_x v(x) = #𝒜 #I`.
* `TauCeti.burgessEnergy_eq_sum_sum_card`: `V₂` is the sum over `(a₁, a₂) ∈ 𝒜 × 𝒜` of the
  number of `(n₁, n₂) ∈ I × I` with `a₂ n₁ ≡ a₁ n₂ (mod p)`.
* `TauCeti.burgessEnergy_le`: if `2 A N ≤ p`, then
  `V₂ ≤ #𝒜 N + ∑_{a₁ ≠ a₂} (N gcd(a₁, a₂) / max(a₁, a₂) + 1)`;
  `TauCeti.burgessEnergy_le_of_prime` is the case of a prime modulus.
* `TauCeti.burgessEnergy_primesLE_le`: McGown's bound for the primes up to `A`;
  `TauCeti.burgessEnergy_primesLE_le_of_prime` is the case of a prime modulus.

## References

* K. McGown, *Norm-Euclidean cyclic fields of prime degree*, Int. J. Number Theory 8 (2012),
  Lemmas A.6 and A.7.
* E. Treviño, *The Burgess inequality and the least k-th power non-residue*, Int. J. Number
  Theory 11 (2015), Lemma 5.
-/

public section

open Finset

namespace TauCeti

variable {p : ℕ}

/-- The count `v(x)`: the number of pairs `(a, n) ∈ 𝒜 × I` with `n ≡ a x (mod p)`. -/
def burgessCount (p : ℕ) (𝒜 : Finset ℕ) (I : Finset ℤ) (x : ZMod p) : ℕ :=
  #{y ∈ 𝒜 ×ˢ I | (y.2 : ZMod p) = y.1 * x}

/-- The definition of `burgessCount`. -/
theorem burgessCount_def (𝒜 : Finset ℕ) (I : Finset ℤ) (x : ZMod p) :
    burgessCount p 𝒜 I x = #{y ∈ 𝒜 ×ˢ I | (y.2 : ZMod p) = y.1 * x} :=
  (rfl)

/-- Without multipliers the count `v(x)` is zero. -/
@[simp]
theorem burgessCount_empty_left (I : Finset ℤ) (x : ZMod p) : burgessCount p ∅ I x = 0 := by
  simp [burgessCount_def]

/-- On the empty interval the count `v(x)` is zero. -/
@[simp]
theorem burgessCount_empty_right (𝒜 : Finset ℕ) (x : ZMod p) : burgessCount p 𝒜 ∅ x = 0 := by
  simp [burgessCount_def]

/-- The multiplicative energy `V₂ = ∑_x v(x)²` of `𝒜` and `I` modulo `p`. -/
def burgessEnergy (p : ℕ) [NeZero p] (𝒜 : Finset ℕ) (I : Finset ℤ) : ℕ :=
  ∑ x : ZMod p, burgessCount p 𝒜 I x ^ 2

/-- The definition of `burgessEnergy`. -/
theorem burgessEnergy_def [NeZero p] (𝒜 : Finset ℕ) (I : Finset ℤ) :
    burgessEnergy p 𝒜 I = ∑ x : ZMod p, burgessCount p 𝒜 I x ^ 2 :=
  (rfl)

/-- Without multipliers the energy `V₂` is zero. -/
@[simp]
theorem burgessEnergy_empty_left [NeZero p] (I : Finset ℤ) : burgessEnergy p ∅ I = 0 := by
  simp [burgessEnergy_def]

/-- On the empty interval the energy `V₂` is zero. -/
@[simp]
theorem burgessEnergy_empty_right [NeZero p] (𝒜 : Finset ℕ) : burgessEnergy p 𝒜 ∅ = 0 := by
  simp [burgessEnergy_def]

/-- For a unit `a` of `ZMod p`, `n = a x` exactly when `n a⁻¹ = x`. -/
private theorem eq_mul_iff_mul_inv_eq {a : ZMod p} (ha : IsUnit a) {n x : ZMod p} :
    n = a * x ↔ n * a⁻¹ = x := by
  obtain ⟨u, rfl⟩ := ha
  rw [ZMod.inv_coe_unit, Units.mul_inv_eq_iff_eq_mul, mul_comm]

/-- **The weighted first moment.** If every `a ∈ 𝒜` is a unit modulo `p`, each pair
`(a, n) ∈ 𝒜 × I` has exactly one `x = n a⁻¹` with `n ≡ a x (mod p)`, so `∑_x v(x) • w(x)` is the
sum of `w(n a⁻¹)` over the pairs `(a, n) ∈ 𝒜 × I`. -/
theorem sum_burgessCount_smul [NeZero p] {M : Type*} [AddCommMonoid M] (𝒜 : Finset ℕ)
    (I : Finset ℤ) (h𝒜 : ∀ a ∈ 𝒜, IsUnit (a : ZMod p)) (w : ZMod p → M) :
    ∑ x : ZMod p, burgessCount p 𝒜 I x • w x =
      ∑ y ∈ 𝒜 ×ˢ I, w ((y.2 : ZMod p) * (y.1 : ZMod p)⁻¹) := by
  rw [← sum_fiberwise' (𝒜 ×ˢ I) (fun y : ℕ × ℤ ↦ (y.2 : ZMod p) * (y.1 : ZMod p)⁻¹) w]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [sum_const, burgessCount_def]
  congr 1
  exact congr_arg card (filter_congr fun y hy ↦ eq_mul_iff_mul_inv_eq (h𝒜 _ (mem_product.1 hy).1))

/-- **The first moment.** If every `a ∈ 𝒜` is a unit modulo `p`, then `V₁ = ∑_x v(x) = #𝒜 #I`. -/
theorem sum_burgessCount [NeZero p] (𝒜 : Finset ℕ) (I : Finset ℤ)
    (h𝒜 : ∀ a ∈ 𝒜, IsUnit (a : ZMod p)) : ∑ x : ZMod p, burgessCount p 𝒜 I x = #𝒜 * #I := by
  simpa [card_product] using sum_burgessCount_smul 𝒜 I h𝒜 fun _ ↦ (1 : ℕ)

/-- **The energy as a count of quadruples.** If every `a ∈ 𝒜` is a unit modulo `p`, then
`V₂ = ∑_x v(x)²` is the sum over `(a₁, a₂) ∈ 𝒜 × 𝒜` of the number of `(n₁, n₂) ∈ I × I` with
`a₂ n₁ ≡ a₁ n₂ (mod p)`. -/
theorem burgessEnergy_eq_sum_sum_card [NeZero p] (𝒜 : Finset ℕ) (I : Finset ℤ)
    (h𝒜 : ∀ a ∈ 𝒜, IsUnit (a : ZMod p)) :
    burgessEnergy p 𝒜 I =
      ∑ a₁ ∈ 𝒜, ∑ a₂ ∈ 𝒜, #{n ∈ I ×ˢ I | (a₂ : ZMod p) * n.1 = a₁ * n.2} := by
  classical
  simp only [burgessEnergy_def, burgessCount_def]
  -- Both sides count the pairs `((a₁, n₁), (a₂, n₂))` with `a₂ n₁ = a₁ n₂`, fibred over
  -- `x = n₁ / a₁` on the left.
  have hleft : ∑ x : ZMod p, #{y ∈ 𝒜 ×ˢ I | (y.2 : ZMod p) = y.1 * x} ^ 2 =
      #{z ∈ (𝒜 ×ˢ I) ×ˢ (𝒜 ×ˢ I) | (z.2.1 : ZMod p) * z.1.2 = z.1.1 * z.2.2} := by
    rw [card_eq_sum_card_fiberwise
      (f := fun z : (ℕ × ℤ) × (ℕ × ℤ) ↦ (z.1.2 : ZMod p) * (z.1.1 : ZMod p)⁻¹)
      (t := univ) fun _ _ ↦ mem_coe.mpr (mem_univ _)]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [sq, ← card_product]
    congr 1
    ext ⟨⟨a₁, n₁⟩, ⟨a₂, n₂⟩⟩
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨ha₁, hn₁⟩, h₁⟩, ⟨⟨ha₂, hn₂⟩, h₂⟩⟩
      refine ⟨⟨⟨⟨ha₁, hn₁⟩, ha₂, hn₂⟩, ?_⟩, (eq_mul_iff_mul_inv_eq (h𝒜 a₁ ha₁)).1 h₁⟩
      rw [h₁, h₂]
      ring
    · rintro ⟨⟨⟨⟨ha₁, hn₁⟩, ha₂, hn₂⟩, h⟩, hx⟩
      have h₁ := (eq_mul_iff_mul_inv_eq (h𝒜 a₁ ha₁)).2 hx
      refine ⟨⟨⟨ha₁, hn₁⟩, h₁⟩, ⟨ha₂, hn₂⟩, (h𝒜 a₁ ha₁).mul_left_cancel ?_⟩
      rw [← h, h₁]
      ring
  rw [hleft]
  simp only [card_filter, sum_product]
  exact sum_congr rfl fun a₁ _ ↦ sum_comm

/-- **The multiplicative energy count.** Let `𝒜` be a finite set of positive integers at most `A`
that are units modulo `p`. If `2 A N ≤ p`, then the energy `V₂` of `𝒜` and `(M, M + N]` satisfies
`V₂ ≤ #𝒜 N + ∑_{a₁ ≠ a₂} (N gcd(a₁, a₂) / max(a₁, a₂) + 1)`. -/
theorem burgessEnergy_le [NeZero p] (𝒜 : Finset ℕ) {A : ℕ} (h𝒜 : ∀ a ∈ 𝒜, 0 < a ∧ a ≤ A)
    (hu : ∀ a ∈ 𝒜, IsUnit (a : ZMod p)) (M : ℤ) (N : ℕ) (h : 2 * A * N ≤ p) :
    (burgessEnergy p 𝒜 (Ioc M (M + N)) : ℝ) ≤
      #𝒜 * N + ∑ a₁ ∈ 𝒜, ∑ a₂ ∈ 𝒜 with a₂ ≠ a₁, ((N * Nat.gcd a₁ a₂ / max a₁ a₂ : ℝ) + 1) := by
  classical
  have hpair {a₁ a₂ : ℕ} (ha₁ : a₁ ∈ 𝒜) (ha₂ : a₂ ∈ 𝒜) : (a₁ + a₂) * N ≤ p :=
    le_trans (Nat.mul_le_mul_right N (by have := (h𝒜 a₁ ha₁).2; have := (h𝒜 a₂ ha₂).2; omega)) h
  rw [burgessEnergy_eq_sum_sum_card 𝒜 _ hu, Nat.cast_sum, ← nsmul_eq_mul, ← sum_const,
    ← sum_add_distrib]
  refine sum_le_sum fun a₁ ha₁ ↦ ?_
  rw [Nat.cast_sum, ← add_sum_erase _ _ ha₁, filter_ne']
  have hdiag := Int.card_filter_mul_eq_mul_self (p := p) (h𝒜 a₁ ha₁).1 M
    (le_trans (Nat.mul_le_mul_right N (by have := (h𝒜 a₁ ha₁).2; omega)) h)
  refine add_le_add (by rw [hdiag]) (sum_le_sum fun a₂ ha₂ ↦ ?_)
  have ha₂' := mem_of_mem_erase ha₂
  exact Int.card_filter_mul_eq_mul_le_max (lt_max_of_lt_right (h𝒜 a₂ ha₂').1) M (hpair ha₁ ha₂')

/-- **The multiplicative energy count for a prime modulus.** Let `p` be prime and `𝒜` a finite set
of positive integers at most `A`. If `2 A N ≤ p`, then the energy `V₂` of `𝒜` and `(M, M + N]`
satisfies `V₂ ≤ #𝒜 N + ∑_{a₁ ≠ a₂} (N gcd(a₁, a₂) / max(a₁, a₂) + 1)`. -/
theorem burgessEnergy_le_of_prime [Fact p.Prime] (𝒜 : Finset ℕ) {A : ℕ}
    (h𝒜 : ∀ a ∈ 𝒜, 0 < a ∧ a ≤ A) (M : ℤ) (N : ℕ) (h : 2 * A * N ≤ p) :
    (burgessEnergy p 𝒜 (Ioc M (M + N)) : ℝ) ≤
      #𝒜 * N + ∑ a₁ ∈ 𝒜, ∑ a₂ ∈ 𝒜 with a₂ ≠ a₁, ((N * Nat.gcd a₁ a₂ / max a₁ a₂ : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [show (burgessEnergy p 𝒜 (Ioc M (M + (0 : ℕ))) : ℝ) = 0 by simp]
    positivity
  -- Every multiplier is a unit modulo `p`, since `0 < a ≤ A < p`.
  refine burgessEnergy_le 𝒜 h𝒜 (fun a ha ↦ ?_) M N h
  rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  refine Nat.not_dvd_of_pos_of_lt (h𝒜 a ha).1 ?_
  have := Nat.mul_le_mul_left (2 * A) hN
  nlinarith [(h𝒜 a ha).1, (h𝒜 a ha).2]

/-- The right-hand side of `burgessEnergy_le` for the primes up to `A`: distinct primes are
coprime, and `π(a) - 1` of the primes up to `A` are below a prime `a ≤ A`. -/
private theorem sum_sum_primesLE_eq (A N : ℕ) :
    (#A.primesLE * N : ℝ) + ∑ a₁ ∈ A.primesLE, ∑ a₂ ∈ A.primesLE with a₂ ≠ a₁,
        ((N * Nat.gcd a₁ a₂ / max a₁ a₂ : ℝ) + 1) =
      A.primeCounting * N + 2 * N * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) / a +
        2 * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) := by
  have hgcd (a₁ : ℕ) (ha₁ : a₁ ∈ A.primesLE) :
      ∑ a₂ ∈ A.primesLE with a₂ ≠ a₁, ((N * Nat.gcd a₁ a₂ / max a₁ a₂ : ℝ) + 1) =
        ∑ a₂ ∈ A.primesLE with a₂ ≠ a₁, ((N : ℝ) / (max a₁ a₂ : ℕ) + 1) := by
    refine sum_congr rfl fun a₂ ha₂ ↦ ?_
    obtain ⟨ha₂, hne⟩ := mem_filter.mp ha₂
    rw [(Nat.coprime_primes (Nat.prime_of_mem_primesLE ha₁)
      (Nat.prime_of_mem_primesLE ha₂)).mpr hne.symm, Nat.cast_one, mul_one]
  have hbelow (a : ℕ) (ha : a ∈ A.primesLE) :
      (#{b ∈ A.primesLE | b < a} : ℝ) = a.primeCounting - 1 := by
    have hp := Nat.prime_of_mem_primesLE ha
    rw [Nat.Prime.card_primesLE_filter_lt hp (Nat.le_of_mem_primesLE ha),
      Nat.cast_pred (Nat.pos_of_ne_zero (Nat.primeCounting_eq_zero_iff.not.2 hp.one_lt.not_ge))]
  have hsum : ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) * ((N : ℝ) / a + 1) =
      N * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) / a +
        ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun a _ ↦ by ring
  rw [sum_congr rfl hgcd, sum_sum_filter_ne_max_eq _ fun m : ℕ ↦ (N : ℝ) / m + 1,
    Nat.primesLE_card_eq_primeCounting,
    sum_congr rfl fun a ha ↦ by rw [nsmul_eq_mul, hbelow a ha], hsum, nsmul_eq_mul,
    Nat.cast_ofNat]
  ring

/-- **McGown's bound for prime multipliers.** Let `v(x)` be the number of pairs `(a, n)` of a
prime `a ≤ A` and `n ∈ (M, M + N]` with `n ≡ a x (mod p)`. If the primes `a ≤ A` are units
modulo `p` and `2 A N ≤ p`, then
`∑_x v(x)² ≤ π(A) N + 2 N ∑_a (π(a) - 1) / a + 2 ∑_a (π(a) - 1)`, the sums over the primes
`a ≤ A`. -/
theorem burgessEnergy_primesLE_le [NeZero p] {A : ℕ}
    (hu : ∀ a ∈ A.primesLE, IsUnit (a : ZMod p)) (M : ℤ) (N : ℕ) (h : 2 * A * N ≤ p) :
    (burgessEnergy p A.primesLE (Ioc M (M + N)) : ℝ) ≤
      A.primeCounting * N + 2 * N * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) / a +
        2 * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) :=
  (burgessEnergy_le _ (fun _ ha ↦ ⟨(Nat.prime_of_mem_primesLE ha).pos,
    Nat.le_of_mem_primesLE ha⟩) hu M N h).trans_eq (sum_sum_primesLE_eq A N)

/-- **McGown's bound for prime multipliers and a prime modulus.** Let `p` be prime and let `v(x)`
be the number of pairs `(a, n)` of a prime `a ≤ A` and `n ∈ (M, M + N]` with `n ≡ a x (mod p)`.
If `2 A N ≤ p`, then `∑_x v(x)² ≤ π(A) N + 2 N ∑_a (π(a) - 1) / a + 2 ∑_a (π(a) - 1)`, the sums
over the primes `a ≤ A`. -/
theorem burgessEnergy_primesLE_le_of_prime [Fact p.Prime] {A : ℕ} (M : ℤ) (N : ℕ)
    (h : 2 * A * N ≤ p) :
    (burgessEnergy p A.primesLE (Ioc M (M + N)) : ℝ) ≤
      A.primeCounting * N + 2 * N * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) / a +
        2 * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) :=
  (burgessEnergy_le_of_prime _ (fun _ ha ↦ ⟨(Nat.prime_of_mem_primesLE ha).pos,
    Nat.le_of_mem_primesLE ha⟩) M N h).trans_eq (sum_sum_primesLE_eq A N)

end TauCeti
