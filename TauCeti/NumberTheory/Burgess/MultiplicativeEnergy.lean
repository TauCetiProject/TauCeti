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
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Data.Int.CardIntervalMod
import TauCeti.NumberTheory.PrimeCounting

/-!
# The multiplicative energy count of Burgess's method

Let `p` be a modulus (a prime for the bounds), `𝒜` a finite set of positive integers at most
`A`, and `I = (M, M + N]` an interval of `N` integers. For `x ∈ ZMod p` let `v(x)` be the number
of pairs `(a, n) ∈ 𝒜 × I` with `n ≡ a x (mod p)`. Burgess's method for character sums needs
the second moment `V₂ = ∑_x v(x)²`, the multiplicative energy of `𝒜` and `I` modulo `p`.

If every `a ∈ 𝒜` is a unit modulo `p`, then `v(x)²` counts the pairs `(a₁, n₁)`, `(a₂, n₂)` with
`n₁ ≡ a₁ x` and `n₂ ≡ a₂ x`, and `x = n₁ a₁⁻¹` is determined by the first pair. So `V₂` counts the
quadruples with `a₂ n₁ ≡ a₁ n₂ (mod p)`. If `2 A N ≤ p`, two solutions `(n₁, n₂)` and `(n₁', n₂')`
for the same `(a₁, a₂)` satisfy `a₂ (n₁ - n₁') = a₁ (n₂ - n₂')` in `ℤ`, because the difference of
the two sides is divisible by `p` and smaller than `p` in absolute value. With
`g = gcd(a₁, a₂)`, the `n₂` of the solutions then lie in one residue class modulo `a₂ / g` and
determine `n₁`, so there are at most `N g / a₂ + 1` solutions. For `a₁ = a₂` the solutions are the
`N` pairs `n₁ = n₂`. Summing over the pairs `(a₁, a₂)` bounds `V₂`; for the primes up to `A`, where
`g = 1` for `a₁ ≠ a₂`, this is McGown's bound
`V₂ ≤ π(A) N + 2 N ∑_{a} (π(a) - 1) / a + 2 ∑_{a} (π(a) - 1)`, the sums over the primes `a ≤ A`.

## Main results

* `TauCeti.burgessCount` and `TauCeti.burgessEnergy`: the count `v(x)` and the energy `V₂`.
* `TauCeti.sum_burgessCount`: `V₁ = ∑_x v(x) = #𝒜 #I`.
* `TauCeti.burgessEnergy_eq_sum_sum_card`: `V₂` is the sum over `(a₁, a₂) ∈ 𝒜 × 𝒜` of the
  number of `(n₁, n₂) ∈ I × I` with `a₂ n₁ ≡ a₁ n₂ (mod p)`.
* `TauCeti.card_filter_mul_eq_mul_le`: if `(a₁ + a₂) N ≤ p`, there are at most
  `N gcd(a₁, a₂) / a₂ + 1` such pairs `(n₁, n₂)`; `TauCeti.card_filter_mul_eq_mul_le_max` is the
  same bound with `max(a₁, a₂)` in place of `a₂`.
* `TauCeti.burgessEnergy_le`: if `2 A N ≤ p`, then
  `V₂ ≤ #𝒜 N + ∑_{a₁ ≠ a₂} (N gcd(a₁, a₂) / max(a₁, a₂) + 1)`.
* `TauCeti.sum_sum_filter_ne_max_eq`: the sum of `g(max(a₁, a₂))` over the ordered pairs of
  distinct elements of `𝒜` is `2 ∑_{a ∈ 𝒜} #{b ∈ 𝒜 | b < a} g(a)`.
* `TauCeti.burgessEnergy_primesLE_le`: McGown's bound for the primes up to `A`.

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

/-- The multiplicative energy `V₂ = ∑_x v(x)²` of `𝒜` and `I` modulo `p`. -/
def burgessEnergy (p : ℕ) [NeZero p] (𝒜 : Finset ℕ) (I : Finset ℤ) : ℕ :=
  ∑ x : ZMod p, burgessCount p 𝒜 I x ^ 2

/-- The definition of `burgessEnergy`. -/
theorem burgessEnergy_def [NeZero p] (𝒜 : Finset ℕ) (I : Finset ℤ) :
    burgessEnergy p 𝒜 I = ∑ x : ZMod p, burgessCount p 𝒜 I x ^ 2 :=
  (rfl)

/-- **The first moment.** If every `a ∈ 𝒜` is a unit modulo `p`, each pair `(a, n) ∈ 𝒜 × I`
has exactly one `x = n a⁻¹` with `n ≡ a x (mod p)`, so `V₁ = ∑_x v(x) = #𝒜 #I`. -/
theorem sum_burgessCount [NeZero p] (𝒜 : Finset ℕ) (I : Finset ℤ)
    (h𝒜 : ∀ a ∈ 𝒜, IsUnit (a : ZMod p)) : ∑ x : ZMod p, burgessCount p 𝒜 I x = #𝒜 * #I := by
  simp only [burgessCount_def]
  rw [← card_product, card_eq_sum_card_fiberwise (s := 𝒜 ×ˢ I)
    (f := fun y : ℕ × ℤ ↦ (y.2 : ZMod p) * (y.1 : ZMod p)⁻¹) (t := univ)
    fun _ _ ↦ mem_coe.mpr (mem_univ _)]
  refine sum_congr rfl fun x _ ↦ congr_arg card (filter_congr fun y hy ↦ ?_)
  have hu := h𝒜 y.1 (mem_product.mp hy).1
  constructor
  · intro h
    rw [h, mul_comm, ← mul_assoc, ZMod.inv_mul_of_unit _ hu, one_mul]
  · rintro rfl
    rw [mul_comm (y.2 : ZMod p), ← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]

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
      refine ⟨⟨⟨⟨ha₁, hn₁⟩, ha₂, hn₂⟩, ?_⟩, ?_⟩
      · rw [h₁, h₂]
        ring
      · rw [h₁, mul_comm, ← mul_assoc, ZMod.inv_mul_of_unit _ (h𝒜 a₁ ha₁), one_mul]
    · rintro ⟨⟨⟨⟨ha₁, hn₁⟩, ha₂, hn₂⟩, h⟩, rfl⟩
      refine ⟨⟨⟨ha₁, hn₁⟩, ?_⟩, ⟨ha₂, hn₂⟩, ?_⟩
      · rw [mul_comm (n₁ : ZMod p), ← mul_assoc, ZMod.mul_inv_of_unit _ (h𝒜 a₁ ha₁), one_mul]
      · rw [← mul_assoc, h, mul_comm (a₁ : ZMod p), mul_assoc, ZMod.mul_inv_of_unit _ (h𝒜 a₁ ha₁),
          mul_one]
  rw [hleft]
  simp only [card_filter, sum_product]
  exact sum_congr rfl fun a₁ _ ↦ sum_comm

/-- Two pairs `(n₁, n₂)`, `(n₁', n₂')` in `(M, M + N]²` with `a₂ n₁ ≡ a₁ n₂` modulo `p` satisfy
`a₂ (n₁ - n₁') = a₁ (n₂ - n₂')` in `ℤ` when `0 < a₂` and `(a₁ + a₂) N ≤ p`: the difference of
the two sides is divisible by `p` and at most `(a₁ + a₂) (N - 1) < p` in absolute value. -/
private theorem mul_sub_eq_mul_sub {a₁ a₂ : ℕ} (ha₂ : 0 < a₂) {M : ℤ} {N : ℕ}
    (h : (a₁ + a₂) * N ≤ p) {n n' : ℤ × ℤ} (hn : n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N))
    (hn' : n' ∈ Ioc M (M + N) ×ˢ Ioc M (M + N)) (h₁ : (a₂ : ZMod p) * n.1 = a₁ * n.2)
    (h₂ : (a₂ : ZMod p) * n'.1 = a₁ * n'.2) :
    (a₂ : ℤ) * (n.1 - n'.1) = a₁ * (n.2 - n'.2) := by
  simp only [mem_product, mem_Ioc] at hn hn'
  rw [← sub_eq_zero]
  refine Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_) ?_
  · push_cast
    linear_combination h₁ - h₂
  · have hp : ((a₁ : ℤ) + a₂) * N ≤ p := by exact_mod_cast h
    have hd₁ : |n.1 - n'.1| ≤ N - 1 := abs_sub_le_iff.mpr ⟨by omega, by omega⟩
    have hd₂ : |n.2 - n'.2| ≤ N - 1 := abs_sub_le_iff.mpr ⟨by omega, by omega⟩
    have ha₂' : (1 : ℤ) ≤ a₂ := by exact_mod_cast ha₂
    calc |(a₂ : ℤ) * (n.1 - n'.1) - a₁ * (n.2 - n'.2)|
        ≤ |(a₂ : ℤ) * (n.1 - n'.1)| + |(a₁ : ℤ) * (n.2 - n'.2)| := abs_sub _ _
      _ = a₂ * |n.1 - n'.1| + a₁ * |n.2 - n'.2| := by
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
      _ ≤ a₂ * (N - 1) + a₁ * (N - 1) := by gcongr
      _ < p := by nlinarith [hp, ha₂']

/-- **The number of solutions for one pair of multipliers.** If `0 < a₂` and `(a₁ + a₂) N ≤ p`,
at most `N gcd(a₁, a₂) / a₂ + 1` pairs `(n₁, n₂) ∈ (M, M + N]²` satisfy `a₂ n₁ ≡ a₁ n₂ (mod p)`:
their `n₂` lie in one residue class modulo `a₂ / gcd(a₁, a₂)` and determine `n₁`. -/
theorem card_filter_mul_eq_mul_le {a₁ a₂ : ℕ} (ha₂ : 0 < a₂) (M : ℤ) {N : ℕ}
    (h : (a₁ + a₂) * N ≤ p) :
    (#{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₂ : ZMod p) * n.1 = a₁ * n.2} : ℝ) ≤
      N * Nat.gcd a₁ a₂ / a₂ + 1 := by
  set S := {n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₂ : ZMod p) * n.1 = a₁ * n.2}
  rcases S.eq_empty_or_nonempty with hS | ⟨n₀, hn₀⟩
  · rw [hS, card_empty, Nat.cast_zero]
    positivity
  set g := Nat.gcd a₁ a₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ ha₂
  have hb : 0 < a₂ / g := Nat.div_pos (Nat.gcd_le_right _ ha₂) hg
  obtain ⟨hn₀I, hn₀'⟩ := mem_filter.mp hn₀
  -- Every solution has `n₂ ≡ n₀₂ (mod a₂ / g)`.
  set T : Finset ℤ := {m ∈ Ico (M + 1) (M + N + 1) | m ≡ n₀.2 [ZMOD ((a₂ / g : ℕ) : ℤ)]}
  have hmaps : Set.MapsTo (fun n : ℤ × ℤ ↦ n.2) S T := by
    intro n hn
    obtain ⟨hnI, hn'⟩ := mem_filter.mp hn
    have key := mul_sub_eq_mul_sub ha₂ h hnI hn₀I hn' hn₀'
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp only [mem_product, mem_Ioc, mem_Ico] at hnI ⊢
      omega
    · -- Divide `a₂ (n₁ - n₀₁) = a₁ (n₂ - n₀₂)` by `g`; then `a₂ / g` is prime to `a₁ / g`.
      have hcop : IsCoprime ((a₂ / g : ℕ) : ℤ) ((a₁ / g : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr (Nat.coprime_div_gcd_div_gcd hg).symm
      have hdiv : ((a₂ / g : ℕ) : ℤ) * (n.1 - n₀.1) = ((a₁ / g : ℕ) : ℤ) * (n.2 - n₀.2) := by
        have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
        refine mul_left_cancel₀ hg' ?_
        rw [← mul_assoc, ← mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul,
          Nat.mul_div_cancel' (Nat.gcd_dvd_right a₁ a₂),
          Nat.mul_div_cancel' (Nat.gcd_dvd_left a₁ a₂), key]
      exact (Int.modEq_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left ⟨_, hdiv.symm⟩)).symm
  -- A solution is determined by its `n₂`.
  have hinj : Set.InjOn (fun n : ℤ × ℤ ↦ n.2) S := by
    intro n hn n' hn' h2
    obtain ⟨hnI, hn⟩ := mem_filter.mp hn
    obtain ⟨hn'I, hn'⟩ := mem_filter.mp hn'
    have key := mul_sub_eq_mul_sub ha₂ h hnI hn'I hn hn'
    simp only at h2
    rw [h2, sub_self, mul_zero, mul_eq_zero, sub_eq_zero] at key
    exact Prod.ext (key.resolve_left (by exact_mod_cast ha₂.ne')) h2
  have hcount := Int.card_Ico_filter_modEq_le (r := ((a₂ / g : ℕ) : ℤ)) (by exact_mod_cast hb)
    (a := M + 1) (b := M + N + 1) (by omega) n₀.2
  have hb' : (((a₂ / g : ℕ) : ℤ) : ℚ) = (a₂ : ℚ) / g := by
    rw [Int.cast_natCast, Nat.cast_div (Nat.gcd_dvd_right a₁ a₂) (by exact_mod_cast hg.ne')]
  rw [hb'] at hcount
  have hq : (#S : ℚ) ≤ N * g / a₂ + 1 :=
    calc (#S : ℚ) ≤ #T := by exact_mod_cast card_le_card_of_injOn _ hmaps hinj
      _ ≤ _ := hcount
      _ = N * g / a₂ + 1 := by
        push_cast
        rw [div_div_eq_mul_div]
        ring
  simpa using (Rat.cast_le (K := ℝ)).mpr hq

/-- The bound of `card_filter_mul_eq_mul_le` with `max(a₁, a₂)` in place of `a₂`. -/
theorem card_filter_mul_eq_mul_le_max {a₁ a₂ : ℕ} (ha : 0 < max a₁ a₂) (M : ℤ) {N : ℕ}
    (h : (a₁ + a₂) * N ≤ p) :
    (#{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₂ : ZMod p) * n.1 = a₁ * n.2} : ℝ) ≤
      N * Nat.gcd a₁ a₂ / max a₁ a₂ + 1 := by
  rcases le_total a₁ a₂ with h₁₂ | h₂₁
  · rw [max_eq_right h₁₂] at ha ⊢
    exact card_filter_mul_eq_mul_le ha M h
  · -- Swap the two coordinates to exchange the roles of `a₁` and `a₂`.
    rw [max_eq_left h₂₁] at ha ⊢
    rw [Nat.gcd_comm]
    have hswap : #{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₂ : ZMod p) * n.1 = a₁ * n.2} =
        #{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₁ : ZMod p) * n.1 = a₂ * n.2} := by
      refine card_bij (fun n _ ↦ n.swap) (fun n hn ↦ ?_) (fun _ _ _ _ h ↦ Prod.swap_injective h)
        fun n hn ↦ ⟨n.swap, ?_, n.swap_swap⟩
      · simp only [mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hn ⊢
        exact ⟨hn.1.symm, hn.2.symm⟩
      · simp only [mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hn ⊢
        exact ⟨hn.1.symm, hn.2.symm⟩
    rw [hswap]
    exact card_filter_mul_eq_mul_le ha M (by rwa [add_comm])

/-- For one multiplier `a` with `2 a N ≤ p`, the pairs `(n₁, n₂) ∈ (M, M + N]²` with
`a n₁ ≡ a n₂ (mod p)` have `n₁ = n₂`, so there are at most `N` of them. -/
private theorem card_filter_mul_eq_mul_self_le {a : ℕ} (ha : 0 < a) (M : ℤ) {N : ℕ}
    (h : (a + a) * N ≤ p) :
    #{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a : ZMod p) * n.1 = a * n.2} ≤ N := by
  set S := {n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a : ZMod p) * n.1 = a * n.2}
  have hmaps : Set.MapsTo (fun n : ℤ × ℤ ↦ n.1) S (Ioc M (M + N)) := fun n hn ↦
    (mem_product.mp (mem_filter.mp hn).1).1
  have hinj : Set.InjOn (fun n : ℤ × ℤ ↦ n.1) S := by
    intro n hn n' hn' h1
    obtain ⟨hnI, hn⟩ := mem_filter.mp hn
    obtain ⟨hn'I, hn'⟩ := mem_filter.mp hn'
    have key := mul_sub_eq_mul_sub ha h hnI hn'I hn hn'
    simp only at h1
    rw [h1, sub_self, mul_zero, eq_comm, mul_eq_zero, sub_eq_zero] at key
    exact Prod.ext h1 (key.resolve_left (by exact_mod_cast ha.ne'))
  have := card_le_card_of_injOn _ hmaps hinj
  rwa [Int.card_Ioc, add_sub_cancel_left, Int.toNat_natCast] at this

/-- **The multiplicative energy count.** Let `𝒜` be a finite set of positive integers at most
`A`. If `2 A N ≤ p`, then the energy `V₂` of `𝒜` and `(M, M + N]` satisfies
`V₂ ≤ #𝒜 N + ∑_{a₁ ≠ a₂} (N gcd(a₁, a₂) / max(a₁, a₂) + 1)`. -/
theorem burgessEnergy_le [Fact p.Prime] (𝒜 : Finset ℕ) {A : ℕ}
    (h𝒜 : ∀ a ∈ 𝒜, 0 < a ∧ a ≤ A) (M : ℤ) (N : ℕ) (h : 2 * A * N ≤ p) :
    (burgessEnergy p 𝒜 (Ioc M (M + N)) : ℝ) ≤
      #𝒜 * N + ∑ a₁ ∈ 𝒜, ∑ a₂ ∈ 𝒜 with a₂ ≠ a₁, ((N * Nat.gcd a₁ a₂ / max a₁ a₂ : ℝ) + 1) := by
  classical
  have hpair {a₁ a₂ : ℕ} (ha₁ : a₁ ∈ 𝒜) (ha₂ : a₂ ∈ 𝒜) : (a₁ + a₂) * N ≤ p :=
    le_trans (Nat.mul_le_mul_right N (by have := (h𝒜 a₁ ha₁).2; have := (h𝒜 a₂ ha₂).2; omega)) h
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [burgessEnergy_def, burgessCount_def, add_zero, Ioc_self, product_empty,
      filter_empty, card_empty, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, CharP.cast_eq_zero,
      mul_zero, zero_mul, zero_div, zero_add]
    positivity
  -- Every multiplier is a unit modulo `p`, since `0 < a ≤ A < p`.
  have h𝒜p (a : ℕ) (ha : a ∈ 𝒜) : IsUnit (a : ZMod p) := by
    rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    refine Nat.not_dvd_of_pos_of_lt (h𝒜 a ha).1 ?_
    have := Nat.mul_le_mul_left (2 * A) hN
    nlinarith [(h𝒜 a ha).1, (h𝒜 a ha).2]
  rw [burgessEnergy_eq_sum_sum_card 𝒜 _ h𝒜p, Nat.cast_sum, ← nsmul_eq_mul, ← sum_const,
    ← sum_add_distrib]
  refine sum_le_sum fun a₁ ha₁ ↦ ?_
  rw [Nat.cast_sum, ← add_sum_erase _ _ ha₁, filter_ne']
  have hdiag := card_filter_mul_eq_mul_self_le (p := p) (h𝒜 a₁ ha₁).1 M (hpair ha₁ ha₁)
  refine add_le_add (by exact_mod_cast hdiag) (sum_le_sum fun a₂ ha₂ ↦ ?_)
  have ha₂' := mem_of_mem_erase ha₂
  exact card_filter_mul_eq_mul_le_max (lt_max_of_lt_right (h𝒜 a₂ ha₂').1) M (hpair ha₁ ha₂')

/-- The sum of `g(max(a₁, a₂))` over the ordered pairs of distinct elements of a finite set `𝒜`
in a linear order is twice the sum over `a ∈ 𝒜` of `g(a)` times the number of elements of `𝒜`
below `a`. -/
theorem sum_sum_filter_ne_max_eq {α β : Type*} [LinearOrder α] [CommSemiring β] (𝒜 : Finset α)
    (g : α → β) :
    ∑ a₁ ∈ 𝒜, ∑ a₂ ∈ 𝒜 with a₂ ≠ a₁, g (max a₁ a₂) = 2 * ∑ a ∈ 𝒜, #{b ∈ 𝒜 | b < a} * g a := by
  have hsplit (a₁ a₂ : α) : (if a₂ ≠ a₁ then g (max a₁ a₂) else 0) =
      (if a₂ < a₁ then g a₁ else 0) + (if a₁ < a₂ then g a₂ else 0) := by
    rcases lt_trichotomy a₂ a₁ with h | rfl | h
    · simp [h, h.ne, lt_asymm h, max_eq_left h.le]
    · simp
    · simp [h, h.ne', lt_asymm h, max_eq_right h.le]
  have hcount : ∑ a₁ ∈ 𝒜, ∑ a₂ ∈ 𝒜, (if a₂ < a₁ then g a₁ else 0) =
      ∑ a ∈ 𝒜, #{b ∈ 𝒜 | b < a} * g a := by
    simp only [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  have hcount' : ∑ a₁ ∈ 𝒜, ∑ a₂ ∈ 𝒜, (if a₁ < a₂ then g a₂ else 0) =
      ∑ a ∈ 𝒜, #{b ∈ 𝒜 | b < a} * g a := by
    rw [sum_comm]
    exact hcount
  simp only [sum_filter, hsplit, sum_add_distrib, hcount, hcount']
  ring

/-- **McGown's bound for prime multipliers.** Let `v(x)` be the number of pairs `(a, n)` of a
prime `a ≤ A` and `n ∈ (M, M + N]` with `n ≡ a x (mod p)`. If `2 A N ≤ p`, then
`∑_x v(x)² ≤ π(A) N + 2 N ∑_a (π(a) - 1) / a + 2 ∑_a (π(a) - 1)`, the sums over the primes
`a ≤ A`. -/
theorem burgessEnergy_primesLE_le [Fact p.Prime] {A : ℕ} (M : ℤ) (N : ℕ) (h : 2 * A * N ≤ p) :
    (burgessEnergy p A.primesLE (Ioc M (M + N)) : ℝ) ≤
      A.primeCounting * N + 2 * N * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) / a +
        2 * ∑ a ∈ A.primesLE, ((a.primeCounting : ℝ) - 1) := by
  refine (burgessEnergy_le _ (fun a ha ↦ ⟨(Nat.prime_of_mem_primesLE ha).pos,
    Nat.le_of_mem_primesLE ha⟩) M N h).trans_eq ?_
  -- Distinct primes are coprime, and `π(a) - 1` primes up to `A` are below a prime `a ≤ A`.
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
    Nat.primesLE_card_eq_primeCounting, sum_congr rfl fun a ha ↦ by rw [hbelow a ha], hsum]
  ring

end TauCeti
