/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Cast.Field
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Data.Int.CardIntervalMod

/-!
# Solutions of `a₁ n₂ - a₂ n₁ = c` and of `a₂ n₁ ≡ a₁ n₂ (mod p)` in a square

Let `a₁, a₂` be natural numbers and `I = (M, M + N]` an interval of `N` integers. For an integer
`c` and `g = gcd(a₁, a₂)`, the solutions `(n₁, n₂) ∈ I²` of `a₁ n₂ - a₂ n₁ = c` have their `n₂` in
one residue class modulo `a₂ / g`, and `n₂` determines `n₁` when `a₂ ≠ 0`. So there are at most
`N g / a₂ + 1` of them, and by symmetry at most `N g / max(a₁, a₂) + 1`.

If `(a₁ + a₂) N ≤ p`, two solutions of the congruence `a₂ n₁ ≡ a₁ n₂ (mod p)` in `I²` give the same
value of `a₁ n₂ - a₂ n₁`, because the difference of the two values is divisible by `p` and smaller
than `p` in absolute value. So the bound for one level `c` also bounds the solutions of the
congruence. This is the count of Treviño's Lemma 5 for the multiplicative energy in Burgess's
method. For `a₁ = a₂ = a` and `2 a N ≤ p` the solutions are exactly the `N` pairs `n₁ = n₂`.

## Main results

* `Int.card_filter_mul_sub_mul_eq_le`, `Int.card_filter_mul_sub_mul_eq_le_max`: at most
  `N gcd(a₁, a₂) / a₂ + 1`, and at most `N gcd(a₁, a₂) / max(a₁, a₂) + 1`, solutions of
  `a₁ n₂ - a₂ n₁ = c` in `I²`.
* `Int.mul_sub_eq_mul_sub_of_cast_mul_eq`: two solutions of the congruence in `I²` satisfy
  `a₂ (n₁ - n₁') = a₁ (n₂ - n₂')` in `ℤ` when `(a₁ + a₂) N ≤ p`.
* `Int.card_filter_mul_eq_mul_le_max`: at most `N gcd(a₁, a₂) / max(a₁, a₂) + 1` solutions of
  `a₂ n₁ ≡ a₁ n₂ (mod p)` in `I²` when `(a₁ + a₂) N ≤ p`.
* `Int.card_filter_mul_eq_mul_self`: exactly `N` solutions of `a n₁ ≡ a n₂ (mod p)` in `I²` when
  `0 < a` and `2 a N ≤ p`.

## References

* E. Treviño, *The Burgess inequality and the least k-th power non-residue*, Int. J. Number
  Theory 11 (2015), Lemma 5.
-/

public section

open Finset

namespace Int

/-- **Solutions at one level.** If `0 < a₂`, at most `N gcd(a₁, a₂) / a₂ + 1` pairs
`(n₁, n₂) ∈ (M, M + N]²` satisfy `a₁ n₂ - a₂ n₁ = c`: their `n₂` lie in one residue class modulo
`a₂ / gcd(a₁, a₂)` and determine `n₁`. -/
theorem card_filter_mul_sub_mul_eq_le {a₁ a₂ : ℕ} (ha₂ : 0 < a₂) (M : ℤ) (N : ℕ) (c : ℤ) :
    (#{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | a₁ * n.2 - a₂ * n.1 = c} : ℝ) ≤
      N * Nat.gcd a₁ a₂ / a₂ + 1 := by
  set S := {n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₁ : ℤ) * n.2 - a₂ * n.1 = c}
  rcases S.eq_empty_or_nonempty with hS | ⟨n₀, hn₀⟩
  · rw [hS, card_empty, Nat.cast_zero]
    positivity
  set g := Nat.gcd a₁ a₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ ha₂
  have hb : 0 < a₂ / g := Nat.div_pos (Nat.gcd_le_right _ ha₂) hg
  have hn₀c := (mem_filter.mp hn₀).2
  -- Every solution has `n₂ ≡ n₀₂ (mod a₂ / g)`.
  set T : Finset ℤ := {m ∈ Ico (M + 1) (M + N + 1) | m ≡ n₀.2 [ZMOD ((a₂ / g : ℕ) : ℤ)]}
  have hmaps : Set.MapsTo (fun n : ℤ × ℤ ↦ n.2) S T := by
    intro n hn
    obtain ⟨hnI, hnc⟩ := mem_filter.mp hn
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
          Nat.mul_div_cancel' (Nat.gcd_dvd_left a₁ a₂)]
        linear_combination hn₀c - hnc
      exact (Int.modEq_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left ⟨_, hdiv.symm⟩)).symm
  -- A solution is determined by its `n₂`.
  have hinj : Set.InjOn (fun n : ℤ × ℤ ↦ n.2) S := by
    intro n hn n' hn' h2
    have hc := (mem_filter.mp hn).2
    have hc' := (mem_filter.mp hn').2
    simp only at h2
    refine Prod.ext (mul_left_cancel₀ (by exact_mod_cast ha₂.ne' : (a₂ : ℤ) ≠ 0) ?_) h2
    linear_combination hc' - hc + (a₁ : ℤ) * h2
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

/-- The bound of `Int.card_filter_mul_sub_mul_eq_le` with `max(a₁, a₂)` in place of `a₂`. -/
theorem card_filter_mul_sub_mul_eq_le_max {a₁ a₂ : ℕ} (ha : 0 < max a₁ a₂) (M : ℤ) (N : ℕ)
    (c : ℤ) :
    (#{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | a₁ * n.2 - a₂ * n.1 = c} : ℝ) ≤
      N * Nat.gcd a₁ a₂ / max a₁ a₂ + 1 := by
  rcases le_total a₁ a₂ with h₁₂ | h₂₁
  · rw [max_eq_right h₁₂] at ha ⊢
    exact card_filter_mul_sub_mul_eq_le ha M N c
  · -- Swap the two coordinates to exchange the roles of `a₁` and `a₂`.
    rw [max_eq_left h₂₁] at ha ⊢
    rw [Nat.gcd_comm]
    have hswap : #{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₁ : ℤ) * n.2 - a₂ * n.1 = c} =
        #{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₂ : ℤ) * n.2 - a₁ * n.1 = -c} := by
      refine card_bij (fun n _ ↦ n.swap) (fun n hn ↦ ?_) (fun _ _ _ _ h ↦ Prod.swap_injective h)
        fun n hn ↦ ⟨n.swap, ?_, n.swap_swap⟩
      · simp only [mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hn ⊢
        exact ⟨hn.1.symm, by linarith [hn.2]⟩
      · simp only [mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hn ⊢
        exact ⟨hn.1.symm, by linarith [hn.2]⟩
    rw [hswap]
    exact card_filter_mul_sub_mul_eq_le ha M N (-c)

/-- Two pairs `(n₁, n₂)`, `(n₁', n₂')` in `(M, M + N]²` with `a₂ n₁ ≡ a₁ n₂` modulo `p` satisfy
`a₂ (n₁ - n₁') = a₁ (n₂ - n₂')` in `ℤ` when `(a₁ + a₂) N ≤ p`: the difference of the two sides is
divisible by `p` and at most `(a₁ + a₂) (N - 1) < p` in absolute value. -/
theorem mul_sub_eq_mul_sub_of_cast_mul_eq {p a₁ a₂ : ℕ} {M : ℤ} {N : ℕ}
    (h : (a₁ + a₂) * N ≤ p) {n n' : ℤ × ℤ} (hn : n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N))
    (hn' : n' ∈ Ioc M (M + N) ×ˢ Ioc M (M + N)) (h₁ : (a₂ : ZMod p) * n.1 = a₁ * n.2)
    (h₂ : (a₂ : ZMod p) * n'.1 = a₁ * n'.2) :
    (a₂ : ℤ) * (n.1 - n'.1) = a₁ * (n.2 - n'.2) := by
  simp only [mem_product, mem_Ioc] at hn hn'
  rcases Nat.eq_zero_or_pos (a₁ + a₂) with ha | ha
  · obtain ⟨rfl, rfl⟩ : a₁ = 0 ∧ a₂ = 0 := by omega
    simp
  rw [← sub_eq_zero]
  refine Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_) ?_
  · push_cast
    linear_combination h₁ - h₂
  · have hp : ((a₁ : ℤ) + a₂) * N ≤ p := by exact_mod_cast h
    have hd₁ : |n.1 - n'.1| ≤ N - 1 := abs_sub_le_iff.mpr ⟨by omega, by omega⟩
    have hd₂ : |n.2 - n'.2| ≤ N - 1 := abs_sub_le_iff.mpr ⟨by omega, by omega⟩
    have ha' : (1 : ℤ) ≤ a₁ + a₂ := by exact_mod_cast ha
    calc |(a₂ : ℤ) * (n.1 - n'.1) - a₁ * (n.2 - n'.2)|
        ≤ |(a₂ : ℤ) * (n.1 - n'.1)| + |(a₁ : ℤ) * (n.2 - n'.2)| := abs_sub _ _
      _ = a₂ * |n.1 - n'.1| + a₁ * |n.2 - n'.2| := by
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
      _ ≤ a₂ * (N - 1) + a₁ * (N - 1) := by gcongr
      _ < p := by nlinarith [hp, ha']

/-- **Treviño's count for one pair of multipliers.** If `0 < max(a₁, a₂)` and
`(a₁ + a₂) N ≤ p`, at most `N gcd(a₁, a₂) / max(a₁, a₂) + 1` pairs `(n₁, n₂) ∈ (M, M + N]²`
satisfy `a₂ n₁ ≡ a₁ n₂ (mod p)`: all of them have the same value of `a₁ n₂ - a₂ n₁`. -/
theorem card_filter_mul_eq_mul_le_max {p a₁ a₂ : ℕ} (ha : 0 < max a₁ a₂) (M : ℤ) {N : ℕ}
    (h : (a₁ + a₂) * N ≤ p) :
    (#{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₂ : ZMod p) * n.1 = a₁ * n.2} : ℝ) ≤
      N * Nat.gcd a₁ a₂ / max a₁ a₂ + 1 := by
  set S := {n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a₂ : ZMod p) * n.1 = a₁ * n.2}
  rcases S.eq_empty_or_nonempty with hS | ⟨n₀, hn₀⟩
  · rw [hS, card_empty, Nat.cast_zero]
    positivity
  obtain ⟨hn₀I, hn₀'⟩ := mem_filter.mp hn₀
  refine le_trans (Nat.cast_le.mpr (card_le_card fun n hn ↦ ?_))
    (card_filter_mul_sub_mul_eq_le_max ha M N (a₁ * n₀.2 - a₂ * n₀.1))
  obtain ⟨hnI, hn'⟩ := mem_filter.mp hn
  have key := mul_sub_eq_mul_sub_of_cast_mul_eq h hnI hn₀I hn' hn₀'
  exact mem_filter.mpr ⟨hnI, by linear_combination -key⟩

/-- For `0 < a` and `2 a N ≤ p`, the pairs `(n₁, n₂) ∈ (M, M + N]²` with `a n₁ ≡ a n₂ (mod p)`
are the `N` pairs with `n₁ = n₂`. -/
theorem card_filter_mul_eq_mul_self {p a : ℕ} (ha : 0 < a) (M : ℤ) {N : ℕ}
    (h : 2 * a * N ≤ p) :
    #{n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a : ZMod p) * n.1 = a * n.2} = N := by
  have h' : (a + a) * N ≤ p := by rwa [← two_mul]
  have hdiag : {n ∈ Ioc M (M + N) ×ˢ Ioc M (M + N) | (a : ZMod p) * n.1 = a * n.2} =
      (Ioc M (M + N)).diag := by
    ext ⟨n₁, n₂⟩
    simp only [mem_filter, mem_diag, mem_product]
    constructor
    · rintro ⟨⟨hn₁, hn₂⟩, hn⟩
      have key := mul_sub_eq_mul_sub_of_cast_mul_eq (n := (n₁, n₂)) (n' := (n₂, n₂)) h'
        (mem_product.2 ⟨hn₁, hn₂⟩) (mem_product.2 ⟨hn₂, hn₂⟩) hn rfl
      rw [sub_self, mul_zero, mul_eq_zero, sub_eq_zero] at key
      exact ⟨hn₁, key.resolve_left (by exact_mod_cast ha.ne')⟩
    · rintro ⟨hn₁, rfl⟩
      exact ⟨⟨hn₁, hn₁⟩, rfl⟩
  rw [hdiag, diag_card, Int.card_Ioc, add_sub_cancel_left, Int.toNat_natCast]

end Int
