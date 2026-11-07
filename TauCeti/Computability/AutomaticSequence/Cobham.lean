/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence.PrefixColors
import TauCeti.Combinatorics.Pigeonhole.RepeatedRepresentatives
import TauCeti.Computability.AutomaticSequence.LocalPeriod
import TauCeti.Data.Nat.Periodic.RadixWindows
import TauCeti.NumberTheory.ExponentialEquation.ClosePowers
import Mathlib.Data.Nat.Prime.Basic

/-!
# Cobham's theorem

A sequence automatic in two multiplicatively independent bases is eventually periodic.
Conversely, an eventually periodic sequence is automatic in every nonzero base. Thus
simultaneous automaticity in two independent bases characterizes eventual periodicity.
The output alphabet is arbitrary, and a finite exceptional prefix is allowed.

Multiplicative independence is stated explicitly as inequality of all positive powers.
Unequal bases alone do not suffice, as the pair `2, 4` shows. The proof combines finite
prefix colours, uniformly repeated representatives, relatively close powers, and gluing
of the resulting local periods along overlapping radix windows.

## References

* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018),
  arXiv:1801.06704, Theorem 1 and its proof in §3.
-/

public section

namespace TauCeti

variable {a b : ℕ} [NeZero a] [NeZero b] {Δ : Type*} {f : ℕ → Δ}

/-- **Cobham's theorem, forward direction.** A sequence automatic in two multiplicatively
independent bases at least two has a positive period after a finite exceptional prefix. -/
theorem IsAutomatic.exists_periodic_tail (hf : IsAutomatic a f) (hg : IsAutomatic b f)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → a ^ m ≠ b ^ n) :
    ∃ N p : ℕ, 0 < p ∧ ∀ t, N ≤ t → f (t + p) = f t := by
  obtain ⟨_, _, A, hA⟩ := hf.exists_prefix_coloring ha
  obtain ⟨_, _, B, hB⟩ := hg.exists_prefix_coloring hb
  obtain ⟨N, ξ, _, hrep⟩ := exists_uniform_repeated_representatives A B
  obtain ⟨m, n, hm, hn, hclose⟩ := Nat.exists_pos_mul_abs_pow_sub_pow_le a b (6 * ξ) ha hb
  have hclose' : 6 * (ξ : ℤ) * |((a ^ m : ℕ) : ℤ) - (b ^ n : ℕ)| ≤ (b ^ n : ℕ) := by
    simpa using hclose
  have hlocal : ∀ x, N ≤ x → ∃ p, 0 < p ∧ 6 * p ≤ b ^ n ∧
      ∀ t, 3 * (x * b ^ n) + b ^ n ≤ 3 * t →
        3 * (t + p) ≤ 3 * (x * b ^ n) + 5 * b ^ n → f (t + p) = f t := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv, hux, hvx, huvA⟩ := hrep x hx
    exact ⟨_, natAbs_sub_mul_sub_period_on_radix_window hu hv huv (hind m n hm hn) hclose'
      rfl (hB x u hux.symm n hn) (hB x v hvx.symm n hn) (hA u v huvA m hm)⟩
  obtain ⟨p, hp, _, htail⟩ := Nat.exists_periodic_tail_of_period_on_radix_windows hlocal
  exact ⟨(N + 1) * b ^ n, p, hp, htail⟩

/-- **Cobham's base-independence theorem.** For two multiplicatively independent bases at
least two, simultaneous automaticity is equivalent to eventual periodicity. -/
theorem isAutomatic_and_isAutomatic_iff_eventually_periodic (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → a ^ m ≠ b ^ n) :
    IsAutomatic a f ∧ IsAutomatic b f ↔
      ∃ N p : ℕ, 0 < p ∧ ∀ t, N ≤ t → f (t + p) = f t := by
  constructor
  · rintro ⟨hf, hg⟩
    exact hf.exists_periodic_tail hg ha hb hind
  · rintro ⟨N, p, hp, h⟩
    exact ⟨isAutomatic_of_eventually_periodic hp h, isAutomatic_of_eventually_periodic hp h⟩

-- Unequal bases are not enough for the hypothesis.
example : (2 : ℕ) ≠ 4 ∧ ¬ (∀ m n : ℕ, 0 < m → 0 < n → 2 ^ m ≠ 4 ^ n) := by
  constructor
  · decide
  · intro h
    exact h 2 1 (by decide) (by decide) (by decide)

-- The bases two and three meet the independence hypothesis.
example (hf : IsAutomatic 2 f) (hg : IsAutomatic 3 f) :
    ∃ N p : ℕ, 0 < p ∧ ∀ t, N ≤ t → f (t + p) = f t := by
  apply hf.exists_periodic_tail hg (by decide) (by decide)
  intro m n hm _ heq
  have hdiv : 2 ∣ 3 ^ n := heq ▸ dvd_pow_self 2 hm.ne'
  have := _root_.Nat.prime_two.dvd_of_dvd_pow hdiv
  norm_num at this

-- A finite exceptional prefix, rather than periodicity from zero, is allowed.
example : IsAutomatic 2 (fun n ↦ if n = 0 then 7 else n % 2) ∧
    IsAutomatic 3 (fun n ↦ if n = 0 then 7 else n % 2) := by
  have h : ∀ t : ℕ, 1 ≤ t →
      (if t + 2 = 0 then 7 else (t + 2) % 2) = (if t = 0 then 7 else t % 2) := by
    intro t ht
    simp [show t ≠ 0 by omega]
  exact ⟨isAutomatic_of_eventually_periodic (by decide : 0 < 2) h,
    isAutomatic_of_eventually_periodic (by decide : 0 < 2) h⟩

end TauCeti
