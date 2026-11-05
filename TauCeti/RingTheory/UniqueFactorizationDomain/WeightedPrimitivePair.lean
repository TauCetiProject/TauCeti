/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

import Mathlib.Algebra.Group.Commute.Units

/-!
# Extracting weighted powers from a pair of elements

Call a pair `(a, b)` in a commutative monoid with zero *primitive of weight `(m, n)`* if every
`ℓ` with both `ℓ ^ m ∣ a` and `ℓ ^ n ∣ b` is a unit. When divisibility is well-founded
(`WfDvdMonoid`) and the weights are positive, every pair not both zero is `(d ^ m * a', d ^ n * b')`
for a nonzero `d` and a pair `(a', b')` primitive of weight `(m, n)`: stripping one non-unit
at a time strictly decreases the pair in the lexicographic order of strict divisibility.

For weight `(1, 1)` the conclusion amounts to `IsRelPrime a' b'`, the extraction of a greatest
common divisor as in `Int.exists_gcd_one`. For `ℤ` and weight `(4, 6)` it produces the
minimal-pair short Weierstrass equation `y² = x³ + Ax + B` of an elliptic curve over `ℚ`, where
`(A, B) ↦ (u⁴A, u⁶B)` is the coefficient freedom of a short equation.

## Main results

* `TauCeti.exists_eq_pow_mul_and_forall_isUnit_of_pow_dvd`: the statement above.
-/

public section

namespace TauCeti

variable {α : Type*} [CommMonoidWithZero α] [WfDvdMonoid α]

/-- **Every pair not both zero is a weighted power times a primitive pair**: in a monoid with
well-founded divisibility, for positive weights `m` and `n` there are `d ≠ 0` and `a'`, `b'` with
`a = d ^ m * a'`, `b = d ^ n * b'`, and every `ℓ` with both `ℓ ^ m ∣ a'` and `ℓ ^ n ∣ b'` a
unit. -/
theorem exists_eq_pow_mul_and_forall_isUnit_of_pow_dvd {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {a b : α} (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ d a' b' : α, d ≠ 0 ∧ a = d ^ m * a' ∧ b = d ^ n * b' ∧
      ∀ ℓ, ℓ ^ m ∣ a' → ℓ ^ n ∣ b' → IsUnit ℓ := by
  -- Well-founded induction on `(a, b)` in the lexicographic order of strict divisibility,
  -- stripping one non-unit `ℓ` with `ℓ ^ m ∣ a` and `ℓ ^ n ∣ b` at a time.
  suffices ∃ d a' b' : α, a = d ^ m * a' ∧ b = d ^ n * b' ∧
      ∀ ℓ, ℓ ^ m ∣ a' → ℓ ^ n ∣ b' → IsUnit ℓ by
    obtain ⟨d, a', b', ha, hb, hmin⟩ := this
    refine ⟨d, a', b', ?_, ha, hb, hmin⟩
    rintro rfl
    simp [ha, hb, zero_pow hm, zero_pow hn] at h
  obtain ⟨p, hp⟩ : ∃ p : α × α, p = (a, b) := ⟨_, rfl⟩
  induction p using (wellFounded_dvdNotUnit (α := α)).prod_lex (wellFounded_dvdNotUnit (α := α))
    |>.induction generalizing a b with
  | _ p ih =>
  subst hp
  by_cases hmin : ∀ ℓ, ℓ ^ m ∣ a → ℓ ^ n ∣ b → IsUnit ℓ
  · exact ⟨1, a, b, by simp, by simp, hmin⟩
  push Not at hmin
  obtain ⟨ℓ, ⟨a₁, rfl⟩, ⟨b₁, rfl⟩, hℓ⟩ := hmin
  have hne : a₁ ≠ 0 ∨ b₁ ≠ 0 := h.imp right_ne_zero_of_mul right_ne_zero_of_mul
  have hlt : Prod.Lex DvdNotUnit DvdNotUnit (a₁, b₁) (ℓ ^ m * a₁, ℓ ^ n * b₁) := by
    rw [Prod.lex_def]
    by_cases ha₁ : a₁ = 0
    · exact .inr ⟨by simp [ha₁], hne.resolve_left (not_not.mpr ha₁), ℓ ^ n,
        mt (isUnit_pow_iff hn).mp hℓ, mul_comm _ _⟩
    · exact .inl ⟨ha₁, ℓ ^ m, mt (isUnit_pow_iff hm).mp hℓ, mul_comm _ _⟩
  obtain ⟨d, a', b', ha', hb', hmin'⟩ := ih _ hlt hne rfl
  exact ⟨ℓ * d, a', b', by rw [ha', mul_pow, mul_assoc], by rw [hb', mul_pow, mul_assoc], hmin'⟩

end TauCeti

end
