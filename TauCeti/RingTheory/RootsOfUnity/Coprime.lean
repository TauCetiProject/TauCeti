/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Power maps on roots of unity of coprime orders

For coprime `a` and `b`, every `ab`-th root of unity `z` of a commutative monoid is the product of
an `a`-th and a `b`-th root of unity, namely `z ^ s` and `z ^ t` for the Chinese-remainder
idempotents `s ≡ 1 [MOD a]`, `s ≡ 0 [MOD b]` and `t ≡ 0 [MOD a]`, `t ≡ 1 [MOD b]`. So an
endomorphism acting by `z ↦ z ^ c` on the `a`-th and on the `b`-th roots of unity acts by
`z ↦ z ^ c` on the `ab`-th roots of unity (`MonoidHom.map_eq_pow_of_coprime`). This is how the
action of a Galois automorphism on `μ_{ab}` is read off from its actions on `μ_a` and `μ_b`.
-/

public section

/-- An endomorphism of a commutative monoid acting by `z ↦ z ^ c` on the `a`-th and on the
`b`-th roots of unity, for coprime `a` and `b`, acts by `z ↦ z ^ c` on the `ab`-th roots of
unity. -/
theorem MonoidHom.map_eq_pow_of_coprime {M : Type*} [CommMonoid M] (φ : M →* M) {a b c : ℕ}
    (hab : a.Coprime b) (ha : ∀ z : M, z ^ a = 1 → φ z = z ^ c)
    (hb : ∀ z : M, z ^ b = 1 → φ z = z ^ c) {z : M} (hz : z ^ (a * b) = 1) : φ z = z ^ c := by
  obtain ⟨s, hsa, hsb⟩ := Nat.chineseRemainder hab 1 0
  obtain ⟨t, hta, htb⟩ := Nat.chineseRemainder hab 0 1
  have hst : (s + t) % (a * b) = 1 % (a * b) :=
    (Nat.modEq_and_modEq_iff_modEq_mul hab).1
      ⟨by simpa using hsa.add hta, by simpa using hsb.add htb⟩
  have hz' : z ^ s * z ^ t = z := by
    rw [← pow_add, pow_eq_pow_mod _ hz, hst, ← pow_eq_pow_mod _ hz, pow_one]
  obtain ⟨k, hk⟩ := Nat.modEq_zero_iff_dvd.1 hsb
  obtain ⟨l, hl⟩ := Nat.modEq_zero_iff_dvd.1 hta
  have hs : (z ^ s) ^ a = 1 := by
    rw [hk, ← pow_mul, mul_right_comm b k a, mul_comm b a, pow_mul, hz, one_pow]
  have ht : (z ^ t) ^ b = 1 := by
    rw [hl, ← pow_mul, mul_right_comm a l b, pow_mul, hz, one_pow]
  rw [← hz', map_mul, ha _ hs, hb _ ht, mul_pow]
