/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.OrderOf
import TauCeti.GroupTheory.OrderOfElement.SignedPowers

/-!
# Avoiding pairs of short signed powers

A set of exponents excluding short modular weighted means yields a set of residues whose ratios
from one point cannot be two distinct short signed powers of the same small prime. For an odd
prime, reduction modulo a power of two and squaring eliminate the signs. For the prime two,
reduction modulo a power of three suffices, since the generator reduces to one there.

The application to sparse sets is from `New.Parameters.exists_large_isSparse` in
`grh/src/New/Reduction/Data/Existence.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

namespace ZMod

/-- If `g` reduces to one modulo `3^(r+1)`, then two powers of `g` cannot differ
by a signed power `2^i` with `0 < i < 3^r`. -/
theorem not_exists_signed_two_pow_relation {m r i a b : ℕ} (hm : 3 ^ (r + 1) ∣ m)
    {g : ZMod m} (hg : castHom hm (ZMod (3 ^ (r + 1))) g = 1) (hi : 0 < i) (hir : i < 3 ^ r) :
    ¬ ∃ ε : ZMod m, ε ^ 2 = 1 ∧ g ^ b = ε * (2 : ZMod m) ^ i * g ^ a := by
  rintro ⟨ε, hε, hb⟩
  let f := castHom hm (ZMod (3 ^ (r + 1)))
  have hg' : f g = 1 := hg
  have hε' : (f ε) ^ 2 = 1 := by simpa using congrArg f hε
  have hb' : 1 = f ε * (2 : ZMod (3 ^ (r + 1))) ^ i := by
    simpa only [map_pow, map_mul, map_ofNat f 2, hg', one_pow, mul_one] using congrArg f hb
  have hpow : ((2 : ZMod (3 ^ (r + 1))) ^ 2) ^ i = 1 := by
    have h := congrArg (fun z => z ^ 2) hb'.symm
    simpa only [mul_pow, hε', one_mul, one_pow, pow_right_comm (2 : ZMod (3 ^ (r + 1))) i 2] using h
  have hnum : ((2 : ZMod (3 ^ (r + 1))) ^ 2) = 1 + 3 * (1 : ℤ) := by push_cast; ring
  have hord : orderOf ((2 : ZMod (3 ^ (r + 1))) ^ 2) = 3 ^ r := by
    rw [hnum]
    simpa using orderOf_one_add_mul_prime Nat.prime_three (by decide) 1 (by decide) r
  exact pow_ne_one_of_lt_orderOf hi.ne' (hord ▸ hir) hpow

/-- Let `g = 1 + 2^(v+2) * u` with `u` odd, and let the modulus `m` be divisible by
`2^(s+v+2)`. If `a, b, c` cannot give the indicated modular weighted mean unless `a = b`, then
`g^b` and `g^c` cannot be short signed powers of `p` times `g^a`. Here signs are any residues
with square one. -/
theorem not_exists_signed_pow_relations {m s v u p i j a b c : ℕ}
    (hu : Odd u) (hm : 2 ^ (s + (v + 2)) ∣ m) (hp : 1 < p) (hi : 0 < i) (hij : i ≤ j)
    (hsize : 2 * i * (p + 1) < 2 ^ s)
    (hmean : (2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) → a = b) :
    let g : ZMod m := 1 + 2 ^ (v + 2) * u
    ¬ ∃ ε ε' : ZMod m, ε ^ 2 = 1 ∧ ε' ^ 2 = 1 ∧
      g ^ b = ε * (p : ZMod m) ^ i * g ^ a ∧ g ^ c = ε' * (p : ZMod m) ^ j * g ^ a := by
  intro g ⟨ε, ε', hε, hε', hb, hc⟩
  let f := castHom hm (ZMod (2 ^ (s + (v + 2))))
  have hord : orderOf (f g) = 2 ^ s := by
    have hu' : ¬(2 : ℤ) ∣ (u : ℤ) := by exact_mod_cast hu.not_two_dvd_nat
    have he := orderOf_one_add_mul_prime_pow Nat.prime_two (v + 2) (by omega) _ hu' s
    simpa only [g, map_add, map_mul, map_pow, map_ofNat f 2, map_one, map_natCast,
      Int.cast_natCast, Nat.cast_ofNat] using he
  have hb' : (f g) ^ b = f ε * (p : ZMod (2 ^ (s + (v + 2)))) ^ i * (f g) ^ a := by
    simpa only [map_mul, map_pow, map_natCast] using congrArg f hb
  have hc' : (f g) ^ c = f ε' * (p : ZMod (2 ^ (s + (v + 2)))) ^ j * (f g) ^ a := by
    simpa only [map_mul, map_pow, map_natCast] using congrArg f hc
  have hε₂ : (f ε) ^ 2 = 1 := by simpa using congrArg f hε
  have hε₂' : (f ε') ^ 2 = 1 := by simpa using congrArg f hε'
  have hfin : IsOfFinOrder (f g) := orderOf_pos_iff.mp (hord ▸ pow_pos two_pos s)
  have he := hfin.add_mul_modEq_of_eq_mul_pow_mul hij hε₂ hε₂' hb' hc'
  rw [hord] at he
  rw [← hmean he] at hb'
  have hb'' : 1 = f ε * (p : ZMod (2 ^ (s + (v + 2)))) ^ i :=
    (hfin.isUnit.pow a).mul_right_cancel (by simpa using hb')
  have hpow : (p : ZMod (2 ^ (s + 1))) ^ (2 * i) = 1 := by
    have hpow' := congrArg (fun z => z ^ 2) hb''.symm
    simp only [mul_pow, hε₂, one_mul, one_pow, ← pow_mul'] at hpow'
    let f₂ := castHom (pow_dvd_pow 2 (by omega : s + 1 ≤ s + (v + 2))) (ZMod (2 ^ (s + 1)))
    simpa using congrArg f₂ hpow'
  exact (not_le_of_gt hsize) (two_pow_le_mul_succ_of_pow_eq_one hp (by omega) hpow)

end ZMod
