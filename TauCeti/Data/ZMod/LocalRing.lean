/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Local rings modulo prime powers

For a positive power of a prime, a residue is a unit exactly when its reduction
modulo the prime is nonzero. This criterion makes the prime-power ring local.
The statements include the prime two and exclude the exponent-zero trivial ring.

## Main declarations

* `ZMod.isUnit_prime_pow_iff_castHom_ne_zero`: the unit criterion under reduction.
* `ZMod.isLocalRing_prime_pow`: every positive prime-power residue ring is local.
-/

public section

namespace ZMod

/-- A residue modulo a positive prime power is a unit exactly when its reduction
modulo the prime is nonzero. -/
@[simp]
theorem isUnit_prime_pow_iff_castHom_ne_zero (p k : ℕ) [Fact p.Prime] (hk : 0 < k)
    (x : ZMod (p ^ k)) :
    IsUnit x ↔ ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x ≠ 0 := by
  have h := ZMod.isUnit_natCast_iff_not_dvd_pow (a := x.val) (Fact.out : p.Prime) hk
  rw [ZMod.natCast_zmod_val] at h
  rw [h]
  have hx : ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x =
      (x.val : ZMod p) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hx, Ne, ZMod.natCast_eq_zero_iff]

/-- The residue ring modulo a positive power of a prime is a local ring. -/
theorem isLocalRing_prime_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    IsLocalRing (ZMod (p ^ k)) := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow hk.ne' (Fact.out : p.Prime).one_lt⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  rw [isUnit_prime_pow_iff_castHom_ne_zero p k hk,
    isUnit_prime_pow_iff_castHom_ne_zero p k hk, map_sub, map_one]
  by_cases h : ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x = 0
  · right
    simp [h]
  · exact Or.inl h

end ZMod
