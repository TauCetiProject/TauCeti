/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Local rings modulo prime powers

For a positive power of a prime, a residue is a unit exactly when its reduction
modulo the prime is nonzero. Mathlib's instance in `Mathlib.RingTheory.ZMod.LocalRing` makes the
prime-power ring local; in that local ring, equality in the residue field is equality after
reduction modulo the prime. The statements include the prime two and exclude the exponent-zero
trivial ring.

## Main declarations

* `ZMod.isUnit_prime_pow_iff_castHom_ne_zero`: the unit criterion under reduction.
* `ZMod.residue_eq_residue_iff_castHom_eq`: equality in the residue field is equality after
  reduction modulo the prime.
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

/-- For a positive prime power, two residues have the same image in the local-ring residue field
exactly when their reductions modulo the prime are equal. -/
theorem residue_eq_residue_iff_castHom_eq (p k : ℕ) [Fact p.Prime]
    [IsLocalRing (ZMod (p ^ k))] (hk : 0 < k) (x y : ZMod (p ^ k)) :
    IsLocalRing.residue _ x = IsLocalRing.residue _ y ↔
      castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x =
        castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) y := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_prime_pow_iff_castHom_ne_zero p k hk, not_not, map_sub, sub_eq_zero]

end ZMod
