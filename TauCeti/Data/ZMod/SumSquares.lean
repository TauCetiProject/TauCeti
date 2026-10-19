/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Data.ZMod.LocalRing

import TauCeti.RingTheory.Henselian.BinaryForm
import TauCeti.RingTheory.Henselian.Basic
import Mathlib.RingTheory.Artinian.Module
-- Supplies completeness of Artinian local rings, needed by the Henselian instance.
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Sums of two squares modulo odd prime powers

Every unit modulo a power of an odd prime is a sum of two squares. The finite
prime-power ring is local and Henselian, so the existing binary-form universality
theorem applies with both coefficients equal to one. The exponent-zero case is
the trivial ring.

## Main declarations

* `ZMod.exists_sq_add_sq_eq_of_isUnit_prime_pow`: the unit sum-of-squares representation.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(a), for the doubled odd cyclic relation that this arithmetic supplies.
-/

public section

namespace ZMod

/-- Every unit modulo a power of an odd prime is a sum of two squares. -/
theorem exists_sq_add_sq_eq_of_isUnit_prime_pow (p k : ℕ) [Fact p.Prime]
    (hp : Odd p) {r : ZMod (p ^ k)} (hr : IsUnit r) :
    ∃ a b : ZMod (p ^ k), a ^ 2 + b ^ 2 = r := by
  by_cases hk : k = 0
  · subst k
    have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  · have hkpos := Nat.pos_of_ne_zero hk
    let : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    let : IsLocalRing (ZMod (p ^ k)) := isLocalRing_prime_pow p k hkpos
    let : IsArtinianRing (ZMod (p ^ k)) := isArtinian_of_finite
    let : Finite (IsLocalRing.ResidueField (ZMod (p ^ k))) :=
      Finite.of_surjective (IsLocalRing.residue _) IsLocalRing.residue_surjective
    have htwo : IsUnit (2 : ZMod (p ^ k)) :=
      (ZMod.isUnit_iff_coprime (2 : ℕ) (p ^ k)).mpr
        ((Nat.coprime_two_left.mpr hp).pow_right k)
    obtain ⟨a, b, hab⟩ := TauCeti.exists_mul_sq_add_mul_sq_eq_of_isUnit
      htwo (a := 1) (b := 1) isUnit_one isUnit_one hr
    exact ⟨a, b, by simpa only [one_mul] using hab⟩

end ZMod
