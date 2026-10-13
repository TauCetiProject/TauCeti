/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Unramifiedness and separability at one prime

An essentially finite type algebra is unramified at a prime exactly when its ramification index
is one and its residue field extension is separable. The separability condition concerns only
the selected prime, rather than every prime above its contraction. This distinction matters
over imperfect residue fields, where ramification index one alone does not imply unramifiedness.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Unramifiedness at a prime is ramification index one together with separability of the
selected residue extension. No separability assumption is imposed at other primes. -/
theorem isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_residueField
    (q : Ideal S) [q.IsPrime] [Algebra.EssFiniteType R S] :
    Algebra.IsUnramifiedAt R q ↔ q.ramificationIdx R = 1 ∧
      let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := by
  -- The length reduction follows Mathlib's Ideal.ramificationIdx_eq_one_iff, combined with
  -- the local criterion Algebra.isUnramifiedAt_iff_map_eq.
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have he : q.ramificationIdx R = 1 ↔
      (q.under R).map (algebraMap R (Localization.AtPrime q)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff]
  rw [Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q, he, and_comm]

end Ideal
