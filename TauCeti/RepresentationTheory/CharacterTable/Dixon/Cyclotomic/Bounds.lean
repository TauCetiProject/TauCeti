/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Prime

/-!
# An explicit prime threshold for cyclotomic reconstruction

The exact central character values at the group exponent `e` have coefficients bounded by
`TauCeti.centralCoefficientBound G e`, which is `|G| * Cyclotomic.rootCoeffBound e`. The threshold
is computable from the group order and exponent, without inspecting the unknown character table.

A prime congruent to `1` modulo the exponent and larger than twice this bound, called a strong
Dixon prime, is a good Dixon prime, and such primes exist. Dixon's smaller threshold
`2 * sqrt |G|` does not bound the power-basis coordinates of central characters.

## References

* J. D. Dixon, *High speed computation of group characters*, Numer. Math. **10** (1967),
  446--450.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [Fintype G]

/-- A prime congruent to `1` modulo the exponent and beyond twice the central coefficient bound is
a good Dixon prime: it exceeds both the group order and Dixon's threshold `2 * sqrt |G|`. -/
theorem IsGoodDixonPrime.of_two_mul_centralCoefficientBound_lt {e p : ℕ}
    (he : e = Monoid.exponent G) (hp : p.Prime) (hdvd : e ∣ p - 1)
    (hlt : 2 * centralCoefficientBound G e < p) : IsGoodDixonPrime G p := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card G ≤ centralCoefficientBound G e := by
    rw [Nat.card_eq_fintype_card]
    exact card_le_centralCoefficientBound G e
  have hsqrt := Nat.sqrt_le_self (Nat.card G)
  exact .of_lt hp (he ▸ hdvd) (by omega)

/-- **Strong Dixon primes exist.** There is Dixon prime data whose prime exceeds twice the central
coefficient bound, since there are arbitrarily large primes congruent to `1` modulo the
exponent. -/
theorem exists_strongDixonPrime {e : ℕ} (he : e = Monoid.exponent G) :
    ∃ q : DixonPrimeData G, 2 * centralCoefficientBound G e < q.p := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨p, hprime, hlt, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := e)
    (2 * centralCoefficientBound G e) (NeZero.ne e)
  have hgood : IsGoodDixonPrime G p := .of_two_mul_centralCoefficientBound_lt he hprime
    ((Nat.modEq_iff_dvd' hprime.one_lt.le).mp hmod.symm) hlt
  obtain ⟨root, hroot⟩ := hgood.exists_isPrimitiveRoot
  exact ⟨⟨p, root, hgood, hroot⟩, hlt⟩

end TauCeti
