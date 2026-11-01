/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.CoefficientBounds
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Checker
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Prime

/-!
# An explicit prime threshold for cyclotomic reconstruction

For an exact cyclotomic character-table certificate at the group exponent `e`, the coefficients
of the central entry on a class `C` are bounded by `|C| * Cyclotomic.rootCoeffBound e`, hence by
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

/-- The bound `|G| * Cyclotomic.rootCoeffBound e` on every power-basis coefficient of every central
character value of `G`. It is computable from the group order and the exponent. -/
def centralCoefficientBound (G : Type*) [Fintype G] (e : ℕ) : ℕ :=
  Fintype.card G * Cyclotomic.rootCoeffBound e

/-- The defining product for the central coefficient bound. -/
theorem centralCoefficientBound_def (G : Type*) [Fintype G] (e : ℕ) :
    centralCoefficientBound G e = Fintype.card G * Cyclotomic.rootCoeffBound e := (rfl)

/-- For a nonzero conductor the central coefficient bound is at least the group order. -/
theorem card_le_centralCoefficientBound (G : Type*) [Fintype G] (e : ℕ) [NeZero e] :
    Fintype.card G ≤ centralCoefficientBound G e :=
  Nat.le_mul_of_pos_right _ Cyclotomic.one_le_rootCoeffBound

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
  refine ⟨hp, fun h ↦ ?_, he ▸ hdvd, by omega⟩
  have := Nat.le_of_dvd Nat.card_pos h
  omega

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

namespace TauCeti.ClassData.IsCyclotomicCharacterTableSpec

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {d : ClassData G} {e : ℕ} [NeZero e]
variable {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
variable {degree : Fin d.numClasses → ℕ}

/-- Each central-character coefficient is bounded by the class size times the largest
power-basis coefficient of an `e`-th root of unity, whenever the class representative
satisfies `d.rep k ^ e = 1`. -/
theorem central_coeff_natAbs_le
    (h : d.IsCyclotomicCharacterTableSpec e omega table degree)
    (i k : Fin d.numClasses) (hk : d.rep k ^ e = 1) (j : ℕ) :
    ((omega i k).coeff j).natAbs ≤ (d.classFinset k).card * Cyclotomic.rootCoeffBound e := by
  let row := finCongr d.numClasses_eq_card_conjClasses i
  obtain ⟨r, hr⟩ := h.isCharacterTableSpec.exists_eq_characterTable row
  have hdegC : (degree i : ℂ) = characterDegree ℂ r := by
    calc
      _ = d.complexTableOfCyclotomic e table row (ConjClasses.mk 1) := by
        rw [← d.classOf_index 1, d.complexTableOfCyclotomic_apply_classOf,
          h.table_index_one, map_natCast]
      _ = characterDegree ℂ r := (hr _).trans (characterTable_one r)
  have hdeg : degree i = characterDegree ℂ r := Nat.cast_injective hdegC
  have ht : Cyclotomic.complexEmbedding (table i k) =
      (irreducibleRepresentation ℂ r).character (d.rep k) := by
    rw [← d.complexTableOfCyclotomic_apply_classOf e table i k, hr, d.classOf_eq_mk,
      characterTable_apply, character_irreducibleRepresentation]
  apply Representation.coeff_natAbs_le_of_finrank_mul_complexEmbedding_eq_natCast_mul_char
    (irreducibleRepresentation ℂ r) hk
    (by simpa using characterDegree_pos ℂ r)
  have hc := congrArg Cyclotomic.complexEmbedding (h.degree_mul_central i k)
  simpa only [map_mul, map_natCast, ht, hdeg, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using hc

end TauCeti.ClassData.IsCyclotomicCharacterTableSpec
