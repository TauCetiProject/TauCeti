/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.CoefficientBounds
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Solver

/-!
# An explicit prime threshold for cyclotomic reconstruction

For an exact cyclotomic character-table certificate at the group exponent `e`, the coefficients
of the central entry on a class `C` are bounded by `|C| * Cyclotomic.rootCoeffBound e`.
Thus a Dixon prime larger than `2 * |G| * Cyclotomic.rootCoeffBound e` guarantees that the solver
reconstructs a certified table. The threshold is computable from the group order and exponent,
without inspecting the unknown character table.

The bound follows from the ordinary character's eigenvalues and the degree-free central bound
in `Representation.coeff_natAbs_le_of_finrank_mul_complexEmbedding_eq_natCast_mul_char`.
The existing solver's completeness theorem then applies to the balanced residue window.
This supplies a sufficient size bound; it does not assert that the smaller threshold
`2 * sqrt |G|` suffices for the power-basis coordinates.

## References

* J. D. Dixon, *High speed computation of group characters*, Numer. Math. **10** (1967),
  446--450.
-/

public section

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

namespace TauCeti.ClassData

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A prime exceeding the explicit group-order and root-coefficient threshold suffices to
reconstruct an exact cyclotomic character table, with no coefficient-bound hypothesis. -/
theorem isSome_dixonCyclotomicCharacterTable_of_rootCoeffBound (d : ClassData G)
    (e : ℕ) (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
    (degree : Fin d.numClasses → ℕ)
    (hspec : d.IsCyclotomicCharacterTableSpec e omega table degree)
    (hp : 2 * (Fintype.card G * Cyclotomic.rootCoeffBound e) < q.p) :
    (d.dixonCyclotomicCharacterTable? e he q).isSome = true := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  apply d.isSome_dixonCyclotomicCharacterTable_of_spec e he q omega table degree hspec
  intro i k j
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2
    ((hspec.central_coeff_natAbs_le i k (he ▸ Monoid.pow_exponent_eq_one (d.rep k)) j).trans
      (Nat.mul_le_mul_right _ (Finset.card_le_univ _)))) hp

end TauCeti.ClassData
