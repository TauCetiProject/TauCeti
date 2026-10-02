/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.InvolutionCount
public import TauCeti.RepresentationTheory.CharacterTable.RealClasses

/-!
# Orthogonal and symplectic rows, and the unweighted sum of the Frobenius-Schur indicators

Over an algebraically closed field `k` of characteristic zero in which `|G|` is invertible, the
Frobenius-Schur indicator of a row of the character table takes only the values `1`, `0` and `-1`
(`TauCeti.frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one`), and the three values name
the **orthogonal**, the **complex** and the **symplectic** rows.  This file counts them.

The one computation behind everything is that an irreducible representation carries a
one-dimensional space of invariant bilinear forms when its character is inversion-invariant, and
none otherwise.  That is a comparison of two facts already in the library.  On one side the
invariant forms are as many as the invariants of the tensor square
(`TauCeti.Representation.finrank_invariantForms_eq_finrank_invariants_tprod_self_cast`), and
Mathlib's `Representation.card_inv_mul_sum_char_eq_finrank` counts those invariants as the average
`|G|⁻¹ ∑_g χ(g)²` of the squared character.  On the other side
`TauCeti.card_inv_mul_sum_irreducibleCharacter_sq` evaluates that very average, for a row of the
character table, as `1` or `0` according as inversion fixes the row.  So the dimension is the
invariance indicator, and the indicator of the row is nonzero exactly on the inversion-invariant
rows.

Three counts follow.  The orthogonal and the symplectic rows together are as many as the real
conjugacy classes, because the inversion-invariant rows already are
(`TauCeti.card_inversionInvariant_eq_card_realClasses`); the remaining, complex, rows make up the
rest of the table; and the **unweighted** sum `∑ᵢ ν₂(χᵢ)` is the difference
`#{orthogonal} - #{symplectic}`.  That unweighted sum is not the weighted one of
`TauCeti.card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree`, whose terms
carry the degrees `χᵢ(1)` and which counts the solutions of `g² = 1`; the two agree only when every
degree is `1`.

A group all of whose rows are orthogonal is **totally orthogonal**.  Two consequences are recorded
in that case: every conjugacy class is real, and the solutions of `g² = 1` are as many as the sum of
the degrees.

## Main results

* `Representation.card_inv_mul_sum_character_sq_eq_finrank_invariantForms`: **the average of the
  squared character counts the invariant bilinear forms**, the squared-character form of Mathlib's
  `Representation.card_inv_mul_sum_char_eq_finrank`.
* `TauCeti.finrank_invariantForms_irreducibleRepresentation`: **a row of the character table has a
  line of invariant forms when inversion fixes it, and none otherwise**.
* `TauCeti.frobeniusSchurIndicatorRow_eq_zero_iff` and
  `TauCeti.frobeniusSchurIndicatorRow_ne_zero_iff`: **the complex rows are exactly the rows that
  inversion does not fix**.
* `TauCeti.card_frobeniusSchurIndicatorRow_ne_zero_eq_card_realClasses`: the rows with nonzero
  indicator are as many as the real conjugacy classes.
* `TauCeti.card_orthogonalRow_add_card_symplecticRow_eq_card_realClasses`: **the orthogonal and the
  symplectic rows together are as many as the real conjugacy classes**, with
  `TauCeti.card_orthogonalRow_add_card_symplecticRow_eq_card_realValued` the same count against the
  conjugation-fixed rows over `ℂ`.
* `TauCeti.card_complexRow_add_card_realClasses_eq_card_conjClasses`: the complex rows fill up the
  rest of the table.
* `TauCeti.sum_frobeniusSchurIndicatorRow`: **the unweighted sum of the row indicators is
  `#{orthogonal} - #{symplectic}`**.
* `TauCeti.card_realClasses_eq_card_conjClasses_of_forall_frobeniusSchurIndicatorRow_eq_one` and
  `TauCeti.card_squareRoot_one_eq_sum_characterDegree_of_forall_frobeniusSchurIndicatorRow_eq_one`:
  for a totally orthogonal group every class is real, and `#{g : g² = 1} = ∑ᵢ χᵢ(1)`.

## Implementation notes

The counts are stated with `Nat.card` on subtypes of the row index type, matching
`TauCeti.card_inversionInvariant_eq_card_realClasses` and
`TauCeti.card_realValued_eq_card_realClasses`, against which they are compared; the decompositions
are performed by `subtypeOrEquiv` and `Equiv.sumCompl` rather than by `Finset.filter`, so no
decidability hypothesis reaches a statement.

`Representation.card_inv_mul_sum_character_sq_eq_finrank_invariantForms` takes an explicit
`Representation` argument and so is declared into the root `Representation` namespace, not into
`TauCeti.Representation`: `scripts/lint-dot-notation.py` reports a new finding for a declaration
named `TauCeti.<MathlibNamespace>.foo` whose first explicit argument has that Mathlib type, and the
pre-existing `TauCeti.Representation` names of
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Trichotomy.lean` are grandfathered in
`scripts/lint-dot-notation-baseline.txt` rather than permitted for new code.  Everything indexed by
a row of the character table is named in plain `TauCeti`, as in the sibling module
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/InvolutionCount.lean`.

The field is taken in `Type` rather than an arbitrary universe, matching
`TauCeti.frobeniusSchurIndicatorRow`.

## References

This proves the unweighted-count clause of Layer 7 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
flagged there twice: the involution-count bullet ends "This is distinct from the **unweighted**
count `∑_χ ν₂(χ) = #{orthogonal} − #{quaternionic}`; do not conflate the two", and the
"Real characters and real classes" bullet asks that "the real-valued characters split into
orthogonal (`ν₂ = +1`) and quaternionic (`ν₂ = -1`), and the unweighted difference `∑_χ ν₂(χ)`
counts orthogonal minus quaternionic irreducibles".

See I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4, and J.-P. Serre, *Linear
Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

open Module (finrank)

universe v w

namespace Representation

open TauCeti TauCeti.Representation

variable {k : Type} {G : Type v} {V : Type w} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Fintype G] [Invertible (Nat.card G : k)]

/-- **The average of the squared character counts the invariant bilinear forms**:
`|G|⁻¹ ∑_g χ(g)² = dim {invariant forms}`, as an identity in `k`.

This is Mathlib's `Representation.card_inv_mul_sum_char_eq_finrank` applied to the tensor square
`ρ ⊗ ρ`, whose character is `χ²`, together with
`TauCeti.Representation.finrank_invariantForms_eq_finrank_invariants_tprod_self_cast`, which
identifies the invariant forms of `ρ` with the invariants of that tensor square.  As with the
latter, in characteristic `p` this is an identity of residues only. -/
theorem card_inv_mul_sum_character_sq_eq_finrank_invariantForms (ρ : Representation k G V) :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g ^ 2 = finrank k (invariantForms ρ) := by
  rw [finrank_invariantForms_eq_finrank_invariants_tprod_self_cast ρ,
    ← Representation.card_inv_mul_sum_char_eq_finrank (ρ.tprod ρ)]
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  rw [Representation.char_tensor, Pi.mul_apply, sq]

end Representation

namespace TauCeti

section OneNeNegOne

variable (k : Type) [Field k] [CharZero k]

/-- In characteristic zero `1` and `-1` are distinct, which is what makes the orthogonal and the
symplectic rows disjoint families.  This is Mathlib's
`Ring.neg_one_ne_one_of_char_ne_two` with the characteristic read off `CharZero`. -/
private theorem one_ne_neg_one : (1 : k) ≠ -1 :=
  (Ring.neg_one_ne_one_of_char_ne_two (R := k)
    (by rw [ringChar.eq_zero]; exact two_ne_zero.symm)).symm

end OneNeNegOne

section Rows

variable (k : Type) (G : Type v) [Field k] [CharZero k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

variable {G} in
open scoped Classical in
/-- **A row of the character table has a line of invariant forms when inversion fixes it, and none
otherwise.**  A representation affording the row is irreducible, so by Schur's lemma it admits at
most one invariant bilinear form up to scalars; which of the two cases occurs is decided by the
average `|G|⁻¹ ∑_g χ(g)²`, computed on one side by
`TauCeti.Representation.card_inv_mul_sum_character_sq_eq_finrank_invariantForms` and on the other by
`TauCeti.card_inv_mul_sum_irreducibleCharacter_sq`. -/
theorem finrank_invariantForms_irreducibleRepresentation (i : Fin (Nat.card (ConjClasses G))) :
    finrank k (Representation.invariantForms (irreducibleRepresentation k i)) =
      if ∀ g : G, irreducibleCharacter k i g⁻¹ = irreducibleCharacter k i g then 1 else 0 := by
  have hcount := Representation.card_inv_mul_sum_character_sq_eq_finrank_invariantForms
    (irreducibleRepresentation k i)
  simp only [character_irreducibleRepresentation] at hcount
  have hvalue := card_inv_mul_sum_irreducibleCharacter_sq (k := k) i
  by_cases hfix : ∀ g : G, irreducibleCharacter k i g⁻¹ = irreducibleCharacter k i g
  · rw [ite_eq_left hfix]
    exact Nat.cast_eq_one.mp (by rw [← hcount, hvalue, ite_eq_left hfix])
  · rw [ite_eq_right hfix]
    exact Nat.cast_eq_zero.mp (by rw [← hcount, hvalue, ite_eq_right hfix])

variable {G} in
/-- **The complex rows are exactly the rows that inversion does not fix.**  The indicator of a row
vanishes precisely when the row carries no nonzero invariant bilinear form
(`TauCeti.Representation.frobeniusSchurIndicator_eq_zero_iff`), and by
`TauCeti.finrank_invariantForms_irreducibleRepresentation` that happens precisely when inverting the
class changes the row. -/
theorem frobeniusSchurIndicatorRow_eq_zero_iff (i : Fin (Nat.card (ConjClasses G))) :
    frobeniusSchurIndicatorRow k i = 0 ↔
      ¬ ∀ C : ConjClasses G, characterTable k G i C⁻¹ = characterTable k G i C := by
  classical
  have hbot : frobeniusSchurIndicatorRow k i = 0 ↔
      finrank k (Representation.invariantForms (irreducibleRepresentation k i)) = 0 := by
    rw [frobeniusSchurIndicatorRow_def, Representation.frobeniusSchurIndicator_eq_zero_iff]
    exact (Submodule.finrank_eq_zero (R := k)
      (M := LinearMap.BilinForm k (Fin (characterDegree k i) → k))
      (S := Representation.invariantForms (irreducibleRepresentation k i))).symm
  rw [hbot, finrank_invariantForms_irreducibleRepresentation, forall_characterTable_inv_iff]
  split_ifs with hfix
  · simp [hfix]
  · simp [hfix]

variable {G} in
/-- **The orthogonal and the symplectic rows are exactly the rows that inversion fixes**, the
contrapositive form of `TauCeti.frobeniusSchurIndicatorRow_eq_zero_iff`. -/
theorem frobeniusSchurIndicatorRow_ne_zero_iff (i : Fin (Nat.card (ConjClasses G))) :
    frobeniusSchurIndicatorRow k i ≠ 0 ↔
      ∀ C : ConjClasses G, characterTable k G i C⁻¹ = characterTable k G i C := by
  rw [ne_eq, frobeniusSchurIndicatorRow_eq_zero_iff, not_not]

end Rows

section Counting

variable (k : Type) (G : Type v) [Field k] [CharZero k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **The rows with nonzero Frobenius-Schur indicator are as many as the real conjugacy classes.**
This is `TauCeti.card_inversionInvariant_eq_card_realClasses` read through
`TauCeti.frobeniusSchurIndicatorRow_ne_zero_iff`. -/
theorem card_frobeniusSchurIndicatorRow_ne_zero_eq_card_realClasses :
    Nat.card {i : Fin (Nat.card (ConjClasses G)) // frobeniusSchurIndicatorRow k i ≠ 0} =
      Nat.card {C : ConjClasses G // IsRealClass C} := by
  rw [← card_inversionInvariant_eq_card_realClasses k G]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun i => frobeniusSchurIndicatorRow_ne_zero_iff k i)

/-- The orthogonal and the symplectic rows are disjoint families: in characteristic zero no row has
indicator both `1` and `-1`. -/
private theorem disjoint_frobeniusSchurIndicatorRow_eq_one_eq_neg_one :
    Disjoint (fun i : Fin (Nat.card (ConjClasses G)) => frobeniusSchurIndicatorRow k i = 1)
      (fun i => frobeniusSchurIndicatorRow k i = -1) :=
  Pi.disjoint_iff.mpr fun _ =>
    Prop.disjoint_iff.mpr fun h => one_ne_neg_one k (h.1 ▸ h.2)

/-- **The orthogonal and the symplectic rows of the character table together are as many as the real
conjugacy classes.**

The orthogonal rows are those with Frobenius-Schur indicator `1`, so by
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff` those carrying a nondegenerate invariant
symmetric form, and the symplectic rows are those with indicator `-1`, carrying a nondegenerate
invariant alternating one.  The two families are disjoint and exhaust the rows with nonzero
indicator, which `TauCeti.card_frobeniusSchurIndicatorRow_ne_zero_eq_card_realClasses` counts. -/
theorem card_orthogonalRow_add_card_symplecticRow_eq_card_realClasses :
    Nat.card {i : Fin (Nat.card (ConjClasses G)) // frobeniusSchurIndicatorRow k i = 1} +
        Nat.card {i : Fin (Nat.card (ConjClasses G)) // frobeniusSchurIndicatorRow k i = -1} =
      Nat.card {C : ConjClasses G // IsRealClass C} := by
  classical
  have hsplit : ∀ i : Fin (Nat.card (ConjClasses G)), frobeniusSchurIndicatorRow k i ≠ 0 ↔
      frobeniusSchurIndicatorRow k i = 1 ∨ frobeniusSchurIndicatorRow k i = -1 := by
    intro i
    rcases frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one k i with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  rw [← card_frobeniusSchurIndicatorRow_ne_zero_eq_card_realClasses k G,
    Nat.card_congr (Equiv.subtypeEquivRight hsplit),
    Nat.card_congr
      (subtypeOrEquiv _ _ (disjoint_frobeniusSchurIndicatorRow_eq_one_eq_neg_one k G)),
    Nat.card_sum]

/-- **The complex rows fill up the rest of the character table.**  A row is complex, that is has
Frobenius-Schur indicator `0`, exactly when inversion moves it, and the rows inversion fixes are as
many as the real conjugacy classes. -/
theorem card_complexRow_add_card_realClasses_eq_card_conjClasses :
    Nat.card {i : Fin (Nat.card (ConjClasses G)) // frobeniusSchurIndicatorRow k i = 0} +
        Nat.card {C : ConjClasses G // IsRealClass C} = Nat.card (ConjClasses G) := by
  classical
  rw [← card_frobeniusSchurIndicatorRow_ne_zero_eq_card_realClasses k G]
  simp only [ne_eq]
  rw [← Nat.card_sum,
    Nat.card_congr
      (Equiv.sumCompl fun i : Fin (Nat.card (ConjClasses G)) => frobeniusSchurIndicatorRow k i = 0)]
  simp

/-- **The unweighted sum of the Frobenius-Schur indicators of the rows counts the orthogonal rows
minus the symplectic ones.**

Each row contributes `1`, `0` or `-1`, so the sum is the difference of the two counts.  This is not
the weighted sum of
`TauCeti.card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree`, whose terms
carry the degrees `χᵢ(1)` and which counts the solutions of `g² = 1`. -/
theorem sum_frobeniusSchurIndicatorRow :
    ∑ i : Fin (Nat.card (ConjClasses G)), frobeniusSchurIndicatorRow k i =
      (Nat.card {i : Fin (Nat.card (ConjClasses G)) // frobeniusSchurIndicatorRow k i = 1} : k) -
        (Nat.card {i : Fin (Nat.card (ConjClasses G)) //
          frobeniusSchurIndicatorRow k i = -1} : k) := by
  classical
  have hone : (Nat.card {i : Fin (Nat.card (ConjClasses G)) //
      frobeniusSchurIndicatorRow k i = 1} : k) =
      ∑ i : Fin (Nat.card (ConjClasses G)),
        if frobeniusSchurIndicatorRow k i = 1 then (1 : k) else 0 := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hneg : (Nat.card {i : Fin (Nat.card (ConjClasses G)) //
      frobeniusSchurIndicatorRow k i = -1} : k) =
      ∑ i : Fin (Nat.card (ConjClasses G)),
        if frobeniusSchurIndicatorRow k i = -1 then (1 : k) else 0 := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hone, hneg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one k i with h | h | h
  · rw [h, ite_eq_left rfl, ite_eq_right (one_ne_neg_one k), sub_zero]
  · rw [h, ite_eq_right fun hz : (0 : k) = 1 => one_ne_zero hz.symm,
      ite_eq_right fun hz : (0 : k) = -1 => one_ne_zero (neg_eq_zero.mp hz.symm), sub_zero]
  · rw [h, ite_eq_right fun hz : (-1 : k) = 1 => one_ne_neg_one k hz.symm, ite_eq_left rfl,
      zero_sub]

end Counting

section TotallyOrthogonal

variable (k : Type) (G : Type v) [Field k] [CharZero k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **For a totally orthogonal group every conjugacy class is real.**  If every row of the character
table has indicator `1`, then every row is inversion-invariant, and the rows inversion fixes are as
many as the real classes. -/
theorem card_realClasses_eq_card_conjClasses_of_forall_frobeniusSchurIndicatorRow_eq_one
    (h : ∀ i : Fin (Nat.card (ConjClasses G)), frobeniusSchurIndicatorRow k i = 1) :
    Nat.card {C : ConjClasses G // IsRealClass C} = Nat.card (ConjClasses G) := by
  rw [← card_frobeniusSchurIndicatorRow_ne_zero_eq_card_realClasses k G,
    Nat.card_congr (Equiv.subtypeUnivEquiv fun i => (h i).trans_ne one_ne_zero)]
  simp

omit [CharZero k] in
/-- **For a totally orthogonal group the solutions of `g² = 1` are as many as the sum of the
degrees** of the irreducible characters.  This is the involution-counting formula
`TauCeti.card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree` with every
indicator equal to `1`. -/
theorem card_squareRoot_one_eq_sum_characterDegree_of_forall_frobeniusSchurIndicatorRow_eq_one
    (h : ∀ i : Fin (Nat.card (ConjClasses G)), frobeniusSchurIndicatorRow k i = 1) :
    (Nat.card {g : G // g * g = 1} : k) =
      ∑ i : Fin (Nat.card (ConjClasses G)), (characterDegree k i : k) := by
  rw [card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree k G]
  exact Finset.sum_congr rfl fun i _ => by rw [h i, one_mul]

end TotallyOrthogonal

section Complex

variable (G : Type v) [Group G] [Fintype G]

/-- **The real-valued irreducible complex characters split into the orthogonal and the symplectic
ones.**  Over `ℂ` a row of the character table is fixed by complex conjugation exactly when it is
fixed by inverting the class (`TauCeti.conj_characterTable`), so
`TauCeti.card_orthogonalRow_add_card_symplecticRow_eq_card_realClasses` and
`TauCeti.card_realValued_eq_card_realClasses` count the same family in two ways. -/
theorem card_orthogonalRow_add_card_symplecticRow_eq_card_realValued :
    Nat.card {i : Fin (Nat.card (ConjClasses G)) // frobeniusSchurIndicatorRow ℂ i = 1} +
        Nat.card {i : Fin (Nat.card (ConjClasses G)) // frobeniusSchurIndicatorRow ℂ i = -1} =
      Nat.card {i : Fin (Nat.card (ConjClasses G)) // ∀ C : ConjClasses G,
        (starRingEnd ℂ) (characterTable ℂ G i C) = characterTable ℂ G i C} := by
  rw [card_orthogonalRow_add_card_symplecticRow_eq_card_realClasses ℂ G]
  exact (card_realValued_eq_card_realClasses G).symm

end Complex

end TauCeti
