/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Perfect
import TauCeti.FieldTheory.Finite.QuadraticNorm

/-!
# Perfectness, projective special unitary model, and simplicity of `²A_r(q)`

For a valid graph-twisted type-`A` index `²A_r(q)` (`2 ≤ r`, with `3 ≤ q` when `r = 2`),
`TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints` identifies the Steinberg fixed points with
`SU_{r+1}(q) = fixedSubgroup ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius r)`. Combining
trace surjectivity and the `|𝔽_q| ≥ 3` witness over `𝔽_{q²}` with
`TauCeti.commutator_specialIsometryGroup_typeAGraphConjugator_eq_top` and
`TauCeti.isSimpleGroup_quotient_center_typeAGraphConjugator` proves that `SU_{r+1}(q)` is perfect
and that the candidate group of `²A_r(q)` is isomorphic to `PSU_{r+1}(q)` and simple.

## Main definitions and results

* `TauCeti.ValidLieTypeIndex.commutator_galoisFieldTwistedFrobenius_eq_top` and
  `TauCeti.ValidLieTypeIndex.isSimpleGroup_quotient_center_galoisFieldTwistedFrobenius`:
  perfectness of `SU_{r+1}(q)` and simplicity of `PSU_{r+1}(q)` for `2 ≤ r` and `r = 2 → 3 ≤ q`.
* `TauCeti.TypeALieIndex.commutator_specialUnitary_eq_top` and
  `TauCeti.TypeALieIndex.projectiveSpecialUnitaryEquivGroup`: `SU_{r+1}(q)` is perfect and the
  candidate group of `²A_r(q)` is `PSU_{r+1}(q)`.
* `TauCeti.TypeALieIndex.isSimpleGroup_group_ofTwistedA` and
  `TauCeti.ValidLieTypeIndex.isSimpleGroup_twistedA`: every `²A_r(q)` on the classification list is
  simple.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), §§11.3, 13.1, and 14.1.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 10.
-/

public section

noncomputable section

namespace TauCeti.ValidLieTypeIndex

section FiniteUnitary

variable (d : ValidLieTypeIndex)

private theorem natCard_extensionGaloisField_two_eq_fieldOrder_sq :
    Nat.card (GaloisField d.characteristic (d.fieldExponent * 2)) = d.fieldOrder ^ 2 := by
  rw [d.natCard_galoisField, ← d.fieldOrder_eq_characteristic_pow]

private theorem rank_ne_two_or_exists_iterateFrobenius_fixed {r : ℕ}
    (hq : r = 2 → 3 ≤ d.fieldOrder) :
    r ≠ 2 ∨ ∃ t : GaloisField d.characteristic (d.fieldExponent * 2),
      iterateFrobenius _ d.characteristic d.fieldExponent t = t ∧ t ≠ 0 ∧ t ≠ 1 := by
  by_cases hr2 : r = 2
  · obtain ⟨t, ht, ht0, ht1⟩ := FiniteField.exists_pow_eq_self_and_ne_zero_and_ne_one (hq hr2)
      d.natCard_extensionGaloisField_two_eq_fieldOrder_sq
    exact .inr ⟨t, by simpa [coe_iterateFrobenius_galoisField] using ht, ht0, ht1⟩
  · exact .inl hr2

/-- **Perfectness of `SU_{r+1}(q)`** in its graph-twisted Frobenius model, for `2 ≤ r` and
`r = 2 → 3 ≤ q` (excluding `SU₃(2)`). -/
theorem commutator_galoisFieldTwistedFrobenius_eq_top {r : ℕ} (hr : 2 ≤ r)
    (hq : r = 2 → 3 ≤ d.fieldOrder) :
    commutator (fixedSubgroup (d.galoisFieldTwistedFrobenius r)) = ⊤ := by
  rw [d.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup]
  exact commutator_specialIsometryGroup_typeAGraphConjugator_eq_top
    d.involutive_iterateFrobenius_galoisField
    (fun s hs ↦ by
      simpa using d.exists_add_neg_one_pow_mul_iterateFrobenius_eq (r := 0) (s := s)
        (by simpa using hs))
    (d.exists_ne_zero_add_neg_one_pow_mul_iterateFrobenius_eq_zero (r := r)) hr
    (d.rank_ne_two_or_exists_iterateFrobenius_fixed hq)

/-- **Simplicity of `PSU_{r+1}(q)`** in its graph-twisted Frobenius model, for `2 ≤ r` and
`r = 2 → 3 ≤ q`. -/
theorem isSimpleGroup_quotient_center_galoisFieldTwistedFrobenius {r : ℕ} (hr : 2 ≤ r)
    (hq : r = 2 → 3 ≤ d.fieldOrder) :
    IsSimpleGroup (fixedSubgroup (d.galoisFieldTwistedFrobenius r) ⧸
      Subgroup.center (fixedSubgroup (d.galoisFieldTwistedFrobenius r))) := by
  rw [d.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup]
  exact isSimpleGroup_quotient_center_typeAGraphConjugator
    d.involutive_iterateFrobenius_galoisField
    (fun s hs ↦ by
      simpa using d.exists_add_neg_one_pow_mul_iterateFrobenius_eq (r := 0) (s := s)
        (by simpa using hs))
    (d.exists_ne_zero_add_neg_one_pow_mul_iterateFrobenius_eq_zero (r := r)) hr
    (d.rank_ne_two_or_exists_iterateFrobenius_fixed hq)

end FiniteUnitary

end TauCeti.ValidLieTypeIndex

namespace TauCeti.TypeALieIndex

private theorem two_le_and_three_le_fieldOrder_of_valid {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    2 ≤ (ofTwistedA r q hv).val.rank ∧
      ((ofTwistedA r q hv).val.rank = 2 → 3 ≤ (ofTwistedA r q hv).val.fieldOrder) := by
  simpa [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType, ValidLieTypeIndex.fieldOrder] using
    (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1

/-- **The finite special unitary group of `²A_r(q)` is perfect.** -/
theorem commutator_specialUnitary_eq_top (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    commutator (fixedSubgroup
      ((ofTwistedA r q hv).val.galoisFieldTwistedFrobenius (ofTwistedA r q hv).val.rank)) = ⊤ := by
  obtain ⟨hr, hq⟩ := two_le_and_three_le_fieldOrder_of_valid hv
  exact (ofTwistedA r q hv).val.commutator_galoisFieldTwistedFrobenius_eq_top hr hq

/-- **The group attached to `²A_r(q)` is the projective special unitary group `PSU_{r+1}(q)`.** -/
def projectiveSpecialUnitaryEquivGroup (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    fixedSubgroup
        ((ofTwistedA r q hv).val.galoisFieldTwistedFrobenius (ofTwistedA r q hv).val.rank) ⧸
      Subgroup.center (fixedSubgroup
        ((ofTwistedA r q hv).val.galoisFieldTwistedFrobenius (ofTwistedA r q hv).val.rank)) ≃*
      (ofTwistedA r q hv).Group :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect (commutator_specialUnitary_eq_top r q hv)
    (specialUnitaryEquivFixedPoints r q hv)

/-- `projectiveSpecialUnitaryEquivGroup` maps a matrix class to its fixed-point class. -/
@[simp]
theorem projectiveSpecialUnitaryEquivGroup_mk (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (x : commutator (fixedSubgroup
      ((ofTwistedA r q hv).val.galoisFieldTwistedFrobenius (ofTwistedA r q hv).val.rank))) :
    projectiveSpecialUnitaryEquivGroup r q hv (QuotientGroup.mk (s := Subgroup.center _)
        (x : fixedSubgroup
          ((ofTwistedA r q hv).val.galoisFieldTwistedFrobenius (ofTwistedA r q hv).val.rank))) =
      ((MulEquiv.commutatorCongr (specialUnitaryEquivFixedPoints r q hv) x :
        commutator (ofTwistedA r q hv).FixedPoints) : (ofTwistedA r q hv).Group) :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect_mk _ _ x

/-- **The group attached to `²A_r(q)` is simple**, for every valid index. -/
theorem isSimpleGroup_group_ofTwistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ofTwistedA r q hv).Group := by
  obtain ⟨hr, hq⟩ := two_le_and_three_le_fieldOrder_of_valid hv
  have := (ofTwistedA r q hv).val.isSimpleGroup_quotient_center_galoisFieldTwistedFrobenius hr hq
  exact (projectiveSpecialUnitaryEquivGroup r q hv).symm.isSimpleGroup

end TauCeti.TypeALieIndex

namespace TauCeti.ValidLieTypeIndex

/-- **Every `²A_r(q)` on the classification list is simple.** -/
theorem isSimpleGroup_twistedA {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_twistedA, GraphTwistedIndex.steinberg_twistedA]
  exact TypeALieIndex.isSimpleGroup_group_ofTwistedA r q hv

end TauCeti.ValidLieTypeIndex

end
