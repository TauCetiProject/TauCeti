/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Perfect
import TauCeti.FieldTheory.Finite.PowAddSelf
import TauCeti.FieldTheory.Finite.QuadraticNorm

/-!
# Perfectness, projective special unitary model, and simplicity of `²A_r(q)`

For a valid graph-twisted type-`A` index `²A_r(q)`, the isomorphism
`TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints` identifies the Steinberg fixed points with
the finite special unitary group `SU_{r+1}(q)` — the subgroup
`fixedSubgroup ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius r)` of `SL_{r+1}(𝔽_{q²})`, which
`ValidLieTypeIndex.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup` equates with
the special isometry group of `typeAGraphConjugator r` relative to `x ↦ x ^ q`.

Over `𝔽_{q²}`, the trace `t ↦ t + t ^ q` and norm `b ↦ b ^ q * b` are both onto `{s | s ^ q = s}`,
and `d + d ^ q = 0` has a nonzero solution (`TauCeti.FiniteField.exists_pow_add_self_eq`,
`TauCeti.FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero`, and
`TauCeti.FiniteField.exists_pow_mul_self_eq`). A valid `²A_r(q)` has `r ≥ 2`, with `q ≥ 3` when
`r = 2` (excluding the solvable group `SU₃(2)`), where
`TauCeti.FiniteField.exists_pow_eq_self_and_ne_zero_and_ne_one` supplies an element of `𝔽_q`
distinct from `0` and `1`. By `TauCeti.commutator_specialIsometryGroup_typeAGraphConjugator` and
`TauCeti.isSimpleGroup_quotient_center_typeAGraphConjugator`, `SU_{r+1}(q)` is perfect and its
central quotient `PSU_{r+1}(q)` is simple.

Through `TauCeti.DerivedCentralQuotient.quotientCenterEquivOfPerfect`, the candidate group attached
to `²A_r(q)` is isomorphic to `PSU_{r+1}(q)`, proving simplicity both on `TauCeti.TypeALieIndex`
and on the assembled Lie-type carrier `TauCeti.ValidLieTypeIndex.Group`.

## Main definitions and results

* `TauCeti.ValidLieTypeIndex.commutator_galoisFieldTwistedFrobenius_eq_top` and
  `TauCeti.ValidLieTypeIndex.isSimpleGroup_quotient_center_galoisFieldTwistedFrobenius`:
  perfectness of `SU_{r+1}(q)` and simplicity of `PSU_{r+1}(q)` for `2 ≤ r` and `r = 2 → 3 ≤ q`.
* `TauCeti.TypeALieIndex.commutator_specialUnitary_eq_top`: `SU_{r+1}(q)` is perfect for every
  valid `²A_r(q)`.
* `TauCeti.TypeALieIndex.projectiveSpecialUnitaryEquivGroup`: the group attached to `²A_r(q)` is
  `PSU_{r+1}(q)`.
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

private theorem natCard_extensionGaloisField_two_eq_pow_sq :
    Nat.card (GaloisField d.characteristic (d.fieldExponent * 2)) =
      (d.characteristic ^ d.fieldExponent) ^ 2 := by
  rw [GaloisField.card _ _ (Nat.mul_ne_zero d.fieldExponent_pos.ne' two_ne_zero), pow_mul]

private theorem natCard_extensionGaloisField_two_eq_fieldOrder_sq :
    Nat.card (GaloisField d.characteristic (d.fieldExponent * 2)) = d.fieldOrder ^ 2 := by
  rw [d.natCard_extensionGaloisField_two_eq_pow_sq, ← d.fieldOrder_eq_characteristic_pow]

private theorem exists_add_iterateFrobenius_eq_of_eq
    {s : GaloisField d.characteristic (d.fieldExponent * 2)}
    (hs : iterateFrobenius _ d.characteristic d.fieldExponent s = s) :
    ∃ t, t + iterateFrobenius _ d.characteristic d.fieldExponent t = s := by
  rw [iterateFrobenius_def] at hs
  obtain ⟨t, ht⟩ := FiniteField.exists_pow_add_self_eq d.natCard_extensionGaloisField_two_eq_pow_sq
    hs
  exact ⟨t, by rwa [iterateFrobenius_def, add_comm]⟩

private theorem exists_ne_zero_add_iterateFrobenius_eq_zero :
    ∃ a ≠ (0 : GaloisField d.characteristic (d.fieldExponent * 2)),
      a + iterateFrobenius _ d.characteristic d.fieldExponent a = 0 := by
  obtain ⟨a, ha0, ha⟩ := FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero
    d.natCard_extensionGaloisField_two_eq_pow_sq 0
  exact ⟨a, ha0, by simpa [iterateFrobenius_def] using ha⟩

private theorem exists_iterateFrobenius_mul_self_eq_of_eq
    {s : GaloisField d.characteristic (d.fieldExponent * 2)}
    (hs : iterateFrobenius _ d.characteristic d.fieldExponent s = s) :
    ∃ b, iterateFrobenius _ d.characteristic d.fieldExponent b * b = s := by
  rw [coe_iterateFrobenius_galoisField] at hs
  obtain ⟨b, hb⟩ := FiniteField.exists_pow_mul_self_eq
    d.natCard_extensionGaloisField_two_eq_fieldOrder_sq hs
  exact ⟨b, by simpa [coe_iterateFrobenius_galoisField] using hb⟩

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
  exact commutator_specialIsometryGroup_typeAGraphConjugator
    d.involutive_iterateFrobenius_galoisField
    (fun _ ↦ d.exists_add_iterateFrobenius_eq_of_eq)
    d.exists_ne_zero_add_iterateFrobenius_eq_zero hr
    (fun _ _ ↦ d.exists_iterateFrobenius_mul_self_eq_of_eq)
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
    (fun _ ↦ d.exists_add_iterateFrobenius_eq_of_eq)
    d.exists_ne_zero_add_iterateFrobenius_eq_zero hr
    (fun _ _ ↦ d.exists_iterateFrobenius_mul_self_eq_of_eq)
    (d.rank_ne_two_or_exists_iterateFrobenius_fixed hq)

end FiniteUnitary

end TauCeti.ValidLieTypeIndex

namespace TauCeti.TypeALieIndex

/-- A valid `²A_r(q)` index has rank at least two, and field order at least three in rank two. -/
private theorem two_le_and_three_le_fieldOrder_of_valid {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    2 ≤ (ofTwistedA r q hv).1.rank ∧
      ((ofTwistedA r q hv).1.rank = 2 → 3 ≤ (ofTwistedA r q hv).1.fieldOrder) := by
  simpa [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType, ValidLieTypeIndex.fieldOrder] using
    (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1

/-- **The finite special unitary group of `²A_r(q)` is perfect.** The validity predicate imposes
`2 ≤ r` and `r = 2 → 3 ≤ q`, excluding the solvable group `SU₃(2)`. -/
theorem commutator_specialUnitary_eq_top (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    commutator (fixedSubgroup
      ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank)) = ⊤ := by
  obtain ⟨hr, hq⟩ := two_le_and_three_le_fieldOrder_of_valid hv
  exact (ofTwistedA r q hv).1.commutator_galoisFieldTwistedFrobenius_eq_top hr hq

/-- **The group attached to `²A_r(q)` is the projective special unitary group `PSU_{r+1}(q)`.**

The Steinberg fixed points are `SU_{r+1}(q)` by
`TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints`. That group is perfect on every valid index,
so its derived subgroup is the whole group and the derived central quotient is its quotient by the
centre. -/
def projectiveSpecialUnitaryEquivGroup (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    fixedSubgroup ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank) ⧸
      Subgroup.center (fixedSubgroup
        ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank)) ≃*
      (ofTwistedA r q hv).Group :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect (commutator_specialUnitary_eq_top r q hv)
    (specialUnitaryEquivFixedPoints r q hv)

/-- The isomorphism with `PSU_{r+1}(q)` sends the class of a matrix in the derived subgroup to the
class of the corresponding fixed point. -/
@[simp]
theorem projectiveSpecialUnitaryEquivGroup_mk (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (x : commutator (fixedSubgroup
      ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank))) :
    projectiveSpecialUnitaryEquivGroup r q hv (QuotientGroup.mk (s := Subgroup.center _)
        (x : fixedSubgroup
          ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank))) =
      ((MulEquiv.commutatorCongr (specialUnitaryEquivFixedPoints r q hv) x :
        commutator (ofTwistedA r q hv).FixedPoints) : (ofTwistedA r q hv).Group) :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect_mk _ _ x

/-- **The group attached to `²A_r(q)` is simple**, for every valid index: it is `PSU_{r+1}(q)`,
which is simple by Iwasawa's criterion. -/
theorem isSimpleGroup_group_ofTwistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ofTwistedA r q hv).Group := by
  obtain ⟨hr, hq⟩ := two_le_and_three_le_fieldOrder_of_valid hv
  have := (ofTwistedA r q hv).1.isSimpleGroup_quotient_center_galoisFieldTwistedFrobenius hr hq
  exact (projectiveSpecialUnitaryEquivGroup r q hv).symm.isSimpleGroup

end TauCeti.TypeALieIndex

namespace TauCeti.ValidLieTypeIndex

/-- **Every `²A_r(q)` on the classification list is simple.** On the constructor `twistedA r q` the
Steinberg endomorphism of the assembly is that of the type-`A` family, so the assembled candidate
group is the twisted type-`A` one. -/
theorem isSimpleGroup_twistedA {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_twistedA, GraphTwistedIndex.steinberg_twistedA]
  exact TypeALieIndex.isSimpleGroup_group_ofTwistedA r q hv

end TauCeti.ValidLieTypeIndex

end
