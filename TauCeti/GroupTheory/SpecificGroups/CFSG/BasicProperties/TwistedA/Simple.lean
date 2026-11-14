/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Simple
import TauCeti.FieldTheory.Finite.Norm
import TauCeti.FieldTheory.Finite.PowAddSelf

/-!
# Perfectness and simplicity of the unitary groups on the classification list

For a valid graph-twisted type-`A` index `²A_r(q)`, the isomorphism
`TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints` identifies the Steinberg fixed points
`TauCeti.TypeALieIndex.FixedPoints` with the finite special unitary group `SU_{r+1}(q)`: the fixed
subgroup of the graph-twisted `q`-power Frobenius
`TauCeti.ValidLieTypeIndex.galoisFieldTwistedFrobenius` on `SL_{r+1}(𝔽_{q²})`. By
`TauCeti.ValidLieTypeIndex.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup`, that
fixed subgroup is the special isometry group `Matrix.specialIsometryGroup Q σ` of the
`(-1) ^ r`-Hermitian signed reversal matrix `Q = typeAGraphConjugator r` relative to the `q`-power
involution `σ : x ↦ x ^ q` of `𝔽_{q²}`.

Over `𝔽_{q²}`, the `(-1) ^ r`-trace `t ↦ t + (-1) ^ r t ^ q` is onto the `(-1) ^ r`-skew elements
with a nonzero kernel element (`TauCeti.FiniteField.exists_add_neg_one_pow_mul_pow_eq` and
`TauCeti.FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero`), the quadratic norm
`b ↦ b * b ^ q` is onto the `q`-power fixed elements (`TauCeti.FiniteField.exists_mul_pow_eq`), and
`x ↦ x ^ q` is nontrivial (`TauCeti.FiniteField.exists_pow_ne_self`). A valid `²A_r(q)` has `r ≥ 2`
and `q ≥ 3` when `r = 2` (excluding only the solvable group `SU₃(2)`), so either `r + 1 ≥ 4` or
`𝔽_{q²}` has a `q`-power fixed element other than `0` and `1`
(`TauCeti.FiniteField.exists_ne_zero_and_ne_one_and_pow_eq_self`).

Thus `SU_{r+1}(q)` is perfect (`Matrix.commutator_specialIsometryGroup_eq_top`) and its quotient by
the centre `PSU_{r+1}(q) = SU_{r+1}(q) ⧸ Z(SU_{r+1}(q))` is simple by Iwasawa's criterion
(`Matrix.isSimpleGroup_quotient_center_specialIsometryGroup`). Through
`TauCeti.DerivedCentralQuotient.quotientCenterEquivOfPerfect`, the candidate group
`TauCeti.TypeALieIndex.Group` of `²A_r(q)` is isomorphic to `PSU_{r+1}(q)`, establishing the
simplicity of every `²A_r(q)` on the classification list both on the family carrier and on the
assembled carrier `TauCeti.ValidLieTypeIndex.Group`.

## Main definitions and results

* `TauCeti.ValidLieTypeIndex.commutator_fixedSubgroup_galoisFieldTwistedFrobenius_eq_top`:
  `SU_{r+1}(q)` is perfect when `2 ≤ r` and `r = 2 → 3 ≤ q`.
* `TauCeti.ValidLieTypeIndex.isSimpleGroup_quotient_center_galoisFieldTwistedFrobenius`:
  `PSU_{r+1}(q)` is simple when `2 ≤ r` and `r = 2 → 3 ≤ q`.
* `TauCeti.TypeALieIndex.commutator_specialUnitary_eq_top`: the finite special unitary group of a
  valid `²A_r(q)` is perfect.
* `TauCeti.TypeALieIndex.projectiveSpecialUnitaryEquivGroup`: the group attached to `²A_r(q)` is
  `PSU_{r+1}(q)`.
* `TauCeti.TypeALieIndex.isSimpleGroup_group_ofTwistedA` and
  `TauCeti.ValidLieTypeIndex.isSimpleGroup_twistedA`: the group attached to `²A_r(q)` is simple.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), §§13.1 and 14.1.
* J. Dieudonné, *On the structure of unitary groups*, Trans. Amer. Math. Soc. **72** (1952),
  367--385.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), §10.4 and §11.5.

The organization follows `TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TypeA`, the
corresponding transport and simplicity proof for the untwisted type-`A` family.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.ValidLieTypeIndex

variable {d : ValidLieTypeIndex} {r : ℕ}

/-- The field `𝔽_{q²}` has `d.fieldOrder ^ 2` elements. -/
private theorem natCard_galoisField_two :
    Nat.card (GaloisField d.characteristic (d.fieldExponent * 2)) = d.fieldOrder ^ 2 := by
  rw [GaloisField.card _ _ (Nat.mul_ne_zero d.fieldExponent_pos.ne' two_ne_zero), pow_mul,
    ← d.fieldOrder_eq_characteristic_pow]

/-- The field `𝔽_{q²}` has `(p ^ e) ^ 2` elements. -/
private theorem natCard_galoisField_pow_sq :
    Nat.card (GaloisField d.characteristic (d.fieldExponent * 2)) =
      (d.characteristic ^ d.fieldExponent) ^ 2 := by
  rw [GaloisField.card _ _ (Nat.mul_ne_zero d.fieldExponent_pos.ne' two_ne_zero), pow_mul]

/-- The `(-1) ^ r`-trace of `𝔽_{q²}` is onto the `(-1) ^ r`-skew elements. -/
private theorem exists_add_neg_one_pow_mul_iterateFrobenius_eq
    {s : GaloisField d.characteristic (d.fieldExponent * 2)}
    (hs : iterateFrobenius _ d.characteristic d.fieldExponent s = (-1) ^ r * s) :
    ∃ t, t + (-1) ^ r * iterateFrobenius _ d.characteristic d.fieldExponent t = s := by
  simp_rw [iterateFrobenius_def] at hs ⊢
  exact FiniteField.exists_add_neg_one_pow_mul_pow_eq natCard_galoisField_pow_sq r hs

/-- The `(-1) ^ r`-trace of `𝔽_{q²}` has a nonzero kernel element. -/
private theorem exists_ne_zero_add_neg_one_pow_mul_iterateFrobenius_eq_zero :
    ∃ a ≠ (0 : GaloisField d.characteristic (d.fieldExponent * 2)),
      a + (-1) ^ r * iterateFrobenius _ d.characteristic d.fieldExponent a = 0 := by
  simp_rw [iterateFrobenius_def]
  exact FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero natCard_galoisField_pow_sq r

/-- The quadratic norm of `𝔽_{q²}` is onto the `q`-power fixed elements. -/
private theorem exists_mul_iterateFrobenius_eq
    {t : GaloisField d.characteristic (d.fieldExponent * 2)}
    (ht : iterateFrobenius _ d.characteristic d.fieldExponent t = t) :
    ∃ b, b * iterateFrobenius _ d.characteristic d.fieldExponent b = t := by
  simp_rw [coe_iterateFrobenius_galoisField] at ht ⊢
  exact FiniteField.exists_mul_pow_eq natCard_galoisField_two ht

/-- The `q`-power Frobenius of `𝔽_{q²}` is nontrivial. -/
private theorem exists_iterateFrobenius_ne_self :
    ∃ a : GaloisField d.characteristic (d.fieldExponent * 2),
      iterateFrobenius _ d.characteristic d.fieldExponent a ≠ a := by
  simp_rw [coe_iterateFrobenius_galoisField]
  exact FiniteField.exists_pow_ne_self natCard_galoisField_two

/-- When `2 ≤ r` and `r = 2 → 3 ≤ d.fieldOrder`, either `𝔽_{q²}` has a `q`-power fixed element other
than `0` and `1` or `4 ≤ r + 1`. -/
private theorem exists_fixed_or_four_le_of_two_le (hr : 2 ≤ r) (hq : r = 2 → 3 ≤ d.fieldOrder) :
    (∃ t : GaloisField d.characteristic (d.fieldExponent * 2),
        t ≠ 0 ∧ t ≠ 1 ∧ iterateFrobenius _ d.characteristic d.fieldExponent t = t) ∨
      4 ≤ Fintype.card (Fin (r + 1)) := by
  rcases hr.eq_or_lt with rfl | hr
  · left
    simp_rw [coe_iterateFrobenius_galoisField]
    exact FiniteField.exists_ne_zero_and_ne_one_and_pow_eq_self natCard_galoisField_two (hq rfl)
  · right
    rw [Fintype.card_fin]
    omega

/-- **The finite special unitary group `SU_{r+1}(q)` is perfect** when `2 ≤ r` and
`r = 2 → 3 ≤ q`. -/
theorem commutator_fixedSubgroup_galoisFieldTwistedFrobenius_eq_top
    (hr : 2 ≤ r) (hq : r = 2 → 3 ≤ d.fieldOrder) :
    commutator (fixedSubgroup (d.galoisFieldTwistedFrobenius r)) = ⊤ := by
  rw [fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup]
  exact Matrix.commutator_specialIsometryGroup_eq_top
    involutive_iterateFrobenius_galoisField transpose_map_typeAGraphConjugator_galoisField
    (isUnits_det_units _).ne_zero (fun _ ↦ exists_add_neg_one_pow_mul_iterateFrobenius_eq)
    exists_ne_zero_add_neg_one_pow_mul_iterateFrobenius_eq_zero
    (fun _ ↦ exists_mul_iterateFrobenius_eq) exists_iterateFrobenius_ne_self
    (by rw [Fintype.card_fin]; omega) (exists_fixed_or_four_le_of_two_le hr hq)

/-- **The projective special unitary group `PSU_{r+1}(q)` is simple** when `2 ≤ r` and
`r = 2 → 3 ≤ q`. -/
theorem isSimpleGroup_quotient_center_galoisFieldTwistedFrobenius
    (hr : 2 ≤ r) (hq : r = 2 → 3 ≤ d.fieldOrder) :
    IsSimpleGroup (fixedSubgroup (d.galoisFieldTwistedFrobenius r) ⧸
      Subgroup.center (fixedSubgroup (d.galoisFieldTwistedFrobenius r))) := by
  rw [fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup]
  exact Matrix.isSimpleGroup_quotient_center_specialIsometryGroup
    involutive_iterateFrobenius_galoisField transpose_map_typeAGraphConjugator_galoisField
    (isUnits_det_units _).ne_zero (fun _ ↦ exists_add_neg_one_pow_mul_iterateFrobenius_eq)
    exists_ne_zero_add_neg_one_pow_mul_iterateFrobenius_eq_zero
    (fun _ ↦ exists_mul_iterateFrobenius_eq) exists_iterateFrobenius_ne_self
    (by rw [Fintype.card_fin]; omega) (exists_fixed_or_four_le_of_two_le hr hq)

end TauCeti.ValidLieTypeIndex

namespace TauCeti.TypeALieIndex

/-- A valid `²A_r(q)` has rank at least two, and field order at least three in rank two. -/
private theorem two_le_and_three_le_card_of_valid {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) :=
  (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1

/-- **The finite special unitary group of `²A_r(q)` is perfect.** On at least four coordinates this
holds over every field, and a valid `²A₂(q)` has `q ≥ 3`, excluding the solvable group `SU₃(2)`. -/
theorem commutator_specialUnitary_eq_top (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    commutator (fixedSubgroup
      ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank)) = ⊤ := by
  obtain ⟨hr, hq⟩ := two_le_and_three_le_card_of_valid hv
  exact ValidLieTypeIndex.commutator_fixedSubgroup_galoisFieldTwistedFrobenius_eq_top
    (by simpa [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType] using hr)
    (by simpa [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
      ValidLieTypeIndex.fieldOrder] using hq)

/-- **The group attached to `²A_r(q)` is the projective special unitary group `PSU_{r+1}(q)`.**

The fixed points are `SU_{r+1}(q)` by `TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints`. That
group is perfect on every valid index, so its derived subgroup is the whole group and the derived
central quotient is its quotient by the centre. -/
def projectiveSpecialUnitaryEquivGroup (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    fixedSubgroup ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius
        (ofTwistedA r q hv).1.rank) ⧸
      Subgroup.center (fixedSubgroup ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius
        (ofTwistedA r q hv).1.rank)) ≃*
      (ofTwistedA r q hv).Group :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect
    (commutator_specialUnitary_eq_top r q hv) (specialUnitaryEquivFixedPoints r q hv)

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
which is simple by Iwasawa's criterion because `SU_{r+1}(q)` is perfect. -/
theorem isSimpleGroup_group_ofTwistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ofTwistedA r q hv).Group := by
  obtain ⟨hr, hq⟩ := two_le_and_three_le_card_of_valid hv
  have := ValidLieTypeIndex.isSimpleGroup_quotient_center_galoisFieldTwistedFrobenius
    (d := (ofTwistedA r q hv).1) (r := (ofTwistedA r q hv).1.rank)
    (by simpa [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType] using hr)
    (by simpa [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
      ValidLieTypeIndex.fieldOrder] using hq)
  exact (projectiveSpecialUnitaryEquivGroup r q hv).symm.isSimpleGroup

end TauCeti.TypeALieIndex

namespace TauCeti.ValidLieTypeIndex

/-- **Every `²A_r(q)` on the classification list is simple.** On the constructor `twistedA r q` the
Steinberg endomorphism of the assembly is that of the type-`A` family, so the assembled candidate
is the type-`A` one. -/
theorem isSimpleGroup_twistedA {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_twistedA, GraphTwistedIndex.steinberg_twistedA]
  exact TypeALieIndex.isSimpleGroup_group_ofTwistedA r q hv

end TauCeti.ValidLieTypeIndex

end
