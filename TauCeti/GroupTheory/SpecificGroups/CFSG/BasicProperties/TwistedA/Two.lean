/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.Simple
import TauCeti.FieldTheory.Finite.PowAddSelf
import TauCeti.FieldTheory.Finite.PowNeOne

/-!
# Perfectness of `SU₃(q)`, the projective unitary identification, and simplicity of `²A₂(q)`

For a valid classification index `LieTypeIndex.twistedA 2 q`,
`TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints` identifies the Steinberg fixed points of
`²A₂(q)` with the finite special unitary group `SU₃(q)`, realized as the fixed subgroup of the
graph-twisted `q`-power Frobenius on `SL₃(𝔽_{q²})`. By
`TauCeti.ValidLieTypeIndex.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup`,
that fixed subgroup is equal to the three-dimensional special isometry group
`Matrix.specialIsometryGroup (typeAGraphConjugator 2 _) σ` over `𝔽_{q²}` with the involutive `q`-th
power Frobenius `σ`.

A valid `²A₂(q)` has `q ≥ 3`: the group `SU₃(2)` is solvable of order `216` (the Hessian group
`3^{1+2} : Q₈`), so `q = 2` is excluded by `LieTypeIndex.InStandardRange`. For `q ≥ 3`, the finite
field `𝔽_{q²}` satisfies all four hypotheses of the rank-one unitary simplicity theorem in
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.Simple`:

* `σ` is involutive (`TauCeti.ValidLieTypeIndex.involutive_iterateFrobenius_galoisField`);
* `x ↦ x + σ x` has a nonzero kernel element
  (`TauCeti.FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero`);
* `x ↦ x + σ x` is surjective onto `{s | σ s = s}`
  (`TauCeti.FiniteField.exists_pow_add_self_eq`);
* `𝔽_{q²}ˣ` is cyclic of order `q² - 1 > q - 2 ≥ 1`, so some nonzero `a ∈ 𝔽_{q²}` satisfies
  `a ^ (q - 2) ≠ 1`, hence `a ^ 2 ≠ a ^ q = σ a`
  (`TauCeti.FiniteField.exists_ne_zero_pow_ne_one`).

Consequently `SU₃(q)` is perfect (`TauCeti.TypeALieIndex.commutator_specialUnitary_two_eq_top`),
the candidate group attached to `²A₂(q)` is isomorphic to the projective special unitary group
`PSU₃(q) = SU₃(q) ⧸ Z(SU₃(q))` (`TauCeti.TypeALieIndex.projectiveSpecialUnitaryEquivGroupTwo`),
and every `²A₂(q)` on the classification list is simple, both on the type-`A` index
(`TauCeti.TypeALieIndex.isSimpleGroup_group_ofTwistedA_two`) and on the assembled Lie-type carrier
(`TauCeti.ValidLieTypeIndex.isSimpleGroup_twistedA_two`).

## Main definitions and results

* `ValidLieTypeIndex.commutator_fixedSubgroup_galoisFieldTwistedFrobenius_two_eq_top`:
  `SU₃(q)` is perfect whenever `3 ≤ d.fieldOrder`.
* `ValidLieTypeIndex.isSimpleGroup_quotient_center_fixedSubgroup_galoisFieldTwistedFrobenius_two`:
  `PSU₃(q)` is simple whenever `3 ≤ d.fieldOrder`.
* `TauCeti.TypeALieIndex.three_le_fieldOrder_ofTwistedA_two`: a valid `²A₂(q)` has `q ≥ 3`.
* `TauCeti.TypeALieIndex.commutator_specialUnitary_two_eq_top`: `SU₃(q)` is perfect for every valid
  `²A₂(q)`.
* `TauCeti.TypeALieIndex.projectiveSpecialUnitaryEquivGroupTwo`: the group attached to `²A₂(q)` is
  `PSU₃(q)`.
* `TauCeti.TypeALieIndex.isSimpleGroup_group_ofTwistedA_two` and
  `TauCeti.ValidLieTypeIndex.isSimpleGroup_twistedA_two`: every `²A₂(q)` on the classification list
  is simple.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), §§13.3 and 14.1.
* D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*,
  Number 1, §2.2, for the exclusion of `²A₂(2)`.
-/

public section

noncomputable section

namespace TauCeti.ValidLieTypeIndex

section RankTwoUnitary

variable {d : ValidLieTypeIndex}

private theorem natCard_galoisField_eq_sq :
    Nat.card (GaloisField d.characteristic (d.fieldExponent * 2)) =
      (d.characteristic ^ d.fieldExponent) ^ 2 := by
  rw [GaloisField.card _ _ (Nat.mul_ne_zero d.fieldExponent_pos.ne' two_ne_zero), pow_mul]

private theorem exists_ne_zero_add_iterateFrobenius_eq_zero :
    ∃ b : GaloisField d.characteristic (d.fieldExponent * 2), b ≠ 0 ∧
      b + iterateFrobenius _ d.characteristic d.fieldExponent b = 0 := by
  obtain ⟨b, hb0, hb⟩ :=
    FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero (d.natCard_galoisField_eq_sq) 2
  exact ⟨b, hb0, by simpa [iterateFrobenius_def] using hb⟩

private theorem exists_add_iterateFrobenius_eq
    (s : GaloisField d.characteristic (d.fieldExponent * 2))
    (hs : iterateFrobenius _ d.characteristic d.fieldExponent s = s) :
    ∃ t : GaloisField d.characteristic (d.fieldExponent * 2),
      t + iterateFrobenius _ d.characteristic d.fieldExponent t = s := by
  rw [iterateFrobenius_def] at hs
  obtain ⟨t, ht⟩ := FiniteField.exists_pow_add_self_eq d.natCard_galoisField_eq_sq hs
  exact ⟨t, by rw [iterateFrobenius_def, add_comm, ht]⟩

private theorem exists_ne_zero_sq_ne_iterateFrobenius (hd : 3 ≤ d.fieldOrder) :
    ∃ a : GaloisField d.characteristic (d.fieldExponent * 2), a ≠ 0 ∧
      a ^ 2 ≠ iterateFrobenius _ d.characteristic d.fieldExponent a := by
  have hk0 : d.fieldOrder - 2 ≠ 0 := by omega
  have hk2 : (d.fieldOrder - 2) + 2 = d.fieldOrder := by omega
  have hcard : d.fieldOrder - 2 + 1 <
      Nat.card (GaloisField d.characteristic (d.fieldExponent * 2)) := by
    rw [d.natCard_galoisField_eq_sq, ← d.fieldOrder_eq_characteristic_pow]
    exact lt_of_lt_of_le (by omega) (Nat.le_self_pow two_ne_zero _)
  obtain ⟨a, ha0, ha⟩ := FiniteField.exists_ne_zero_pow_ne_one hk0 hcard
  refine ⟨a, ha0, fun heq ↦ ha ?_⟩
  rw [d.coe_iterateFrobenius_galoisField] at heq
  have hpow : a ^ d.fieldOrder = a ^ 2 * a ^ (d.fieldOrder - 2) := by
    rw [← pow_add, add_comm, hk2]
  apply mul_left_cancel₀ (pow_ne_zero 2 ha0)
  rw [← hpow, mul_one, heq]

/-- **The finite special unitary group `SU₃(q)` is perfect** whenever `3 ≤ d.fieldOrder`. -/
theorem commutator_fixedSubgroup_galoisFieldTwistedFrobenius_two_eq_top
    (hd : 3 ≤ d.fieldOrder) :
    commutator (fixedSubgroup (d.galoisFieldTwistedFrobenius 2)) = ⊤ := by
  rw [d.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup 2]
  exact UnitaryRankOne.commutator_eq_top d.involutive_iterateFrobenius_galoisField
    d.exists_ne_zero_add_iterateFrobenius_eq_zero d.exists_add_iterateFrobenius_eq
    (d.exists_ne_zero_sq_ne_iterateFrobenius hd)

/-- **The projective special unitary group `PSU₃(q)` is simple** whenever `3 ≤ d.fieldOrder`. -/
theorem isSimpleGroup_quotient_center_fixedSubgroup_galoisFieldTwistedFrobenius_two
    (hd : 3 ≤ d.fieldOrder) :
    IsSimpleGroup (fixedSubgroup (d.galoisFieldTwistedFrobenius 2) ⧸
      Subgroup.center (fixedSubgroup (d.galoisFieldTwistedFrobenius 2))) := by
  rw [d.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup 2]
  exact UnitaryRankOne.isSimpleGroup_quotient_center d.involutive_iterateFrobenius_galoisField
    d.exists_ne_zero_add_iterateFrobenius_eq_zero d.exists_add_iterateFrobenius_eq
    (d.exists_ne_zero_sq_ne_iterateFrobenius hd)

end RankTwoUnitary

end TauCeti.ValidLieTypeIndex

namespace TauCeti.TypeALieIndex

/-- A valid `²A₂(q)` index has Frobenius parameter `q ≥ 3`; `²A₂(2)` is excluded as solvable. -/
theorem three_le_fieldOrder_ofTwistedA_two (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    3 ≤ (ofTwistedA 2 q hv).1.fieldOrder := by
  simpa only [ValidLieTypeIndex.fieldOrder, LieTypeIndex.fieldOrder_twistedA] using
    (((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).2 rfl)

/-- **The finite special unitary group `SU₃(q)` of a valid `²A₂(q)` is perfect.** -/
theorem commutator_specialUnitary_two_eq_top (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    commutator (fixedSubgroup ((ofTwistedA 2 q hv).1.galoisFieldTwistedFrobenius 2)) = ⊤ :=
  (ofTwistedA 2 q hv).1.commutator_fixedSubgroup_galoisFieldTwistedFrobenius_two_eq_top
    (three_le_fieldOrder_ofTwistedA_two q hv)

/-- **The group attached to `²A₂(q)` is the projective special unitary group `PSU₃(q)`.**

The Steinberg fixed points are isomorphic to `SU₃(q)` by
`TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints`. Since `SU₃(q)` is perfect for `q ≥ 3`, its
derived subgroup is the whole group and the derived central quotient is `SU₃(q) ⧸ Z(SU₃(q))`. -/
def projectiveSpecialUnitaryEquivGroupTwo (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    fixedSubgroup ((ofTwistedA 2 q hv).1.galoisFieldTwistedFrobenius 2) ⧸
        Subgroup.center (fixedSubgroup ((ofTwistedA 2 q hv).1.galoisFieldTwistedFrobenius 2)) ≃*
      (ofTwistedA 2 q hv).Group :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect (commutator_specialUnitary_two_eq_top q hv)
    (specialUnitaryEquivFixedPoints 2 q hv)

/-- The isomorphism with `PSU₃(q)` sends the central coset of a matrix in the derived subgroup to
the class of the corresponding Steinberg fixed point. -/
@[simp]
theorem projectiveSpecialUnitaryEquivGroupTwo_mk (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (x : commutator (fixedSubgroup ((ofTwistedA 2 q hv).1.galoisFieldTwistedFrobenius 2))) :
    projectiveSpecialUnitaryEquivGroupTwo q hv (QuotientGroup.mk (s := Subgroup.center _)
        (x : fixedSubgroup ((ofTwistedA 2 q hv).1.galoisFieldTwistedFrobenius 2))) =
      ((MulEquiv.commutatorCongr (specialUnitaryEquivFixedPoints 2 q hv) x :
        commutator (ofTwistedA 2 q hv).FixedPoints) : (ofTwistedA 2 q hv).Group) :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect_mk _ _ x

/-- **The group attached to `²A₂(q)` is simple**, for every valid index. -/
theorem isSimpleGroup_group_ofTwistedA_two (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    IsSimpleGroup (ofTwistedA 2 q hv).Group :=
  let d := (ofTwistedA 2 q hv).1
  have := d.isSimpleGroup_quotient_center_fixedSubgroup_galoisFieldTwistedFrobenius_two
    (three_le_fieldOrder_ofTwistedA_two q hv)
  (projectiveSpecialUnitaryEquivGroupTwo q hv).symm.isSimpleGroup

end TauCeti.TypeALieIndex

namespace TauCeti.ValidLieTypeIndex

/-- **Every `²A₂(q)` on the classification list is simple.** On the constructor `twistedA 2 q` the
Steinberg endomorphism of the assembly is that of the type-`A` family, so the assembled candidate
group is `(TypeALieIndex.ofTwistedA 2 q hv).Group`. -/
theorem isSimpleGroup_twistedA_two {q : PrimePower} (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_twistedA, GraphTwistedIndex.steinberg_twistedA]
  exact TypeALieIndex.isSimpleGroup_group_ofTwistedA_two q hv

end TauCeti.ValidLieTypeIndex

end
