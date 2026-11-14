/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.Simple

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
field `𝔽_{q²}` has cardinality `q²` (`TauCeti.ValidLieTypeIndex.natCard_galoisField`) and `σ` acts
as `a ↦ a ^ q` (`TauCeti.ValidLieTypeIndex.coe_iterateFrobenius_galoisField`), so
`TauCeti.UnitaryRankOne.commutator_eq_top_of_natCard_eq_sq` and
`TauCeti.UnitaryRankOne.isSimpleGroup_quotient_center_of_natCard_eq_sq` apply directly.

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

/-- **The finite special unitary group `SU₃(q)` is perfect** whenever `3 ≤ d.fieldOrder`. -/
theorem commutator_fixedSubgroup_galoisFieldTwistedFrobenius_two_eq_top
    (hd : 3 ≤ d.fieldOrder) :
    commutator (fixedSubgroup (d.galoisFieldTwistedFrobenius 2)) = ⊤ := by
  rw [d.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup 2]
  exact UnitaryRankOne.commutator_eq_top_of_natCard_eq_sq hd
    (by rw [d.natCard_galoisField, ← d.fieldOrder_eq_characteristic_pow])
    (congrFun d.coe_iterateFrobenius_galoisField)

/-- **The projective special unitary group `PSU₃(q)` is simple** whenever `3 ≤ d.fieldOrder`. -/
theorem isSimpleGroup_quotient_center_fixedSubgroup_galoisFieldTwistedFrobenius_two
    (hd : 3 ≤ d.fieldOrder) :
    IsSimpleGroup (fixedSubgroup (d.galoisFieldTwistedFrobenius 2) ⧸
      Subgroup.center (fixedSubgroup (d.galoisFieldTwistedFrobenius 2))) := by
  rw [d.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup 2]
  exact UnitaryRankOne.isSimpleGroup_quotient_center_of_natCard_eq_sq hd
    (by rw [d.natCard_galoisField, ← d.fieldOrder_eq_characteristic_pow])
    (congrFun d.coe_iterateFrobenius_galoisField)

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
