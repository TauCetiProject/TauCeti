/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialLinearFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
public import TauCeti.LinearAlgebra.Projectivization.PSL.Simple

/-!
# Finiteness and simplicity of the untwisted type-`A` groups on the classification list

The type-`A` carrier of `TauCeti.TypeALieIndex` is the explicit full-weight Chevalley carrier, and
`TauCeti.TypeALieIndex.carrierEquivSpecialLinear` identifies it with the standard matrix group
`SL_{r+1}` over the algebraic closure of the prime field. On the untwisted family `A_r(q)` the
graph factor of the standard Steinberg map is trivial, so that standard Steinberg map is the
entrywise `q`-power Frobenius (`TauCeti.TypeALieIndex.specialLinearSteinberg_ofA`).

This file transports the fixed points of the Steinberg map along that identification. The carrier
equivalence intertwines the carrier Steinberg map with the standard one, so
`TauCeti.fixedSubgroupCongr` turns their fixed subgroups into isomorphic groups, and the standard
fixed subgroup is the finite special linear group `SL_{r+1}(𝔽_q)` of
`TauCeti.ValidLieTypeIndex.specialLinearEquivFrobeniusFixedPoints`. The composite is
`TauCeti.TypeALieIndex.specialLinearEquivFixedPoints`, an isomorphism between that finite matrix
group and the fixed points `TauCeti.TypeALieIndex.FixedPoints` of the index.

Both groups attached to `A_r(q)` are then finite: the fixed points themselves, and the derived
central quotient `TauCeti.TypeALieIndex.Group` of them, which inherits finiteness from the fixed
points because a derived subgroup and a quotient by the centre of a finite group are finite.

On every valid index `SL_{r+1}(𝔽_q)` is perfect: on at least three coordinates over every field,
and on two coordinates because a valid `A₁(q)` has `q ≥ 4`. Its derived subgroup is then the
whole group, so the derived central quotient of the fixed points is the projective special linear
group `PSL_{r+1}(𝔽_q)`, which is simple by Iwasawa's criterion
(`Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_commutator_eq_top`). This is the
simplicity of every untwisted type-`A` group on the classification list, read both on the family
carrier and on the assembled carrier `TauCeti.ValidLieTypeIndex.Group`. No order is computed.

## Main definitions and results

* `TauCeti.TypeALieIndex.specialLinearEquivFixedPoints`: the fixed points of the Steinberg map
  of `A_r(q)` are the finite special linear group `SL_{r+1}(𝔽_q)`.
* `TauCeti.TypeALieIndex.finite_fixedPoints_ofA` and `TauCeti.TypeALieIndex.finite_group_ofA`: the
  fixed points and the derived central quotient of `A_r(q)` are finite.
* `TauCeti.TypeALieIndex.projectiveSpecialLinearEquivGroup`: the group attached to `A_r(q)` is
  `PSL_{r+1}(𝔽_q)`.
* `TauCeti.TypeALieIndex.isSimpleGroup_group_ofA` and `TauCeti.ValidLieTypeIndex.isSimpleGroup_A`:
  the group attached to `A_r(q)` is simple.

## Provenance

The identification of the fixed points with `SL_{r+1}(𝔽_q)` adapts
`CFSG/TypeALinearCandidate.lean` from
`https://github.com/AxiomMath/CFSG` (Apache-2.0), commit
`69cb972f587a3ecc035e092253167ff2e303c962`.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.TypeALieIndex

/-- **The Steinberg fixed points of `A_r(q)` are the finite special linear group
`SL_{r+1}(𝔽_q)`.**

The carrier equivalence intertwines the two Steinberg maps, so it identifies their fixed subgroups,
while the standard fixed subgroup is the finite special linear group by the coefficient
identification. Both transports are the general group-theoretic ones. -/
def specialLinearEquivFixedPoints (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) :
    SpecialLinearGroup (Fin ((ofA r q hv).1.rank + 1))
      (GaloisField (ofA r q hv).1.characteristic (ofA r q hv).1.fieldExponent) ≃*
      (ofA r q hv).FixedPoints := by
  let d := ofA r q hv
  have hintertwine : d.carrierEquivSpecialLinear.toMonoidHom.comp d.steinberg =
      d.specialLinearSteinberg.comp d.carrierEquivSpecialLinear.toMonoidHom :=
    MonoidHom.ext fun g => d.carrierEquivSpecialLinear_steinberg g
  let e := TauCeti.fixedSubgroupCongr d.carrierEquivSpecialLinear hintertwine
  have hF := specialLinearSteinberg_ofA r q hv
  let eF : ↥(fixedSubgroup d.specialLinearSteinberg) ≃*
      fixedSubgroup (SpecialLinearGroup.map (n := Fin (d.1.rank + 1))
        (iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent)) :=
    MulEquiv.subgroupCongr (congrArg fixedSubgroup hF)
  exact (ValidLieTypeIndex.specialLinearEquivFrobeniusFixedPoints d.1
    (Fin (d.1.rank + 1))).trans (eF.symm.trans e.symm)

/-- The isomorphism to the finite special linear group sends a finite-field matrix to the fixed
point whose image under the carrier equivalence is that matrix read over the closure. -/
@[simp]
theorem specialLinearEquivFixedPoints_apply (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid)
    (g : SpecialLinearGroup (Fin ((ofA r q hv).1.rank + 1))
      (GaloisField (ofA r q hv).1.characteristic (ofA r q hv).1.fieldExponent)) :
    ((specialLinearEquivFixedPoints r q hv g : (ofA r q hv).FixedPoints) :
        (ofA r q hv).AmbientGroup) =
      (ofA r q hv).carrierEquivSpecialLinear.symm
        (ValidLieTypeIndex.specialLinearEquivFrobeniusFixedPoints (ofA r q hv).1
          (Fin ((ofA r q hv).1.rank + 1)) g) := by
  unfold specialLinearEquivFixedPoints
  simp only [MulEquiv.trans_apply]
  erw [TauCeti.coe_fixedSubgroupCongr_symm_apply]
  rw [MulEquiv.subgroupCongr_symm_apply]

/-- The Steinberg fixed points of `A_r(q)` are finite. -/
instance finite_fixedPoints_ofA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) : Finite (ofA r q hv).FixedPoints :=
  Finite.of_equiv _ (specialLinearEquivFixedPoints r q hv).toEquiv

/-- **The group attached to `A_r(q)` is finite.** It is the derived subgroup of the Steinberg fixed
points, modulo the centre of that derived subgroup, so it is finite because the fixed points are. -/
instance finite_group_ofA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) : Finite (ofA r q hv).Group :=
  finiteFixedPointCandidate (F := (ofA r q hv).steinberg)
    (h := finite_fixedPoints_ofA r q hv)

/-- A valid `A_r(q)` has rank at least one, and field order at least four in rank one. -/
private theorem one_le_and_four_le_card_of_valid {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) : 1 ≤ r ∧ (r = 1 → 4 ≤ q.card) :=
  (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1

/-- **The finite special linear group of `A_r(q)` is perfect.** On at least three coordinates
this holds over every field, and a valid `A₁(q)` has `q ≥ 4`. The validity predicate excludes
exactly the two nonperfect groups `SL₂(𝔽₂)` and `SL₂(𝔽₃)`. -/
theorem commutator_specialLinearGroup_eq_top (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) :
    commutator (SpecialLinearGroup (Fin ((ofA r q hv).1.rank + 1))
      (GaloisField (ofA r q hv).1.characteristic (ofA r q hv).1.fieldExponent)) = ⊤ := by
  obtain ⟨hr, hq⟩ := one_le_and_four_le_card_of_valid hv
  rcases hr.eq_or_lt with rfl | hr
  · apply SpecialLinearGroup.commutator_eq_top_of_four_le_natCard
    simpa [ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent,
      GaloisField.card _ _ q.exponent_pos.ne'] using hq rfl
  · exact SpecialLinearGroup.commutator_eq_top_of_three_le_card
      (by
        rw [Fintype.card_fin]
        simp [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType]
        omega)

/-- **The group attached to `A_r(q)` is the projective special linear group `PSL_{r+1}(𝔽_q)`.**

The fixed points are `SL_{r+1}(𝔽_q)` by `TauCeti.TypeALieIndex.specialLinearEquivFixedPoints`.
That group is perfect on every valid index, so its derived subgroup is the whole group and the
derived central quotient is its quotient by the centre. -/
def projectiveSpecialLinearEquivGroup (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) :
    ProjectiveSpecialLinearGroup (Fin ((ofA r q hv).1.rank + 1))
      (GaloisField (ofA r q hv).1.characteristic (ofA r q hv).1.fieldExponent) ≃*
      (ofA r q hv).Group :=
  letI : Group.IsPerfect (SpecialLinearGroup (Fin ((ofA r q hv).1.rank + 1))
      (GaloisField (ofA r q hv).1.characteristic (ofA r q hv).1.fieldExponent)) :=
    ⟨commutator_specialLinearGroup_eq_top r q hv⟩
  DerivedCentralQuotient.mulEquivQuotientCenter.symm.trans
    (DerivedCentralQuotient.congr (specialLinearEquivFixedPoints r q hv))

/-- The isomorphism with `PSL_{r+1}(𝔽_q)` sends the class of a matrix in the derived subgroup to
the class of the corresponding fixed point. -/
@[simp]
theorem projectiveSpecialLinearEquivGroup_mk (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid)
    (x : commutator (SpecialLinearGroup (Fin ((ofA r q hv).1.rank + 1))
      (GaloisField (ofA r q hv).1.characteristic (ofA r q hv).1.fieldExponent))) :
    projectiveSpecialLinearEquivGroup r q hv (QuotientGroup.mk (s := Subgroup.center _)
        (x : Matrix.SpecialLinearGroup (Fin ((ofA r q hv).1.rank + 1))
          (GaloisField (ofA r q hv).1.characteristic (ofA r q hv).1.fieldExponent))) =
      ((MulEquiv.commutatorCongr (specialLinearEquivFixedPoints r q hv) x :
        commutator (ofA r q hv).FixedPoints) : (ofA r q hv).Group) := by
  let _ : Group.IsPerfect (SpecialLinearGroup (Fin ((ofA r q hv).1.rank + 1))
      (GaloisField (ofA r q hv).1.characteristic (ofA r q hv).1.fieldExponent)) :=
    ⟨commutator_specialLinearGroup_eq_top r q hv⟩
  rw [projectiveSpecialLinearEquivGroup, MulEquiv.trans_apply,
    ← DerivedCentralQuotient.mulEquivQuotientCenter_mk, MulEquiv.symm_apply_apply,
    DerivedCentralQuotient.congr_mk]

/-- **The group attached to `A_r(q)` is simple**, for every valid index: it is `PSL_{r+1}(𝔽_q)`,
which is simple by Iwasawa's criterion because `SL_{r+1}(𝔽_q)` is perfect. -/
theorem isSimpleGroup_group_ofA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    IsSimpleGroup (ofA r q hv).Group :=
  have : Nontrivial (Fin ((ofA r q hv).1.rank + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (by
      simpa [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType] using
        (one_le_and_four_le_card_of_valid hv).1)
  have := ProjectiveSpecialLinearGroup.isSimpleGroup_of_commutator_eq_top
    (commutator_specialLinearGroup_eq_top r q hv)
  (projectiveSpecialLinearEquivGroup r q hv).symm.isSimpleGroup

end TauCeti.TypeALieIndex

namespace TauCeti.ValidLieTypeIndex

/-- **Every `A_r(q)` on the classification list is simple.** On the constructor `A r q` the
Steinberg endomorphism of the assembly is that of the type-`A` family, so the assembled candidate
is the type-`A` one. -/
theorem isSimpleGroup_A {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_A, GraphTwistedIndex.steinberg_A]
  exact TypeALieIndex.isSimpleGroup_group_ofA r q hv

end TauCeti.ValidLieTypeIndex

end
