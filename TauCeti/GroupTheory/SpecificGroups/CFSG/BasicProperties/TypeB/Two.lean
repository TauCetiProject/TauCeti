/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.SymplecticFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.SpinAgreement
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Simple

/-!
# The Steinberg fixed points of `B₂(q)`, its projective symplectic group and its simplicity

The untwisted family `Bₙ(q)` is built at every rank on the full-weight spin carrier, and its
Steinberg map is the carrier's `q`-power Frobenius. At rank two the spin representation of
`Spin₅` is the standard representation of `Sp₄`: `TauCeti.TypeB2LieIndex.spinEquivCarrier`
identifies the spin carrier of `B₂(q)` with the rank-two standard symplectic carrier, and
`TauCeti.RankTwoBLieIndex.carrierEquivSymplectic` identifies that carrier with the standard
symplectic matrix group `Sp₄` over the algebraic closure of the prime field. Both identifications
intertwine the `q`-power Frobenius maps, so their composite carries the Steinberg map of `B₂(q)` to
the entrywise `q`-power Frobenius of `Sp₄`.

This file transports the fixed points of the Steinberg map along that composite. By
`TauCeti.fixedSubgroupCongr` the fixed points of the Steinberg map are those of the entrywise
Frobenius, which form the finite symplectic group `Sp₄(𝔽_q)` of
`TauCeti.ValidLieTypeIndex.symplecticEquivFrobeniusFixedPoints`. The resulting isomorphism is
`TauCeti.TypeB2LieIndex.symplecticEquivFixedPoints`.

A valid `B₂(q)` has `q ≥ 4`: `B₂(2)` is excluded from the classification list as non-simple, by
the standard range, and `B₂(3)` as a duplicate representative. The field `𝔽_q` therefore has an
element other than `0` and `1`, so `Sp₄(𝔽_q)` is perfect by
`TauCeti.GLSymplecticFin.commutator_eq_top_of_two_le`. Its derived subgroup is then the whole group,
and the candidate group of `B₂(q)`, the derived subgroup of the fixed points modulo its centre, is
the projective symplectic group `PSp₄(𝔽_q) = Sp₄(𝔽_q) ⧸ Z(Sp₄(𝔽_q))`. That is
`TauCeti.TypeB2LieIndex.projectiveSymplecticEquivGroup`. It is simple by Iwasawa's criterion
(`TauCeti.GLSymplecticFin.isSimpleGroup_quotient_center`), so every `B₂(q)` on
the classification list is simple, read both on the type-`B` index and on the assembled carrier
`TauCeti.ValidLieTypeIndex.Group`.

## Main definitions and results

* `TauCeti.TypeB2LieIndex.symplecticEquivFixedPoints`: the Steinberg fixed points of `B₂(q)` are
  the finite symplectic group `Sp₄(𝔽_q)`.
* `TauCeti.TypeB2LieIndex.carrierEquivSymplectic_spinEquivCarrier_symplecticEquivFixedPoints`: read
  in `Sp₄` over the closure, the fixed point attached to a finite-field matrix is that matrix.
* `TauCeti.TypeB2LieIndex.commutator_symplectic_eq_top`: `Sp₄(𝔽_q)` is perfect.
* `TauCeti.TypeB2LieIndex.projectiveSymplecticEquivGroup`: the group attached to `B₂(q)` is
  `PSp₄(𝔽_q)`.
* `TauCeti.TypeB2LieIndex.isSimpleGroup_group` and `TauCeti.ValidLieTypeIndex.isSimpleGroup_B_two`:
  the group attached to `B₂(q)` is simple.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§1.2, 11.3 and 14.1.
* D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*,
  Number 1, §2.2, for the exclusion of `B₂(2)` and `B₂(3)`.

The organization follows `TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TypeC`, the same
transport for the type-`C` family.
-/

public section

noncomputable section

namespace TauCeti.TypeB2LieIndex

variable (d : TypeB2LieIndex)

/-- The composite identification of the spin carrier of `B₂(q)` with `Sp₄` over the closure
carries the Steinberg map to the entrywise `q`-power Frobenius. -/
private theorem comp_steinberg :
    ((d.spinEquivCarrier.trans d.1.carrierEquivSymplectic :
        d.toTypeBLieIndex.AmbientGroup ≃* d.1.StandardGroup) :
        d.toTypeBLieIndex.AmbientGroup →* d.1.StandardGroup).comp d.toTypeBLieIndex.steinberg =
      (GLSymplecticFin.map 2 d.1.1.Closure
          (iterateFrobenius d.1.1.Closure d.1.1.characteristic d.1.1.fieldExponent)).comp
        (d.spinEquivCarrier.trans d.1.carrierEquivSymplectic :
          d.toTypeBLieIndex.AmbientGroup →* d.1.StandardGroup) :=
  MonoidHom.ext fun g => by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.coe_ofClass, MulEquiv.trans_apply,
      TypeBLieIndex.steinberg_def, spinEquivCarrier_frobenius,
      RankTwoBLieIndex.carrierEquivSymplectic_frobenius, RankTwoBLieIndex.symplecticFrobenius_def,
      MulEquiv.trans_apply]

/-- **The Steinberg fixed points of `B₂(q)` are the finite symplectic group `Sp₄(𝔽_q)`.**

The spin carrier of `B₂(q)` is identified with `Sp₄` over the closure, intertwining the Steinberg
map with the entrywise `q`-power Frobenius, so the identification carries one fixed subgroup onto
the other; the fixed subgroup of that Frobenius is the finite symplectic group by the coefficient
identification. -/
def symplecticEquivFixedPoints :
    GLSymplecticFin 2 (GaloisField d.1.1.characteristic d.1.1.fieldExponent) ≃*
      d.toTypeBLieIndex.FixedPoints :=
  (ValidLieTypeIndex.symplecticEquivFrobeniusFixedPoints d.1.1 2).trans
    (fixedSubgroupCongr (d.spinEquivCarrier.trans d.1.carrierEquivSymplectic)
      d.comp_steinberg).symm

/-- **The fixed point of `B₂(q)` attached to a finite-field symplectic matrix is that matrix**,
once the spin carrier is read as `Sp₄` over the closure: its image under the carrier
identifications is the matrix with its coefficients extended to the closure. -/
@[simp]
theorem carrierEquivSymplectic_spinEquivCarrier_symplecticEquivFixedPoints
    (g : GLSymplecticFin 2 (GaloisField d.1.1.characteristic d.1.1.fieldExponent)) :
    d.1.carrierEquivSymplectic (d.spinEquivCarrier (d.symplecticEquivFixedPoints g)) =
      GLSymplecticFin.map 2 _ d.1.1.galoisFieldEmbedding g := by
  rw [symplecticEquivFixedPoints, MulEquiv.trans_apply, coe_fixedSubgroupCongr_symm_apply,
    ← MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  exact Subtype.ext (Units.ext (by
    rw [ValidLieTypeIndex.coe_symplecticEquivFrobeniusFixedPoints, GLSymplecticFin.coe_map]))

/-- **The finite symplectic group of `B₂(q)` is perfect.** A valid `B₂(q)` has `q ≥ 4`, and
`Sp₄(𝔽_q)` is perfect as soon as `𝔽_q` has an element other than `0` and `1`. -/
theorem commutator_symplectic_eq_top :
    commutator (GLSymplecticFin 2 (GaloisField d.1.1.characteristic d.1.1.fieldExponent)) = ⊤ :=
  GLSymplecticFin.commutator_eq_top_of_two_le le_rfl <| .inr <| Cardinal.exists_ne_ne_of_three_le
    (by
      rw [← Nat.cast_card, GaloisField.card _ _ d.1.1.fieldExponent_pos.ne',
        ← ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
      exact_mod_cast (by have := d.four_le_fieldOrder; omega)) 0 1

/-- **The group attached to `B₂(q)` is the projective symplectic group `PSp₄(𝔽_q)`.**

The fixed points are `Sp₄(𝔽_q)` by `TauCeti.TypeB2LieIndex.symplecticEquivFixedPoints`. That group
is perfect, so its derived subgroup is the whole group and the derived central quotient is its
quotient by the centre. -/
def projectiveSymplecticEquivGroup :
    GLSymplecticFin 2 (GaloisField d.1.1.characteristic d.1.1.fieldExponent) ⧸
        Subgroup.center (GLSymplecticFin 2 (GaloisField d.1.1.characteristic d.1.1.fieldExponent))
      ≃* d.toTypeBLieIndex.Group :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect d.commutator_symplectic_eq_top
    d.symplecticEquivFixedPoints

/-- The isomorphism with `PSp₄(𝔽_q)` sends the class of a matrix in the derived subgroup to the
class of the corresponding fixed point. -/
@[simp]
theorem projectiveSymplecticEquivGroup_mk
    (x : commutator (GLSymplecticFin 2 (GaloisField d.1.1.characteristic d.1.1.fieldExponent))) :
    d.projectiveSymplecticEquivGroup (QuotientGroup.mk (s := Subgroup.center _)
        (x : GLSymplecticFin 2 (GaloisField d.1.1.characteristic d.1.1.fieldExponent))) =
      ((MulEquiv.commutatorCongr d.symplecticEquivFixedPoints x :
          commutator d.toTypeBLieIndex.FixedPoints) : d.toTypeBLieIndex.Group) :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect_mk _ _ x

/-- **The group attached to `B₂(q)` is simple**, for every valid index: it is `PSp₄(𝔽_q)`, which is
simple by Iwasawa's criterion because `Sp₄(𝔽_q)` is perfect. -/
theorem isSimpleGroup_group : IsSimpleGroup d.toTypeBLieIndex.Group :=
  have := GLSymplecticFin.isSimpleGroup_quotient_center
    d.commutator_symplectic_eq_top
  d.projectiveSymplecticEquivGroup.symm.isSimpleGroup

end TauCeti.TypeB2LieIndex

namespace TauCeti.ValidLieTypeIndex

/-- **Every `B₂(q)` on the classification list is simple.** On the constructor `B 2 q` the
Steinberg endomorphism of the assembly is that of the type-`B` family, so the assembled candidate
is the one of `TauCeti.TypeB2LieIndex.of q hv`. -/
theorem isSimpleGroup_B_two {q : PrimePower} (hv : (LieTypeIndex.B 2 q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_B, GraphTwistedIndex.steinberg_B]
  exact (TypeB2LieIndex.of q hv).isSimpleGroup_group

end TauCeti.ValidLieTypeIndex

end
