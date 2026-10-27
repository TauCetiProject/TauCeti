/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialLinearFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement

/-!
# Finiteness of the type-`A` groups on the classification list

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
Nothing here asserts that the quotient is nontrivial or simple, and no order is computed.

## Main definitions and results

* `TauCeti.TypeALieIndex.specialLinearEquivFixedPoints`: the fixed points of the Steinberg map
  of `A_r(q)` are the finite special linear group `SL_{r+1}(𝔽_q)`.
* `TauCeti.TypeALieIndex.finite_fixedPoints_ofA` and `TauCeti.TypeALieIndex.finite_group_ofA`: the
  fixed points and the derived central quotient of `A_r(q)` are finite.

## Provenance

This file adapts `CFSG/TypeALinearCandidate.lean` from
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

end TauCeti.TypeALieIndex

end
