/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialUnitaryFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement

/-!
# The Steinberg fixed points of the unitary groups on the classification list

The carrier of the graph-twisted type-`A` index `²A_r(q)` is the explicit full-weight Chevalley
carrier, which `TauCeti.TypeALieIndex.carrierEquivSpecialLinear` identifies with `SL_{r+1}` over
the algebraic closure of the prime field. Under that identification the Steinberg map of the index
becomes `g ↦ θ (g ^ (q))`, with `θ` the signed reverse-inverse-transpose automorphism
(`TauCeti.TypeALieIndex.specialLinearSteinberg_ofTwistedA`).

This file transports the fixed points of the Steinberg map along that identification, and then
along `TauCeti.ValidLieTypeIndex.specialUnitaryEquivFrobeniusFixedPoints`, which identifies the
fixed points of `g ↦ θ (g ^ (q))` over the closure with those in `SL_{r+1}(𝔽_{q²})`. The
composite `TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints` is an isomorphism between the
finite special unitary group `SU_{r+1}(q)`, realized as the fixed subgroup of
`TauCeti.ValidLieTypeIndex.galoisFieldTwistedFrobenius`, and the fixed points
`TauCeti.TypeALieIndex.FixedPoints` of the index. By
`TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff`, that finite group is
the group of determinant-one isometries of the sesquilinear form on `𝔽_{q²} ^ (r + 1)` with the
signed reversal Gram matrix, so the candidate group `TauCeti.TypeALieIndex.Group` of the index is,
through `TauCeti.DerivedCentralQuotient.congr`, the derived subgroup of that special unitary group
modulo its centre. Nothing here asserts that this quotient is nontrivial or simple.

## Main definitions and results

* `TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints`: the Steinberg fixed points of `²A_r(q)`
  are the finite special unitary group, the fixed points of the graph-twisted Frobenius of
  `SL_{r+1}(𝔽_{q²})`.
* `TauCeti.TypeALieIndex.coe_specialUnitaryEquivFixedPoints`: the fixed point attached to a finite
  matrix is that matrix read over the closure.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), §§13.1 and 14.1.
-/

public section

noncomputable section

namespace TauCeti.TypeALieIndex

/-- The carrier equivalence of `²A_r(q)` intertwines the carrier Steinberg map with the
graph-twisted `q`-power Frobenius of `SL_{r+1}` over the closure. -/
private theorem carrierEquivSpecialLinear_comp_steinberg_ofTwistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    ((ofTwistedA r q hv).carrierEquivSpecialLinear :
        (ofTwistedA r q hv).AmbientGroup →* (ofTwistedA r q hv).StandardGroup).comp
        (ofTwistedA r q hv).steinberg =
      ((Matrix.SpecialLinearGroup.typeAGraphAutomorphism (ofTwistedA r q hv).1.rank
          (ofTwistedA r q hv).1.Closure : _ →* _).comp
        (Matrix.SpecialLinearGroup.map (n := Fin ((ofTwistedA r q hv).1.rank + 1))
          (iterateFrobenius (ofTwistedA r q hv).1.Closure
            (ofTwistedA r q hv).1.characteristic (ofTwistedA r q hv).1.fieldExponent))).comp
        ((ofTwistedA r q hv).carrierEquivSpecialLinear :
          (ofTwistedA r q hv).AmbientGroup →* (ofTwistedA r q hv).StandardGroup) := by
  rw [← specialLinearSteinberg_ofTwistedA]
  exact MonoidHom.ext fun g ↦ (ofTwistedA r q hv).carrierEquivSpecialLinear_steinberg g

/-- **The Steinberg fixed points of `²A_r(q)` are the finite special unitary group.** They are
isomorphic to the points of `SL_{r+1}(𝔽_{q²})` fixed by the graph-twisted `q`-power Frobenius,
which are the determinant-one isometries of the sesquilinear form with the signed reversal Gram
matrix. The isomorphism is the coefficient extension to the closure followed by the inverse of
the carrier equivalence. -/
def specialUnitaryEquivFixedPoints (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    fixedSubgroup ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank) ≃*
      (ofTwistedA r q hv).FixedPoints :=
  ((ofTwistedA r q hv).1.specialUnitaryEquivFrobeniusFixedPoints (ofTwistedA r q hv).1.rank).trans
    (fixedSubgroupCongr (ofTwistedA r q hv).carrierEquivSpecialLinear
      (carrierEquivSpecialLinear_comp_steinberg_ofTwistedA r q hv)).symm

/-- The isomorphism with the finite special unitary group sends a finite matrix to the fixed point
whose image under the carrier equivalence is that matrix read over the closure. -/
@[simp]
theorem coe_specialUnitaryEquivFixedPoints (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (g : fixedSubgroup
      ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank)) :
    ((ofTwistedA r q hv).carrierEquivSpecialLinear
        (specialUnitaryEquivFixedPoints r q hv g : (ofTwistedA r q hv).AmbientGroup) :
        Matrix (Fin ((ofTwistedA r q hv).1.rank + 1)) (Fin ((ofTwistedA r q hv).1.rank + 1))
          (ofTwistedA r q hv).1.Closure) =
      (g : Matrix (Fin ((ofTwistedA r q hv).1.rank + 1)) (Fin ((ofTwistedA r q hv).1.rank + 1))
          _).map ((ofTwistedA r q hv).1.extensionGaloisFieldEmbedding 2 two_ne_zero) := by
  rw [specialUnitaryEquivFixedPoints, MulEquiv.trans_apply, coe_fixedSubgroupCongr_symm_apply,
    MulEquiv.apply_symm_apply, ValidLieTypeIndex.coe_specialUnitaryEquivFrobeniusFixedPoints]

end TauCeti.TypeALieIndex

end
