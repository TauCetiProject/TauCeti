/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Unitary
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic

/-!
# The twisted root group of `SU₃(q)` in the Steinberg fixed points

The upper unitriangular root group of `SU₃(q)` has matrices
`!![1, x, z; 0, 1, x^q; 0, 0, 1]` with `z + z^q = x x^q`.
We embed the corresponding unitary subgroup of the Heisenberg group into the finite
special unitary model and then into the actual Steinberg fixed points of `²A₂(q)`.
The embedding is injective and retains the matrix coordinates under finite-field descent.
The inherited multiplication and central commutator formulas describe this root subgroup.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.ValidLieTypeIndex

variable (d : ValidLieTypeIndex)

/-- A Heisenberg matrix is fixed by the graph-twisted Frobenius exactly when it belongs to
the unitary root subgroup. -/
theorem heisenbergGroup_toSpecialLinear_mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff
    (a : HeisenbergGroup (GaloisField d.characteristic (d.fieldExponent * 2))) :
    HeisenbergGroup.toSpecialLinear a ∈ fixedSubgroup (d.galoisFieldTwistedFrobenius 2) ↔
      a ∈ HeisenbergGroup.unitarySubgroup
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
          d.characteristic d.fieldExponent) := by
  rw [fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup,
    coe_typeAGraphConjugator_two, Matrix.mem_specialIsometryGroup_iff,
    HeisenbergGroup.coe_toSpecialLinear,
    ← HeisenbergGroup.mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq]

/-- The embedding of the unitary Heisenberg root subgroup into the finite special unitary
model `SU₃(q)` by its upper unitriangular matrix. -/
def rankTwoUpperUnitaryRootHom :
    HeisenbergGroup.unitarySubgroup
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
          d.characteristic d.fieldExponent) →*
      fixedSubgroup (d.galoisFieldTwistedFrobenius 2) :=
  (HeisenbergGroup.toSpecialLinear.comp
    (HeisenbergGroup.unitarySubgroup _).subtype).codRestrict
      (fixedSubgroup (d.galoisFieldTwistedFrobenius 2)) fun a ↦ by
        simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using
          (d.heisenbergGroup_toSpecialLinear_mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff
            a).mpr a.property

/-- The root homomorphism is the standard upper unitriangular special linear matrix. -/
@[simp]
theorem coe_rankTwoUpperUnitaryRootHom (a : HeisenbergGroup.unitarySubgroup
    (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
      d.characteristic d.fieldExponent)) :
    (d.rankTwoUpperUnitaryRootHom a : SpecialLinearGroup (Fin 3)
        (GaloisField d.characteristic (d.fieldExponent * 2))) =
      HeisenbergGroup.toSpecialLinear a := (rfl)

/-- No two root parameters give the same unitary matrix. -/
theorem rankTwoUpperUnitaryRootHom_injective :
    Function.Injective d.rankTwoUpperUnitaryRootHom := by
  intro a b h
  apply Subtype.ext
  apply HeisenbergGroup.toSpecialLinear_injective
  exact congrArg Subtype.val h

/-- An element of the finite special unitary group lies in the range of the rank-two upper
root embedding exactly when its matrix is upper unitriangular. -/
theorem mem_range_rankTwoUpperUnitaryRootHom_iff
    (g : fixedSubgroup (d.galoisFieldTwistedFrobenius 2)) :
    g ∈ d.rankTwoUpperUnitaryRootHom.range ↔
      ((g : SpecialLinearGroup (Fin 3)
        (GaloisField d.characteristic (d.fieldExponent * 2))) : Matrix (Fin 3) (Fin 3)
          (GaloisField d.characteristic (d.fieldExponent * 2))).IsUpperUnitriangular := by
  rw [← HeisenbergGroup.mem_range_toSpecialLinear_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, hga⟩
    have ha' :=
      (d.heisenbergGroup_toSpecialLinear_mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff a).mp
        (hga.symm ▸ g.property)
    exact ⟨⟨a, ha'⟩, Subtype.ext hga⟩

end TauCeti.ValidLieTypeIndex

namespace TauCeti.TypeALieIndex

/-- The injective embedding of the unitary root group into the Steinberg fixed points of
`²A₂(q)`, via finite-field descent. -/
def rankTwoUpperUnitaryRootHom (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    HeisenbergGroup.unitarySubgroup
        (iterateFrobenius (GaloisField (ofTwistedA 2 q hv).1.characteristic
          ((ofTwistedA 2 q hv).1.fieldExponent * 2)) (ofTwistedA 2 q hv).1.characteristic
          (ofTwistedA 2 q hv).1.fieldExponent) →*
      (ofTwistedA 2 q hv).FixedPoints :=
  -- The abbreviation ofTwistedA makes its rank definitionally 2, so the descent domain
  -- indexed by Fin (rank + 1) agrees with the root homomorphism's Fin 3 matrix carrier.
  (specialUnitaryEquivFixedPoints 2 q hv).toMonoidHom.comp
    (ofTwistedA 2 q hv).1.rankTwoUpperUnitaryRootHom

/-- The rank-two upper root embedding is the composition with finite-field descent. -/
theorem rankTwoUpperUnitaryRootHom_def (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    rankTwoUpperUnitaryRootHom q hv =
      (specialUnitaryEquivFixedPoints 2 q hv).toMonoidHom.comp
        (ofTwistedA 2 q hv).1.rankTwoUpperUnitaryRootHom := (rfl)

/-- The root embedding is finite-field descent applied to the finite unitary root matrix. -/
theorem rankTwoUpperUnitaryRootHom_apply (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (a : HeisenbergGroup.unitarySubgroup
      (iterateFrobenius (GaloisField (ofTwistedA 2 q hv).1.characteristic
        ((ofTwistedA 2 q hv).1.fieldExponent * 2)) (ofTwistedA 2 q hv).1.characteristic
        (ofTwistedA 2 q hv).1.fieldExponent)) :
    rankTwoUpperUnitaryRootHom q hv a =
      specialUnitaryEquivFixedPoints 2 q hv
        ((ofTwistedA 2 q hv).1.rankTwoUpperUnitaryRootHom a) := (rfl)

/-- In the standard matrix carrier over the closure, the root embedding is coefficient extension
of its upper unitriangular Heisenberg matrix. -/
@[simp]
theorem carrierEquivSpecialLinear_rankTwoUpperUnitaryRootHom (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (a : HeisenbergGroup.unitarySubgroup
      (iterateFrobenius (GaloisField (ofTwistedA 2 q hv).1.characteristic
        ((ofTwistedA 2 q hv).1.fieldExponent * 2)) (ofTwistedA 2 q hv).1.characteristic
        (ofTwistedA 2 q hv).1.fieldExponent)) :
    (ofTwistedA 2 q hv).carrierEquivSpecialLinear
        (rankTwoUpperUnitaryRootHom q hv a : (ofTwistedA 2 q hv).AmbientGroup) =
      HeisenbergGroup.toSpecialLinear (HeisenbergGroup.map
        ((ofTwistedA 2 q hv).1.extensionGaloisFieldEmbedding 2 two_ne_zero) a) := by
  rw [← HeisenbergGroup.map_toSpecialLinear, rankTwoUpperUnitaryRootHom_apply]
  apply Subtype.ext
  have h := coe_specialUnitaryEquivFixedPoints 2 q hv
    ((ofTwistedA 2 q hv).1.rankTwoUpperUnitaryRootHom a)
  simp only [ValidLieTypeIndex.coe_rankTwoUpperUnitaryRootHom,
    HeisenbergGroup.coe_toSpecialLinear] at h
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    HeisenbergGroup.coe_toSpecialLinear]
  -- Normalize the numeric rank in the dependent matrix indices of finite-field descent.
  convert! h using 1

/-- The root group embeds faithfully into the actual fixed points. -/
theorem rankTwoUpperUnitaryRootHom_injective (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    Function.Injective (rankTwoUpperUnitaryRootHom q hv) :=
  (specialUnitaryEquivFixedPoints 2 q hv).injective.comp
    (ofTwistedA 2 q hv).1.rankTwoUpperUnitaryRootHom_injective

end TauCeti.TypeALieIndex

end
