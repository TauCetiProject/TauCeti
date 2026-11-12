/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Unitary
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA

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
theorem toSpecialLinear_mem_fixedSubgroup_iff
    (a : HeisenbergGroup (GaloisField d.characteristic (d.fieldExponent * 2))) :
    HeisenbergGroup.toSpecialLinear a ∈ fixedSubgroup (d.galoisFieldTwistedFrobenius 2) ↔
      a ∈ HeisenbergGroup.unitarySubgroup
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
          d.characteristic d.fieldExponent) := by
  rw [fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup,
    typeAGraphConjugator_two, Matrix.mem_specialIsometryGroup_iff,
    HeisenbergGroup.coe_toSpecialLinear,
    ← HeisenbergGroup.mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq]

/-- The embedding of the unitary Heisenberg root subgroup into the finite special unitary
model `SU₃(q)` by its upper unitriangular matrix. -/
def unitaryRootHom :
    HeisenbergGroup.unitarySubgroup
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
          d.characteristic d.fieldExponent) →*
      fixedSubgroup (d.galoisFieldTwistedFrobenius 2) :=
  (HeisenbergGroup.toSpecialLinear.comp
    (HeisenbergGroup.unitarySubgroup _).subtype).codRestrict
      (fixedSubgroup (d.galoisFieldTwistedFrobenius 2)) fun a ↦ by
        simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using
          (d.toSpecialLinear_mem_fixedSubgroup_iff a).mpr a.property

/-- The root homomorphism has the standard upper unitriangular matrix. -/
@[simp]
theorem coe_unitaryRootHom (a : HeisenbergGroup.unitarySubgroup
    (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
      d.characteristic d.fieldExponent)) :
    ((d.unitaryRootHom a : SpecialLinearGroup (Fin 3)
        (GaloisField d.characteristic (d.fieldExponent * 2))) : Matrix (Fin 3) (Fin 3)
          (GaloisField d.characteristic (d.fieldExponent * 2))) =
      HeisenbergGroup.toMatrix (a : HeisenbergGroup
        (GaloisField d.characteristic (d.fieldExponent * 2))) := by
  simp [unitaryRootHom]

/-- No two root parameters give the same unitary matrix. -/
theorem unitaryRootHom_injective : Function.Injective d.unitaryRootHom := by
  intro a b h
  apply Subtype.ext
  apply HeisenbergGroup.toSpecialLinear_injective
  exact congrArg Subtype.val h

/-- An element of the finite special unitary group lies in the range of `unitaryRootHom`
exactly when its matrix is upper unitriangular. -/
theorem mem_range_unitaryRootHom_iff (g : fixedSubgroup (d.galoisFieldTwistedFrobenius 2)) :
    g ∈ d.unitaryRootHom.range ↔ ∃ a : HeisenbergGroup
        (GaloisField d.characteristic (d.fieldExponent * 2)),
      ((g : SpecialLinearGroup (Fin 3)
        (GaloisField d.characteristic (d.fieldExponent * 2))) : Matrix (Fin 3) (Fin 3)
          (GaloisField d.characteristic (d.fieldExponent * 2))) =
        HeisenbergGroup.toMatrix a := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, d.coe_unitaryRootHom a⟩
  · rintro ⟨a, ha⟩
    have hga : HeisenbergGroup.toSpecialLinear a = g.val :=
      Subtype.ext (by simpa using ha.symm)
    have ha' := (d.toSpecialLinear_mem_fixedSubgroup_iff a).mp (hga.symm ▸ g.property)
    refine ⟨⟨a, ha'⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_unitaryRootHom]
    exact ha.symm

end TauCeti.ValidLieTypeIndex

namespace TauCeti.TypeALieIndex

/-- The injective embedding of the unitary root group into the Steinberg fixed points of
`²A₂(q)`, via finite-field descent. -/
def unitaryRootHom (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    HeisenbergGroup.unitarySubgroup
        (iterateFrobenius (GaloisField (ofTwistedA 2 q hv).1.characteristic
          ((ofTwistedA 2 q hv).1.fieldExponent * 2)) (ofTwistedA 2 q hv).1.characteristic
          (ofTwistedA 2 q hv).1.fieldExponent) →*
      (ofTwistedA 2 q hv).FixedPoints :=
  -- The abbreviation ofTwistedA makes its rank definitionally 2, so the descent domain
  -- indexed by Fin (rank + 1) agrees with the root homomorphism's Fin 3 matrix carrier.
  (specialUnitaryEquivFixedPoints 2 q hv).toMonoidHom.comp (ofTwistedA 2 q hv).1.unitaryRootHom

/-- The root embedding is finite-field descent applied to the finite unitary root matrix. -/
theorem unitaryRootHom_apply (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (a : HeisenbergGroup.unitarySubgroup
      (iterateFrobenius (GaloisField (ofTwistedA 2 q hv).1.characteristic
        ((ofTwistedA 2 q hv).1.fieldExponent * 2)) (ofTwistedA 2 q hv).1.characteristic
        (ofTwistedA 2 q hv).1.fieldExponent)) :
    unitaryRootHom q hv a =
      specialUnitaryEquivFixedPoints 2 q hv ((ofTwistedA 2 q hv).1.unitaryRootHom a) := (rfl)

/-- In the standard matrix carrier over the closure, the root embedding is coefficient extension
of its upper unitriangular Heisenberg matrix. -/
@[simp]
theorem carrierEquivSpecialLinear_unitaryRootHom (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (a : HeisenbergGroup.unitarySubgroup
      (iterateFrobenius (GaloisField (ofTwistedA 2 q hv).1.characteristic
        ((ofTwistedA 2 q hv).1.fieldExponent * 2)) (ofTwistedA 2 q hv).1.characteristic
        (ofTwistedA 2 q hv).1.fieldExponent)) :
    (ofTwistedA 2 q hv).carrierEquivSpecialLinear
        (unitaryRootHom q hv a : (ofTwistedA 2 q hv).AmbientGroup) =
      SpecialLinearGroup.map
        ((ofTwistedA 2 q hv).1.extensionGaloisFieldEmbedding 2 two_ne_zero)
        (HeisenbergGroup.toSpecialLinear a) := by
  rw [unitaryRootHom_apply]
  apply Subtype.ext
  have h := coe_specialUnitaryEquivFixedPoints 2 q hv
    ((ofTwistedA 2 q hv).1.unitaryRootHom a)
  rw [ValidLieTypeIndex.coe_unitaryRootHom] at h
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    HeisenbergGroup.coe_toSpecialLinear]
  -- Normalize the numeric rank in the dependent matrix indices of finite-field descent.
  convert! h using 1

/-- The root group embeds faithfully into the actual fixed points. -/
theorem unitaryRootHom_injective (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    Function.Injective (unitaryRootHom q hv) :=
  (specialUnitaryEquivFixedPoints 2 q hv).injective.comp
    (ofTwistedA 2 q hv).1.unitaryRootHom_injective

end TauCeti.TypeALieIndex

end
