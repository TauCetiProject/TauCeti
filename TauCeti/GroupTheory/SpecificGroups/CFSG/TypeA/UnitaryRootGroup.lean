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
Thus the inherited multiplication and central commutator formulas describe an actual root
subgroup, rather than an abstract group with no comparison to the fixed-point carrier.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.ValidLieTypeIndex

variable (d : ValidLieTypeIndex)

/-- The upper unitriangular twisted root group in the finite special unitary model of `SU₃(q)`.
Its parameters satisfy trace equal to norm over the quadratic extension. -/
def unitaryRootHom :
    HeisenbergGroup.unitarySubgroup
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
          d.characteristic d.fieldExponent) involutive_iterateFrobenius_galoisField →*
      fixedSubgroup (d.galoisFieldTwistedFrobenius 2) :=
  (HeisenbergGroup.toSpecialLinear.comp
    (HeisenbergGroup.unitarySubgroup _ involutive_iterateFrobenius_galoisField).subtype).codRestrict
      (fixedSubgroup (d.galoisFieldTwistedFrobenius 2)) fun a ↦ by
        rw [mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff]
        rw [typeAGraphConjugator_two, MonoidHom.comp_apply, HeisenbergGroup.coe_toSpecialLinear,
          ← coe_iterateFrobenius_galoisField]
        exact (HeisenbergGroup.transpose_map_toMatrix_mul_form_iff _
          involutive_iterateFrobenius_galoisField (a : HeisenbergGroup
            (GaloisField d.characteristic (d.fieldExponent * 2)))).mpr a.property

/-- The root homomorphism has the standard upper unitriangular matrix. -/
@[simp]
theorem coe_unitaryRootHom (a : HeisenbergGroup.unitarySubgroup
    (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
      d.characteristic d.fieldExponent) involutive_iterateFrobenius_galoisField) :
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

/-- An upper unitriangular matrix of the finite special unitary group is in the root group.
The unitary equations force the two Heisenberg coordinate relations. -/
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
    have h := (mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff 2
      (g : SpecialLinearGroup (Fin 3)
        (GaloisField d.characteristic (d.fieldExponent * 2)))).mp g.property
    rw [ha, ← coe_iterateFrobenius_galoisField] at h
    rw [typeAGraphConjugator_two] at h
    have ha' := (HeisenbergGroup.transpose_map_toMatrix_mul_form_iff _
      involutive_iterateFrobenius_galoisField a).mp h
    refine ⟨⟨a, ha'⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_unitaryRootHom]
    exact ha.symm

end TauCeti.ValidLieTypeIndex

namespace TauCeti.TypeALieIndex

/-- The twisted upper root group as a subgroup of the actual Steinberg fixed points of `²A₂(q)`.
The map uses the proved finite-field/carrier descent, not an identification by group name. -/
def unitaryRootHom (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid) :
    HeisenbergGroup.unitarySubgroup
        (iterateFrobenius (GaloisField (ofTwistedA 2 q hv).1.characteristic
          ((ofTwistedA 2 q hv).1.fieldExponent * 2)) (ofTwistedA 2 q hv).1.characteristic
          (ofTwistedA 2 q hv).1.fieldExponent)
          ValidLieTypeIndex.involutive_iterateFrobenius_galoisField →*
      (ofTwistedA 2 q hv).FixedPoints :=
  (specialUnitaryEquivFixedPoints 2 q hv).toMonoidHom.comp (ofTwistedA 2 q hv).1.unitaryRootHom

/-- The root embedding is finite-field descent applied to the finite unitary root matrix. -/
theorem unitaryRootHom_apply (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (a : HeisenbergGroup.unitarySubgroup
      (iterateFrobenius (GaloisField (ofTwistedA 2 q hv).1.characteristic
        ((ofTwistedA 2 q hv).1.fieldExponent * 2)) (ofTwistedA 2 q hv).1.characteristic
        (ofTwistedA 2 q hv).1.fieldExponent)
          ValidLieTypeIndex.involutive_iterateFrobenius_galoisField) :
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
        (ofTwistedA 2 q hv).1.fieldExponent)
          ValidLieTypeIndex.involutive_iterateFrobenius_galoisField) :
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
