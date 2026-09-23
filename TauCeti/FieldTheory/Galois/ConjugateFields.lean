/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Conjugates
public import TauCeti.FieldTheory.Galois.FixedField

/-!
# Conjugate intermediate fields

The automorphism group of an extension acts on its intermediate fields by mapping their
elements.  For a finite Galois extension, the Galois correspondence intertwines this action
with conjugation of fixing subgroups.  Consequently the conjugates of an intermediate field
correspond bijectively to the conjugates of its fixing subgroup, and their number is the index
of the subgroup's normalizer.

This distinguishes two quotients attached to an intermediate field `E`.  Its embeddings into
the ambient Galois extension are indexed by the cosets of `E.fixingSubgroup`, whereas the
distinct images of those embeddings are indexed by the cosets of
`E.fixingSubgroup.normalizer`.  The latter quotient can be strictly smaller.

## Main definitions

* `TauCeti.conjugateFields`: the orbit of an intermediate field under ambient automorphisms.
* `TauCeti.conjugateFieldsEquivConjugateSubgroups`: the Galois-correspondence bijection between
  those two sets.

## Main results

* `TauCeti.stabilizer_intermediateField_eq_normalizer`: the stabilizer of an intermediate field
  is the normalizer of its fixing subgroup.
* `TauCeti.ncard_conjugateFields`: the number of conjugate fields is the normalizer index.
-/

public section

namespace TauCeti

open IntermediateField MulAction
open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The action of the automorphism group of `L / K` on its intermediate fields. -/
instance instMulActionIntermediateField : MulAction (L ≃ₐ[K] L) (IntermediateField K L) where
  smul σ E := E.map σ.toAlgHom
  one_smul E := by
    change E.map (AlgHom.id K L) = E
    exact E.map_id
  mul_smul σ τ E := by
    change E.map (σ * τ).toAlgHom = (E.map τ.toAlgHom).map σ.toAlgHom
    rw [IntermediateField.map_map]
    congr 1

/-- Conjugating an intermediate field means mapping it along the automorphism. -/
@[simp]
theorem smul_intermediateField_def (σ : L ≃ₐ[K] L) (E : IntermediateField K L) :
    σ • E = E.map σ.toAlgHom :=
  (rfl)

/-- The set of images of `E` under automorphisms of the ambient extension. -/
def conjugateFields (E : IntermediateField K L) : Set (IntermediateField K L) :=
  orbit (L ≃ₐ[K] L) E

/-- Membership in `conjugateFields E` means being the image of `E` under an automorphism. -/
theorem mem_conjugateFields_iff {E E' : IntermediateField K L} :
    E' ∈ conjugateFields E ↔ ∃ σ : L ≃ₐ[K] L, E.map σ.toAlgHom = E' := by
  simp [conjugateFields, mem_orbit_iff, eq_comm]

section Galois

variable [FiniteDimensional K L] [IsGalois K L]

/-- The stabilizer of an intermediate field under ambient automorphisms is the normalizer of
its fixing subgroup. -/
theorem stabilizer_intermediateField_eq_normalizer (E : IntermediateField K L) :
    stabilizer (L ≃ₐ[K] L) E =
      Subgroup.normalizer (E.fixingSubgroup : Set (L ≃ₐ[K] L)) := by
  ext σ
  rw [mem_stabilizer_iff, Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    calc
      E.fixingSubgroup.map (MulAut.conj σ) = (σ • E).fixingSubgroup := by
        rw [smul_intermediateField_def, IsGalois.map_fixingSubgroup]
        congr 1
      _ = E.fixingSubgroup := congrArg IntermediateField.fixingSubgroup h
  · intro h
    rw [← IsGalois.fixedField_fixingSubgroup (σ • E), smul_intermediateField_def,
      IsGalois.map_fixingSubgroup]
    convert congrArg fixedField h using 1 <;> congr 1
    exact (IsGalois.fixedField_fixingSubgroup E).symm

/-- The Galois correspondence restricts to a bijection from conjugates of an intermediate
field to conjugates of its fixing subgroup. -/
noncomputable def conjugateFieldsEquivConjugateSubgroups (E : IntermediateField K L) :
    conjugateFields E ≃ MulAction.orbit (ConjAct (L ≃ₐ[K] L)) E.fixingSubgroup where
  toFun E' := ⟨E'.1.fixingSubgroup, by
    obtain ⟨σ, hσ⟩ := mem_conjugateFields_iff.mp E'.2
    refine mem_conjugateSubgroups_iff.mpr ⟨σ, ?_⟩
    calc
      E.fixingSubgroup.map (MulAut.conj σ) = (E.map σ.toAlgHom).fixingSubgroup := by
        rw [IsGalois.map_fixingSubgroup]
        congr 1
      _ = E'.1.fixingSubgroup := congrArg IntermediateField.fixingSubgroup hσ⟩
  invFun H := ⟨fixedField H.1, by
    obtain ⟨σ, hσ⟩ := mem_conjugateSubgroups_iff.mp H.2
    apply mem_conjugateFields_iff.mpr
    refine ⟨σ, ?_⟩
    calc
      E.map σ.toAlgHom = σ • E := rfl
      _ = fixedField (E.fixingSubgroup.map (MulAut.conj σ)) := by
        simp only [Subgroup.fixedField_map_conj, IsGalois.fixedField_fixingSubgroup,
          smul_intermediateField_def]
      _ = fixedField H.1 := congrArg fixedField hσ
      _ = _ := rfl⟩
  left_inv E' := Subtype.ext (IsGalois.fixedField_fixingSubgroup E'.1)
  right_inv H := Subtype.ext (IntermediateField.fixingSubgroup_fixedField H.1)

/-- The number of distinct conjugates of an intermediate field is the index of the normalizer
of its fixing subgroup. -/
theorem ncard_conjugateFields (E : IntermediateField K L) :
    (conjugateFields E).ncard =
      (Subgroup.normalizer (E.fixingSubgroup : Set (L ≃ₐ[K] L))).index := by
  rw [conjugateFields, ← MulAction.index_stabilizer,
    stabilizer_intermediateField_eq_normalizer]

end Galois

end TauCeti
