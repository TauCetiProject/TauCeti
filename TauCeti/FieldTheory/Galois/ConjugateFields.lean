/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Conjugates
public import TauCeti.FieldTheory.Galois.FixedField
public import TauCeti.FieldTheory.IntermediateField.ConjugateFields

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

* `IntermediateField.conjugateFieldsEquivConjugateSubgroups`: the Galois-correspondence
  bijection between those two sets.
* `IntermediateField.quotientNormalizerEquivConjugateFields`: normalizer cosets index the
  conjugate fields.

## Main results

* `IntermediateField.stabilizer_eq_normalizer_fixingSubgroup`: the field stabilizer is the
  normalizer of its fixing subgroup.
* `IntermediateField.ncard_conjugateFields`: the number of fields is the normalizer index.
-/

public section

open IntermediateField MulAction
open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace IntermediateField

section Galois

variable [FiniteDimensional K L] [IsGalois K L]

/-- The stabilizer of an intermediate field under ambient automorphisms is the normalizer of
its fixing subgroup. -/
@[simp]
theorem stabilizer_eq_normalizer_fixingSubgroup (E : IntermediateField K L) :
    stabilizer (L ≃ₐ[K] L) E =
      Subgroup.normalizer (E.fixingSubgroup : Set (L ≃ₐ[K] L)) := by
  ext σ
  rw [mem_stabilizer_iff, Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    calc
      E.fixingSubgroup.map (MulAut.conj σ) = (σ • E).fixingSubgroup := by
        rw [AlgEquiv.smul_intermediateField_def, IsGalois.map_fixingSubgroup]
        congr 1
      _ = E.fixingSubgroup := congrArg IntermediateField.fixingSubgroup h
  · intro h
    rw [← IsGalois.fixedField_fixingSubgroup (σ • E), AlgEquiv.smul_intermediateField_def,
      IsGalois.map_fixingSubgroup]
    convert congrArg fixedField h using 1 <;> congr 1
    exact (IsGalois.fixedField_fixingSubgroup E).symm

/-- The Galois correspondence restricts to a bijection from conjugates of an intermediate
field to conjugates of its fixing subgroup. -/
noncomputable def conjugateFieldsEquivConjugateSubgroups (E : IntermediateField K L) :
    conjugateFields E ≃ MulAction.orbit (ConjAct (L ≃ₐ[K] L)) E.fixingSubgroup where
  toFun E' := ⟨E'.1.fixingSubgroup, by
    obtain ⟨σ, hσ⟩ := mem_conjugateFields_iff.mp E'.2
    refine TauCeti.mem_orbit_conjAct_iff.mpr ⟨σ, ?_⟩
    calc
      E.fixingSubgroup.map (MulAut.conj σ) = (E.map σ.toAlgHom).fixingSubgroup := by
        rw [IsGalois.map_fixingSubgroup]
        congr 1
      _ = E'.1.fixingSubgroup := congrArg IntermediateField.fixingSubgroup hσ⟩
  invFun H := ⟨fixedField H.1, by
    obtain ⟨σ, hσ⟩ := TauCeti.mem_orbit_conjAct_iff.mp H.2
    apply mem_conjugateFields_iff.mpr
    refine ⟨σ, ?_⟩
    calc
      E.map σ.toAlgHom = σ • E := (AlgEquiv.smul_intermediateField_def σ E).symm
      _ = fixedField (E.fixingSubgroup.map (MulAut.conj σ)) := by
        simp only [Subgroup.fixedField_map_conj, IsGalois.fixedField_fixingSubgroup,
          AlgEquiv.smul_intermediateField_def]
      _ = fixedField H.1 := congrArg fixedField hσ
      _ = _ := rfl⟩
  left_inv E' := Subtype.ext (IsGalois.fixedField_fixingSubgroup E'.1)
  right_inv H := Subtype.ext (IntermediateField.fixingSubgroup_fixedField H.1)

/-- The forward Galois correspondence sends a conjugate field to its fixing subgroup. -/
@[simp]
theorem conjugateFieldsEquivConjugateSubgroups_apply (E : IntermediateField K L)
    (E' : conjugateFields E) :
    (conjugateFieldsEquivConjugateSubgroups E E').1 = E'.1.fixingSubgroup := by
  simp [conjugateFieldsEquivConjugateSubgroups]

/-- The inverse Galois correspondence sends a conjugate subgroup to its fixed field. -/
@[simp]
theorem conjugateFieldsEquivConjugateSubgroups_symm_apply (E : IntermediateField K L)
    (H : MulAction.orbit (ConjAct (L ≃ₐ[K] L)) E.fixingSubgroup) :
    ((conjugateFieldsEquivConjugateSubgroups E).symm H).1 = fixedField H.1 := by
  simp [conjugateFieldsEquivConjugateSubgroups]

/-- The normalizer cosets index the conjugate images of an intermediate field. -/
noncomputable def quotientNormalizerEquivConjugateFields (E : IntermediateField K L) :
    (L ≃ₐ[K] L) ⧸ Subgroup.normalizer (E.fixingSubgroup : Set (L ≃ₐ[K] L)) ≃
      conjugateFields E :=
  (Subgroup.quotientEquivOfEq (stabilizer_eq_normalizer_fixingSubgroup E).symm).trans
    ((MulAction.orbitEquivQuotientStabilizer (L ≃ₐ[K] L) E).symm.trans
      (Equiv.subtypeEquivRight fun E' ↦ by
        simp only [mem_orbit_iff, AlgEquiv.smul_intermediateField_def,
          mem_conjugateFields_iff]))

/-- A normalizer coset represented by `σ` gives the field `σ • E`. -/
@[simp]
theorem quotientNormalizerEquivConjugateFields_mk (E : IntermediateField K L)
    (σ : L ≃ₐ[K] L) :
    ((quotientNormalizerEquivConjugateFields E) (QuotientGroup.mk σ)).1 = σ • E := by
  simp only [quotientNormalizerEquivConjugateFields, Equiv.trans_apply,
    Subgroup.quotientEquivOfEq_mk, Equiv.subtypeEquivRight_apply,
    MulAction.orbitEquivQuotientStabilizer_symm_apply]

/-- The normalizer-coset parametrization respects the ambient Galois action. -/
@[simp]
theorem quotientNormalizerEquivConjugateFields_smul (E : IntermediateField K L)
    (σ : L ≃ₐ[K] L)
    (q : (L ≃ₐ[K] L) ⧸ Subgroup.normalizer (E.fixingSubgroup : Set (L ≃ₐ[K] L))) :
    (quotientNormalizerEquivConjugateFields E (σ • q)).1 =
      σ • (quotientNormalizerEquivConjugateFields E q).1 := by
  induction q using Quotient.inductionOn' with
  | _ τ => simp [mul_smul]

/-- The number of distinct conjugates of an intermediate field is the index of the normalizer
of its fixing subgroup. -/
@[simp]
theorem ncard_conjugateFields (E : IntermediateField K L) :
    (conjugateFields E).ncard =
      (Subgroup.normalizer (E.fixingSubgroup : Set (L ≃ₐ[K] L))).index := by
  have hcard : (conjugateFields E).ncard =
      (MulAction.orbit (L ≃ₐ[K] L) E).ncard := by
    congr 1
    ext E'
    simp only [mem_conjugateFields_iff, mem_orbit_iff,
      AlgEquiv.smul_intermediateField_def]
  rw [hcard, ← MulAction.index_stabilizer,
    stabilizer_eq_normalizer_fixingSubgroup]

end Galois

end IntermediateField
