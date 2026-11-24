/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Conjugates
public import TauCeti.FieldTheory.Galois.FixedField
public import TauCeti.FieldTheory.IntermediateField.ConjugateFields
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Conjugate intermediate fields

The automorphism group of an extension acts on its intermediate fields by mapping their
elements.  For a Galois extension, the Galois correspondence intertwines this action
with conjugation of fixing subgroups.  Consequently the conjugates of an intermediate field
correspond bijectively to the conjugates of its fixing subgroup, and their number is the index
of the subgroup's normalizer.

This distinguishes two quotients attached to an intermediate field `E`.  Its embeddings into
the ambient Galois extension are indexed by the cosets of `E.fixingSubgroup`, whereas the
distinct images of those embeddings are indexed by the cosets of
`E.fixingSubgroup.normalizer`.  The latter quotient can be strictly smaller.

Over a normal extension the conjugates of `E` are exactly the intermediate fields `K`-isomorphic
to `E`, because a `K`-isomorphism between intermediate fields extends to an automorphism of the
ambient field. Combined with the conjugation-equivariance of fixed fields, two finite subgroups of
the automorphism group have isomorphic fixed fields exactly when they are conjugate; abstractly
isomorphic subgroups need not have isomorphic fixed fields.

## Main definitions

* `IntermediateField.conjugateFieldsEquivConjugateSubgroups`: the Galois-correspondence
  bijection between those two sets.
* `IntermediateField.quotientNormalizerEquivConjugateFields`: normalizer cosets index the
  conjugate fields.

## Main results

* `IntermediateField.stabilizer_eq_normalizer_fixingSubgroup`: the field stabilizer is the
  normalizer of its fixing subgroup.
* `IntermediateField.ncard_conjugateFields`: the number of fields is the normalizer index.
* `IntermediateField.nonempty_algEquiv_iff_mem_conjugateFields`: over a normal extension, the
  intermediate fields isomorphic to `E` are its conjugates.
* `Subgroup.nonempty_fixedField_algEquiv_iff_exists_map_conj_eq`: two finite subgroups of the
  automorphism group of a normal extension have isomorphic fixed fields exactly when they are
  conjugate.
-/

public section

open IntermediateField MulAction
open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace IntermediateField

/-- **Isomorphic intermediate fields of a normal extension are conjugate.** Two intermediate
fields of a normal extension `L / K` are isomorphic as `K`-algebras exactly when an automorphism of
`L` carries one onto the other. Normality is used only for the forward direction, where it extends
a `K`-isomorphism `E ≃ₐ[K] E'` to an automorphism of `L`. -/
theorem nonempty_algEquiv_iff_mem_conjugateFields [Normal K L] {E E' : IntermediateField K L} :
    Nonempty (E ≃ₐ[K] E') ↔ E' ∈ conjugateFields E := by
  rw [mem_conjugateFields_iff]
  refine ⟨fun ⟨φ⟩ ↦ ⟨φ.liftNormal L, ?_⟩, fun ⟨σ, hσ⟩ ↦ ⟨(equivMap E σ).trans (equivOfEq hσ)⟩⟩
  -- The lift of `φ` to `L` agrees with `φ` on `E`, so it maps `E` onto `φ(E) = E'`.
  have hg (x : E) : φ.liftNormal L x = φ x := φ.liftNormal_commutes L x
  ext y
  refine ⟨?_, fun hy ↦ ⟨φ.symm ⟨y, hy⟩, (φ.symm ⟨y, hy⟩).property, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    simp [hg ⟨x, hx⟩]
  · simp [hg]

section Galois

variable [IsGalois K L]

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
      _ = E.fixingSubgroup := congrArg fixingSubgroup h
  · intro h
    rw [← InfiniteGalois.fixedField_fixingSubgroup (σ • E), AlgEquiv.smul_intermediateField_def,
      IsGalois.map_fixingSubgroup]
    convert congrArg fixedField h using 1 <;> congr 1
    exact (InfiniteGalois.fixedField_fixingSubgroup E).symm

/-- The Galois correspondence restricts to a bijection from conjugates of an intermediate
field to conjugates of its fixing subgroup. -/
noncomputable def conjugateFieldsEquivConjugateSubgroups (E : IntermediateField K L) :
    conjugateFields E ≃ MulAction.orbit (ConjAct (L ≃ₐ[K] L)) E.fixingSubgroup where
  toFun E' := ⟨E'.val.fixingSubgroup, by
    obtain ⟨σ, hσ⟩ := mem_conjugateFields_iff.mp E'.property
    refine TauCeti.mem_orbit_conjAct_iff.mpr ⟨σ, ?_⟩
    calc
      E.fixingSubgroup.map (MulAut.conj σ) = (E.map σ.toAlgHom).fixingSubgroup := by
        rw [IsGalois.map_fixingSubgroup]
        congr 1
      _ = E'.val.fixingSubgroup := congrArg fixingSubgroup hσ⟩
  invFun H := ⟨fixedField H.val, by
    obtain ⟨σ, hσ⟩ := TauCeti.mem_orbit_conjAct_iff.mp H.property
    apply mem_conjugateFields_iff.mpr
    refine ⟨σ, ?_⟩
    calc
      E.map σ.toAlgHom = σ • E := (AlgEquiv.smul_intermediateField_def σ E).symm
      _ = fixedField (E.fixingSubgroup.map (MulAut.conj σ)) := by
        simp only [Subgroup.fixedField_map_conj, InfiniteGalois.fixedField_fixingSubgroup,
          AlgEquiv.smul_intermediateField_def]
      _ = fixedField H.val := congrArg fixedField hσ
      _ = _ := rfl⟩
  left_inv E' := Subtype.ext (InfiniteGalois.fixedField_fixingSubgroup E'.val)
  right_inv H := by
    obtain ⟨σ, hσ⟩ := TauCeti.mem_orbit_conjAct_iff.mp H.property
    apply Subtype.ext
    -- By the `toFun` and `invFun` fields above, the round trip is by definition the fixing
    -- subgroup of the fixed field of `H`; `change` states this before the Galois rewrites.
    change (fixedField H.val).fixingSubgroup = H.val
    rw [← hσ, Subgroup.fixedField_map_conj,
      InfiniteGalois.fixedField_fixingSubgroup, IsGalois.map_fixingSubgroup]
    congr 1

/-- The forward Galois correspondence sends a conjugate field to its fixing subgroup. -/
@[simp]
theorem conjugateFieldsEquivConjugateSubgroups_apply (E : IntermediateField K L)
    (E' : conjugateFields E) :
    (conjugateFieldsEquivConjugateSubgroups E E').val = E'.val.fixingSubgroup := by
  simp [conjugateFieldsEquivConjugateSubgroups]

/-- The inverse Galois correspondence sends a conjugate subgroup to its fixed field. -/
@[simp]
theorem conjugateFieldsEquivConjugateSubgroups_symm_apply (E : IntermediateField K L)
    (H : MulAction.orbit (ConjAct (L ≃ₐ[K] L)) E.fixingSubgroup) :
    ((conjugateFieldsEquivConjugateSubgroups E).symm H).val = fixedField H.val := by
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
    ((quotientNormalizerEquivConjugateFields E) (QuotientGroup.mk σ)).val = σ • E := by
  simp only [quotientNormalizerEquivConjugateFields, Equiv.trans_apply,
    Subgroup.quotientEquivOfEq_mk, Equiv.subtypeEquivRight_apply,
    MulAction.orbitEquivQuotientStabilizer_symm_apply]

/-- The normalizer-coset parametrization respects the ambient Galois action. -/
@[simp]
theorem quotientNormalizerEquivConjugateFields_smul (E : IntermediateField K L)
    (σ : L ≃ₐ[K] L)
    (q : (L ≃ₐ[K] L) ⧸ Subgroup.normalizer (E.fixingSubgroup : Set (L ≃ₐ[K] L))) :
    (quotientNormalizerEquivConjugateFields E (σ • q)).val =
      σ • (quotientNormalizerEquivConjugateFields E q).val := by
  induction q using Quotient.inductionOn' with
  | _ τ => simp [mul_smul]

/-- The number of distinct conjugates of an intermediate field is the index of the normalizer
of its fixing subgroup. -/
@[simp]
theorem ncard_conjugateFields (E : IntermediateField K L) :
    (conjugateFields E).ncard =
      (Subgroup.normalizer (E.fixingSubgroup : Set (L ≃ₐ[K] L))).index := by
  -- The imported definition does not unfold here; identify its orbit through membership.
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

namespace Subgroup

/-- **Isomorphic fixed fields and conjugate subgroups.** For finite subgroups `H` and `H'` of the
automorphism group of a normal extension `L / K`, the fixed fields of `H` and `H'` are isomorphic
as `K`-algebras exactly when `H'` is a conjugate `σ H σ⁻¹` of `H`.

For a finite Galois extension every subgroup is finite, so this compares the fixed fields of any
two subgroups. Isomorphic subgroups do not suffice: in a Galois extension of `ℚ` with group `S₄`,
the normal Klein four-group and a non-normal one are isomorphic but not conjugate, and their fixed
fields are not isomorphic. -/
theorem nonempty_fixedField_algEquiv_iff_exists_map_conj_eq [_root_.Normal K L]
    (H H' : Subgroup (L ≃ₐ[K] L)) [Finite H] [Finite H'] :
    Nonempty (fixedField H ≃ₐ[K] fixedField H') ↔
      ∃ σ : L ≃ₐ[K] L, H.map (MulAut.conj σ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L)) = H' := by
  rw [IntermediateField.nonempty_algEquiv_iff_mem_conjugateFields,
    IntermediateField.mem_conjugateFields_iff]
  refine exists_congr fun σ ↦ ⟨fun h ↦ ?_, fun h ↦ by rw [← h, fixedField_map_conj]⟩
  -- A finite subgroup is the fixing subgroup of its fixed field, so equal fixed fields force
  -- equal subgroups.
  have : Finite (H.map (MulAut.conj σ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L))) :=
    Finite.of_equiv H (H.equivMapOfInjective _ (MulAut.conj σ).injective).toEquiv
  rw [← IntermediateField.fixingSubgroup_fixedField_of_finite (H.map _), fixedField_map_conj,
    ← IntermediateField.fixingSubgroup_fixedField_of_finite H']
  exact congrArg IntermediateField.fixingSubgroup h

end Subgroup
