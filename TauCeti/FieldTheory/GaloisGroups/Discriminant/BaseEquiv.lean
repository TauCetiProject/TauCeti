/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Discriminant.Field
import TauCeti.FieldTheory.Kummer.Extension

/-!
# Discriminant fields under base-field isomorphisms

Compatible ring isomorphisms `e : F ≃+* F'` and `τ : E ≃+* E'` carry the discriminant field of
`f : F[X]` in `E` onto that of `f.map e` in `E'`. This compares extensions with different base
fields, whereas `TauCeti.discrField_map` compares extensions over the same base field.

The image equality `TauCeti.discrField_map_ringEquiv` is stated using subfields: the two
intermediate fields have different base types, so `IntermediateField.map` does not apply.
`TauCeti.discrFieldRingEquiv` restricts the ambient isomorphism to these fields and commutes with
the base isomorphism. No square root needs to be chosen, and the result includes the cases of a
zero or square discriminant, characteristic two, and ambient fields containing no square root.

The construction uses the discriminant base-change identity and Mathlib's
`Subring.equivMapOfInjective` to restrict the ambient isomorphism.
-/

public section

namespace TauCeti

open Polynomial

variable {F F' E E' : Type*} [Field F] [Field F'] [Field E] [Field E']
    [Algebra F E] [Algebra F' E']
    {f : F[X]} {e : F ≃+* F'} {τ : E ≃+* E'}

/-- Compatible isomorphisms of the base and ambient fields carry the discriminant field onto
that of the polynomial with transported coefficients. -/
theorem discrField_map_ringEquiv
    (hcomm : (τ : E →+* E').comp (algebraMap F E) =
      (algebraMap F' E').comp (e : F →+* F')) :
    (discrField f E).toSubfield.map (τ : E →+* E') =
      (discrField (f.map (e : F →+* F')) E').toSubfield := by
  have hdiscr : (f.map (e : F →+* F')).discr = e f.discr :=
    Polynomial.discr_map_of_natDegree_eq (e : F →+* F')
      (Polynomial.natDegree_map_eq_of_injective e.injective f)
  have hbase : τ '' Set.range (algebraMap F E) = Set.range (algebraMap F' E') := by
    rw [← Set.range_comp]
    have hfun : τ ∘ algebraMap F E = algebraMap F' E' ∘ e := by
      simpa only [RingHom.coe_comp, RingEquiv.coe_toRingHom]
        using congrArg DFunLike.coe hcomm
    rw [hfun]
    exact e.surjective.range_comp (algebraMap F' E')
  have hroots : τ '' (X ^ 2 - C f.discr).rootSet E =
      (X ^ 2 - C (f.map (e : F →+* F')).discr).rootSet E' := by
    ext y
    simp only [Set.mem_image, Polynomial.mem_rootSet_X_pow_sub_C two_ne_zero, hdiscr]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← map_pow, hx]
      exact DFunLike.congr_fun hcomm f.discr
    · intro hy
      refine ⟨τ.symm y, ?_, τ.apply_symm_apply y⟩
      apply τ.injective
      rw [map_pow, τ.apply_symm_apply, hy]
      exact (DFunLike.congr_fun hcomm f.discr).symm
  rw [discrField_def, discrField_def, IntermediateField.adjoin_toSubfield,
    IntermediateField.adjoin_toSubfield, RingHom.map_field_closure, Set.image_union]
  simp only [RingEquiv.coe_toRingHom, hbase, hroots]

/-- The restriction of a compatible ambient isomorphism to the discriminant fields.
It lies over the given base-field isomorphism, as expressed by
`TauCeti.discrFieldRingEquiv_algebraMap`. -/
noncomputable def discrFieldRingEquiv
    (hcomm : (τ : E →+* E').comp (algebraMap F E) =
      (algebraMap F' E').comp (e : F →+* F')) :
    discrField f E ≃+* discrField (f.map (e : F →+* F')) E' :=
  -- The intermediate field, its subfield, and its subring have the same carrier and operations.
  ((discrField f E).toSubfield.toSubring.equivMapOfInjective (τ : E →+* E') τ.injective).trans
    (RingEquiv.subfieldCongr (discrField_map_ringEquiv hcomm))

/-- On elements, the induced isomorphism is the ambient isomorphism. -/
@[simp]
theorem discrFieldRingEquiv_apply
    (hcomm : (τ : E →+* E').comp (algebraMap F E) =
      (algebraMap F' E').comp (e : F →+* F'))
    (x : discrField f E) :
    (discrFieldRingEquiv hcomm x : E') = τ (x : E) := by
  -- Equality transport between subfields preserves the underlying ambient element.
  have coe_subfieldCongr {S T : Subfield E'} (h : S = T) (y : S) :
      (RingEquiv.subfieldCongr h y : E') = (y : E') := by
    subst T
    rfl
  unfold discrFieldRingEquiv
  -- Use full transparency to identify the intermediate-field, subfield, and subring carriers.
  erw [RingEquiv.trans_apply, coe_subfieldCongr, Subring.coe_equivMapOfInjective_apply]
  simp only [RingEquiv.coe_toRingHom]

/-- The inverse induced isomorphism is the inverse ambient isomorphism. -/
@[simp]
theorem discrFieldRingEquiv_symm_apply
    (hcomm : (τ : E →+* E').comp (algebraMap F E) =
      (algebraMap F' E').comp (e : F →+* F'))
    (x : discrField (f.map (e : F →+* F')) E') :
    ((discrFieldRingEquiv hcomm).symm x : E) = τ.symm (x : E') := by
  apply τ.injective
  simp only [τ.apply_symm_apply, ← discrFieldRingEquiv_apply hcomm,
    RingEquiv.apply_symm_apply]

/-- The discriminant-field isomorphism commutes with the base-field isomorphism. -/
@[simp]
theorem discrFieldRingEquiv_algebraMap
    (hcomm : (τ : E →+* E').comp (algebraMap F E) =
      (algebraMap F' E').comp (e : F →+* F'))
    (x : F) :
    discrFieldRingEquiv hcomm (algebraMap F (discrField f E) x) =
      algebraMap F' (discrField (f.map (e : F →+* F')) E') (e x) := by
  apply Subtype.ext
  rw [discrFieldRingEquiv_apply, IntermediateField.coe_algebraMap_apply,
    IntermediateField.coe_algebraMap_apply]
  simpa only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom] using
    DFunLike.congr_fun hcomm x

/-- The inverse discriminant-field isomorphism commutes with the inverse base isomorphism. -/
@[simp]
theorem discrFieldRingEquiv_symm_algebraMap
    (hcomm : (τ : E →+* E').comp (algebraMap F E) =
      (algebraMap F' E').comp (e : F →+* F'))
    (x : F') :
    (discrFieldRingEquiv hcomm).symm
        (algebraMap F' (discrField (f.map (e : F →+* F')) E') x) =
      algebraMap F (discrField f E) (e.symm x) := by
  apply (discrFieldRingEquiv hcomm).injective
  simp only [RingEquiv.apply_symm_apply, discrFieldRingEquiv_algebraMap]

end TauCeti
