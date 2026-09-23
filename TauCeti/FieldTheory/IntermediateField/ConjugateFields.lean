/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Conjugate intermediate fields

The automorphism group of an extension acts on its intermediate fields by mapping their
elements. The conjugates of a field form its orbit under this action.

## Main definitions

* `TauCeti.instMulActionIntermediateField`: automorphisms act by mapping intermediate fields.
* `IntermediateField.conjugateFields`: the orbit of an intermediate field.

## Main results

* `AlgEquiv.smul_intermediateField_def`: the action is `IntermediateField.map`.
* `IntermediateField.mem_conjugateFields_iff`: orbit membership is an automorphism image.
-/

public section

namespace TauCeti

open IntermediateField MulAction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The action of the automorphism group of `L / K` on its intermediate fields. -/
instance instMulActionIntermediateField : MulAction (L ≃ₐ[K] L) (IntermediateField K L) where
  smul σ E := E.map σ.toAlgHom
  one_smul E := by
    -- The action is defined by `map`; the identity automorphism coerces to `AlgHom.id`.
    change E.map (AlgHom.id K L) = E
    exact E.map_id
  mul_smul σ τ E := by
    -- The product automorphism coerces to the composite in the order used by `map_map`.
    change E.map (σ * τ).toAlgHom = (E.map τ.toAlgHom).map σ.toAlgHom
    rw [IntermediateField.map_map]
    congr 1

end TauCeti

open IntermediateField MulAction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace AlgEquiv

/-- Conjugating an intermediate field means mapping it along the automorphism. -/
@[simp]
theorem smul_intermediateField_def (σ : L ≃ₐ[K] L) (E : IntermediateField K L) :
    σ • E = E.map σ.toAlgHom :=
  rfl

end AlgEquiv

namespace IntermediateField

/-- The set of images of `E` under automorphisms of the ambient extension. -/
def conjugateFields (E : IntermediateField K L) : Set (IntermediateField K L) :=
  orbit (L ≃ₐ[K] L) E

/-- Conjugate fields are the orbit under automorphisms of the ambient extension. -/
theorem conjugateFields_def (E : IntermediateField K L) :
    conjugateFields E = orbit (L ≃ₐ[K] L) E :=
  by simp only [conjugateFields]

/-- Membership in `conjugateFields E` means being the image of `E` under an automorphism. -/
@[simp]
theorem mem_conjugateFields_iff {E E' : IntermediateField K L} :
    E' ∈ conjugateFields E ↔ ∃ σ : L ≃ₐ[K] L, E.map σ.toAlgHom = E' := by
  simp [conjugateFields, mem_orbit_iff, eq_comm]

end IntermediateField
