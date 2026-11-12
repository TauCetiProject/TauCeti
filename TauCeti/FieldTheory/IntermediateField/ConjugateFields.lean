/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Conjugate intermediate fields

A monoid acting on `L` by `K`-algebra endomorphisms acts on the intermediate fields of `L / K`
by mapping their elements, in parallel with `Subalgebra.pointwiseMulAction`. In particular the
automorphism group of the extension acts this way, and the conjugates of a field form its orbit
under that action.

## Main definitions

* `IntermediateField.pointwiseMulAction`: the pointwise action, an instance in the `Pointwise`
  locale.
* `IntermediateField.conjugateFields`: the orbit of an intermediate field under the
  automorphism group.

## Main results

* `IntermediateField.pointwise_smul_def`: the action is `IntermediateField.map`.
* `IntermediateField.coe_pointwise_smul`, `IntermediateField.mem_smul_pointwise_iff_exists`:
  the underlying set and the elements of a translated intermediate field.
* `AlgEquiv.smul_intermediateField_def`: an automorphism acts by mapping along it.
* `IntermediateField.mem_conjugateFields_iff`: orbit membership is an automorphism image.
-/

public section

open MulAction
open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace IntermediateField

section Pointwise

variable {G : Type*} [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- The action on intermediate fields given by applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
protected def pointwiseMulAction : MulAction G (IntermediateField K L) where
  smul g E := E.map (MulSemiringAction.toAlgHom K L g)
  one_smul E := congr(E.map $(AlgHom.ext <| one_smul G)).trans E.map_id
  mul_smul _ _ E := congr(E.map $(AlgHom.ext <| mul_smul _ _)).trans (E.map_map _ _).symm

scoped[Pointwise] attribute [instance] IntermediateField.pointwiseMulAction

/-- Acting on an intermediate field means mapping it along the induced algebra endomorphism. -/
theorem pointwise_smul_def (g : G) (E : IntermediateField K L) :
    g • E = E.map (MulSemiringAction.toAlgHom K L g) :=
  (rfl)

/-- The underlying set of a translated intermediate field is the translated set. -/
@[simp, norm_cast]
theorem coe_pointwise_smul (g : G) (E : IntermediateField K L) :
    ((g • E : IntermediateField K L) : Set L) = g • (E : Set L) :=
  (rfl)

/-- The elements of `g • E` are the translates of the elements of `E`. -/
@[simp]
theorem mem_smul_pointwise_iff_exists (g : G) (x : L) (E : IntermediateField K L) :
    x ∈ g • E ↔ ∃ y ∈ E, g • y = x :=
  Set.mem_smul_set

end Pointwise

end IntermediateField

namespace AlgEquiv

/-- Conjugating an intermediate field means mapping it along the automorphism. -/
@[simp]
theorem smul_intermediateField_def (σ : L ≃ₐ[K] L) (E : IntermediateField K L) :
    σ • E = E.map σ :=
  (rfl)

end AlgEquiv

namespace IntermediateField

/-- The set of images of `E` under automorphisms of the ambient extension. -/
def conjugateFields (E : IntermediateField K L) : Set (IntermediateField K L) :=
  orbit (L ≃ₐ[K] L) E

/-- Membership in `conjugateFields E` means being the image of `E` under an automorphism. -/
@[simp]
theorem mem_conjugateFields_iff {E E' : IntermediateField K L} :
    E' ∈ conjugateFields E ↔ ∃ σ : L ≃ₐ[K] L, E.map σ = E' := by
  simp [conjugateFields, mem_orbit_iff, eq_comm]

end IntermediateField
