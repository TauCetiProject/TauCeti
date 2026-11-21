/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Structure

/-!
# Inclusions and corestrictions of flat subcoalgebras

For a flat subcoalgebra `D` of a flat coalgebra `C`, the inclusion of `D.toSubmodule` into `C`
is a coalgebra morphism for the inherited coalgebra structure `TauCeti.Subcoalgebra.coalgebra`.
A coalgebra morphism whose values lie in `D` corestricts to a coalgebra morphism into `D`, and
a coalgebra morphism with flat range factors through its range.

## Main declarations

* `TauCeti.Subcoalgebra.subtype`: the inclusion of a subcoalgebra as a coalgebra morphism.
* `CoalgHom.codRestrict`: a coalgebra morphism corestricted to a subcoalgebra containing its
  values.
* `CoalgHom.rangeRestrict`: a coalgebra morphism corestricted to its range.

## References

This is the standard inclusion of a subcoalgebra; see Sweedler, *Hopf Algebras*, Chapter 2.
The comultiplication compatibility of a corestriction follows from injectivity of
`D ⊗ D → C ⊗ C`, given by Mathlib's `TensorProduct.map_injective_of_flat_flat`.
-/

public section

open scoped TensorProduct

universe u v w x

namespace TauCeti.Subcoalgebra

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable (D : Subcoalgebra R C) [Module.Flat R D.toSubmodule]

/-- The inclusion of a flat subcoalgebra as a coalgebra morphism. -/
@[expose] noncomputable def subtype : D.toSubmodule →ₗc[R] C where
  toLinearMap := D.toSubmodule.subtype
  counit_comp := rfl
  map_comp_comul := LinearMap.ext D.map_subtype_comulLinearMap

/-- The underlying linear map of a subcoalgebra inclusion is the submodule inclusion. -/
@[simp]
theorem subtype_toLinearMap :
    (D.subtype : D.toSubmodule →ₗ[R] C) = D.toSubmodule.subtype :=
  rfl

/-- The subcoalgebra inclusion acts as the subtype coercion. -/
@[simp]
theorem subtype_apply (x : D.toSubmodule) : D.subtype x = x :=
  rfl

/-- The subcoalgebra inclusion is the subtype coercion. -/
theorem coe_subtype : ⇑D.subtype = ((↑) : D.toSubmodule → C) :=
  rfl

/-- The inclusion of a subcoalgebra is injective. -/
theorem subtype_injective : Function.Injective D.subtype :=
  Subtype.val_injective

end TauCeti.Subcoalgebra

namespace CoalgHom

open TauCeti

variable {R : Type u} {A : Type v} {B : Type w} {C : Type x}
variable [CommSemiring R]
variable [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
variable [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]

/-- Corestrict a coalgebra morphism to a flat subcoalgebra containing its values. -/
@[expose] noncomputable def codRestrict (f : A →ₗc[R] C) (D : Subcoalgebra R C)
    [Module.Flat R D.toSubmodule] (h : ∀ a, f a ∈ D) : A →ₗc[R] D.toSubmodule where
  toLinearMap := f.toLinearMap.codRestrict D.toSubmodule h
  counit_comp := by
    ext a
    exact CoalgHomClass.counit_comp_apply f a
  map_comp_comul := by
    ext a
    apply TensorProduct.map_injective_of_flat_flat D.toSubmodule.subtype D.toSubmodule.subtype
      Subtype.val_injective Subtype.val_injective
    simp only [LinearMap.comp_apply, TensorProduct.map_map, Subcoalgebra.comul_apply,
      Subcoalgebra.map_subtype_comulLinearMap]
    exact CoalgHomClass.map_comp_comul_apply f a

variable (f : A →ₗc[R] C) (D : Subcoalgebra R C) [Module.Flat R D.toSubmodule]

/-- The underlying linear map of a corestricted coalgebra morphism is the linear
corestriction. -/
@[simp]
theorem codRestrict_toLinearMap (h : ∀ a, f a ∈ D) :
    (f.codRestrict D h : A →ₗ[R] D.toSubmodule) =
      (f : A →ₗ[R] C).codRestrict D.toSubmodule h :=
  rfl

/-- Corestricting a coalgebra morphism changes only its codomain. -/
@[simp]
theorem codRestrict_apply (h : ∀ a, f a ∈ D) (a : A) : (f.codRestrict D h a : C) = f a :=
  rfl

/-- Composing a corestricted coalgebra morphism with the subcoalgebra inclusion recovers the
original morphism. -/
@[simp]
theorem subtype_comp_codRestrict (h : ∀ a, f a ∈ D) : D.subtype.comp (f.codRestrict D h) = f :=
  rfl

/-- A coalgebra morphism into a subcoalgebra is the corestriction of its composite with the
inclusion. -/
@[simp]
theorem codRestrict_subtype_comp (g : A →ₗc[R] D.toSubmodule) :
    (D.subtype.comp g).codRestrict D (fun a ↦ (g a).2) = g :=
  rfl

/-- Corestriction commutes with precomposition. -/
theorem codRestrict_comp (f : B →ₗc[R] C) (g : A →ₗc[R] B) (h : ∀ b, f b ∈ D) :
    (f.comp g).codRestrict D (fun a ↦ h (g a)) = (f.codRestrict D h).comp g :=
  rfl

variable [Module.Flat R f.range.toSubmodule]

/-- A coalgebra morphism with flat range, corestricted to its range. -/
@[expose] noncomputable def rangeRestrict : A →ₗc[R] f.range.toSubmodule :=
  f.codRestrict f.range f.mem_range_self

/-- Range restriction does not change values. -/
@[simp]
theorem rangeRestrict_apply (a : A) : (f.rangeRestrict a : C) = f a :=
  rfl

/-- Composing the range restriction with the range inclusion recovers the morphism. -/
@[simp]
theorem subtype_comp_rangeRestrict : f.range.subtype.comp f.rangeRestrict = f :=
  rfl

/-- The range restriction of a coalgebra morphism is surjective. -/
theorem surjective_rangeRestrict : Function.Surjective f.rangeRestrict := by
  rintro ⟨c, hc⟩
  obtain ⟨a, rfl⟩ := mem_range.1 hc
  exact ⟨a, rfl⟩

end CoalgHom
