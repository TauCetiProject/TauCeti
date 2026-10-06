/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DualTensorIhom
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Dualizable modules and finite projectivity

An `R`-module is dualizable in the symmetric monoidal category `ModuleCat R` exactly when it
is finite projective. Under the internal-Hom identification, the categorical dual-tensor map
is Mathlib's `dualTensorHom`; invertibility at the module itself supplies a finite dual basis,
and Mathlib's dual-basis criterion yields finite projectivity. Conversely, a finite projective
module has an invertible contraction, so the categorical dual-basis criterion constructs its
dual.

This is the affine algebraic criterion used in comparing finite locally free sheaves with
dualizable quasicoherent sheaves.

The dual-basis criterion used here is from Mathlib's `LinearAlgebra.Contraction`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- A finite projective module is dualizable, with internal Hom into the tensor unit as a
canonical left dual. -/
noncomputable instance _root_.ModuleCat.hasLeftDualOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] : HasLeftDual M := by
  have h : IsIso ((dualTensorIhom M).app M) :=
    (ModuleCat.isIso_dualTensorIhom_app_iff M M).2 dualTensorHom_bijective
  let hI : IsIso ((dualTensorIhom M).app M) := h
  refine { leftDual := (ihom M).obj (𝟙_ (ModuleCat.{u} R)), exact := ?_ }
  exact exactPairingOfIsIsoDualTensorIhom (Y := M)

/-- A finite projective module also has a right dual in the symmetric monoidal category
`ModuleCat R`. -/
noncomputable instance _root_.ModuleCat.hasRightDualOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] : HasRightDual M :=
  BraidedCategory.hasRightDualOfHasLeftDual

/-- The chosen left dual of a finite projective module is its internal Hom into the unit. -/
@[simp]
theorem _root_.ModuleCat.leftDual_of_finite_projective
    [Module.Finite R M] [Module.Projective R M] :
    HasLeftDual.leftDual (Y := M) = (ihom M).obj (𝟙_ (ModuleCat.{u} R)) :=
  rfl

/-- The chosen right dual of a finite projective module is its internal Hom into the unit. -/
@[simp]
theorem _root_.ModuleCat.rightDual_of_finite_projective
    [Module.Finite R M] [Module.Projective R M] :
    HasRightDual.rightDual (X := M) = (ihom M).obj (𝟙_ (ModuleCat.{u} R)) :=
  rfl

/-- A dualizable module is finite projective: its coevaluation gives a finite dual basis. -/
theorem _root_.ModuleCat.finite_projective_of_hasLeftDual [HasLeftDual M] :
    Module.Finite R M ∧ Module.Projective R M := by
  have h : IsIso ((dualTensorIhom M).app M) := inferInstance
  have hb : Function.Bijective (dualTensorHom R M M) :=
    (ModuleCat.isIso_dualTensorIhom_app_iff M M).1 h
  have hmem : (1 : M →ₗ[R] M) ∈ (dualTensorHom R M M).range := hb.2 1
  exact ⟨Module.Finite.of_one_mem_range_dualTensorHom hmem,
    Module.Projective.of_one_mem_range_dualTensorHom hmem⟩

/-- A module with a right dual is finite projective. -/
theorem _root_.ModuleCat.finite_projective_of_hasRightDual [HasRightDual M] :
    Module.Finite R M ∧ Module.Projective R M := by
  let _ : HasLeftDual M := BraidedCategory.hasLeftDualOfHasRightDual
  exact ModuleCat.finite_projective_of_hasLeftDual M

/-- An `R`-module is dualizable if and only if it is finite projective. -/
theorem _root_.ModuleCat.nonempty_hasLeftDual_iff_finite_projective :
    Nonempty (HasLeftDual M) ↔ Module.Finite R M ∧ Module.Projective R M := by
  constructor
  · rintro ⟨h⟩
    let _ : HasLeftDual M := h
    exact ModuleCat.finite_projective_of_hasLeftDual M
  · rintro ⟨hfinite, hproj⟩
    let _ : Module.Finite R M := hfinite
    let _ : Module.Projective R M := hproj
    exact ⟨inferInstance⟩

/-- An `R`-module has a right dual if and only if it is finite projective. -/
theorem _root_.ModuleCat.nonempty_hasRightDual_iff_finite_projective :
    Nonempty (HasRightDual M) ↔ Module.Finite R M ∧ Module.Projective R M := by
  constructor
  · rintro ⟨h⟩
    let _ : HasRightDual M := h
    exact ModuleCat.finite_projective_of_hasRightDual M
  · rintro ⟨hfinite, hproj⟩
    let _ : Module.Finite R M := hfinite
    let _ : Module.Projective R M := hproj
    exact ⟨inferInstance⟩

end TauCeti
