/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

/-!
# The action of a form-preserving representation on the kernel

A representation `ρ` of a group `H` on `W` by isometries of a bilinear form `B` maps the kernel
of `B` to itself (`LinearMap.BilinForm.IsometryEquiv.map_ker`), so it restricts to a
representation on `ker B` (`LinearMap.BilinForm.kerRepresentation`), and induces the
contragredient representation `a ↦ a ∘ ρ(h⁻¹)` on the dual of `ker B`
(`LinearMap.BilinForm.kerDualRepresentation`).
-/

public section

open Module

namespace LinearMap.BilinForm

variable {R H W : Type*} [CommRing R] [Group H] [AddCommGroup W] [Module R W]
  (B : LinearMap.BilinForm R W)

/-- A representation of `H` on `W` preserving `B` restricts to a representation on the kernel of
`B`. -/
noncomputable def kerRepresentation (ρ : H →* W ≃ₗ[R] W) (hρ : ∀ h, B.IsOrthogonal (ρ h)) :
    H →* LinearMap.ker B ≃ₗ[R] LinearMap.ker B where
  toFun h := (ρ h).ofSubmodules _ _ (⟨ρ h, hρ h⟩ : B.IsometryEquiv B).map_ker
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

variable {B}

/-- The action on the kernel is the restriction of the action on `W`. -/
@[simp]
theorem coe_kerRepresentation_apply {ρ : H →* W ≃ₗ[R] W}
    (hρ : ∀ h, B.IsOrthogonal (ρ h)) (h : H) (k : LinearMap.ker B) :
    (B.kerRepresentation ρ hρ h k : W) = ρ h k :=
  (rfl)

variable (B) in
/-- The contragredient action `a ↦ a ∘ ρ(h⁻¹)` of `H` on the dual of the kernel of a form `B`
preserved by `ρ`. -/
noncomputable def kerDualRepresentation (ρ : H →* W ≃ₗ[R] W) (hρ : ∀ h, B.IsOrthogonal (ρ h)) :
    H →* Dual R (LinearMap.ker B) ≃ₗ[R] Dual R (LinearMap.ker B) where
  toFun h := (B.kerRepresentation ρ hρ h⁻¹).dualMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- The contragredient action is `a ↦ a ∘ ρ(h⁻¹)`. -/
@[simp]
theorem kerDualRepresentation_apply_apply {ρ : H →* W ≃ₗ[R] W}
    (hρ : ∀ h, B.IsOrthogonal (ρ h)) (h : H) (a : Dual R (LinearMap.ker B))
    (k : LinearMap.ker B) :
    B.kerDualRepresentation ρ hρ h a k = a (B.kerRepresentation ρ hρ h⁻¹ k) :=
  (rfl)

end LinearMap.BilinForm
