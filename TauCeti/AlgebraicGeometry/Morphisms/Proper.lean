/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper morphisms of affine schemes, and integrality over affine opens

A morphism of affine schemes `Spec S ⟶ Spec R` is proper exactly when `S` is a finite
`R`-module. This is the affine case of Mathlib's characterization of finite morphisms as the
proper affine ones (`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`), combined with
the description of finite morphisms of affine schemes
(`AlgebraicGeometry.IsFinite.SpecMap_iff`).

For example, the affine line `Spec R[t] ⟶ Spec R` over a nonzero ring is not proper, since
`R[t]` is not a finite `R`-module.

For a universally closed morphism `f : X ⟶ Y` and an affine open `U ⊆ Y`, the ring map
`Γ(Y, U) ⟶ Γ(X, f⁻¹U)` is integral
(`AlgebraicGeometry.Scheme.Hom.isIntegral_app_of_universallyClosed`). This is Mathlib's
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` applied to the restriction of `f`
over `U`; it holds without finiteness or Noetherian hypotheses.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of affine schemes `Spec S ⟶ Spec R` is proper if and only if the ring map
`R → S` is finite. -/
@[simp]
lemma IsProper.SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsProper (Spec.map f) ↔ f.hom.Finite := by
  rw [← IsFinite.SpecMap_iff, IsFinite.iff_isProper_and_isAffineHom,
    and_iff_left (by infer_instance)]

/-- For a universally closed morphism `f : X ⟶ Y` and an affine open `U ⊆ Y`, the ring map
`Γ(Y, U) ⟶ Γ(X, f⁻¹U)` is integral. This is Mathlib's `isIntegral_appTop_of_universallyClosed`
for the restriction of `f` over `U`. -/
theorem Scheme.Hom.isIntegral_app_of_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] {U : Y.Opens} (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral := by
  have : IsAffine U := hU
  have h := isIntegral_appTop_of_universallyClosed (f ∣_ U)
  rw [morphismRestrict_appTop] at h
  replace h := (RingHom.isIntegral_respectsIso.cancel_right_isIso _ _).mp h
  -- Transport along `U.ι ''ᵁ ⊤ = U`, which changes the type of `f.app`.
  have key : ∀ W, W = U → (f.app W).hom.IsIntegral → (f.app U).hom.IsIntegral := by
    rintro _ rfl h
    exact h
  exact key _ (by simp) h

end AlgebraicGeometry
