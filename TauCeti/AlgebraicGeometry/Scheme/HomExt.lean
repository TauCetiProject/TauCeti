/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Extensionality of scheme morphisms through `appLE`

Mathlib's `AlgebraicGeometry.Scheme.Hom.ext` compares two morphisms of schemes with the same
underlying map through their maps `app` on sections, up to an `eqToHom` restriction. This file
states the same criterion through the maps `appLE`, which avoids that restriction.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ext_of_appLE`: two morphisms with the same underlying map agree
  if `φ.appLE V (ψ ⁻¹ᵁ V)` agrees with `ψ.app V` for every open `V`.
* `AlgebraicGeometry.Scheme.Hom.ext_of_appLE_eq_appLE`: two morphisms with the same underlying
  map agree if their maps `appLE` agree.
* `AlgebraicGeometry.Scheme.Hom.appLE_appLE_eq_app`: composing maps `appLE` of `g` and `f` gives
  the map `app` of `f ≫ g`, the form in which the hypothesis of `ext_of_appLE` arises for a
  composite.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Y Z : Scheme.{u}} {φ ψ : Y ⟶ Z}

/-- Two morphisms of schemes with the same underlying map agree if their maps on sections agree. -/
theorem ext_of_appLE (hbase : φ.base = ψ.base)
    (h : ∀ V e (x : Γ(Z, V)), φ.appLE V (ψ ⁻¹ᵁ V) e x = ψ.app V x) : φ = ψ := by
  refine Scheme.Hom.ext hbase fun V ↦ ?_
  rw [app_eq_appLE φ, appLE_map]
  ext x
  exact h V _ x

/-- Two morphisms of schemes with the same underlying map agree if their maps on sections agree. -/
theorem ext_of_appLE_eq_appLE (hbase : φ.base = ψ.base)
    (h : ∀ V U e e' (x : Γ(Z, V)), φ.appLE V U e x = ψ.appLE V U e' x) : φ = ψ :=
  ext_of_appLE hbase fun V e x ↦ (h V _ e le_rfl x).trans (by rw [appLE_eq_app])

/-- Applying `g.appLE U V` and then `f.appLE V ((f ≫ g) ⁻¹ᵁ U)` to a section is applying
`(f ≫ g).app U`. -/
theorem appLE_appLE_eq_app {X : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : (f ≫ g) ⁻¹ᵁ U ≤ f ⁻¹ᵁ V) (x : Γ(Z, U)) :
    f.appLE V ((f ≫ g) ⁻¹ᵁ U) e₂ (g.appLE U V e₁ x) = (f ≫ g).app U x := by
  rw [← CommRingCat.comp_apply, appLE_comp_appLE, app_eq_appLE]

end AlgebraicGeometry.Scheme.Hom
