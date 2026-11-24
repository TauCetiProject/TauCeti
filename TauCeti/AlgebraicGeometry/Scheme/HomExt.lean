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

end AlgebraicGeometry.Scheme.Hom
