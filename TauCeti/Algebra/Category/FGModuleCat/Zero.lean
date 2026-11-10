/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic

/-!
# Zero finitely generated modules

A finitely generated module is a zero object of the category of finitely generated modules
exactly when its carrier is subsingleton; in particular a nontrivial ring is a nonzero module over
itself. The zero object of `FGModuleCat` itself comes from the
`ContainsZero` instance for `ModuleCat.isFG` in `TauCeti.Algebra.Category.FGModuleCat.Basic`.
-/

public section

namespace FGModuleCat

open CategoryTheory CategoryTheory.Limits

universe v u

/-- A finitely generated module is a zero object exactly when its carrier is subsingleton. -/
theorem isZero_iff_subsingleton {R : Type u} [Ring R]
    {M : FGModuleCat.{v} R} : IsZero M ↔ Subsingleton M := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  exact ⟨(ObjectProperty.ι _).map_isZero, .of_full_of_faithful_of_isZero (ObjectProperty.ι _) _⟩

/-- A nontrivial ring is a nonzero finitely generated module over itself. -/
theorem not_isZero_of_self {R : Type u} [Ring R] [Nontrivial R] : ¬ IsZero (FGModuleCat.of R R) :=
  fun h ↦ not_subsingleton R (isZero_iff_subsingleton.mp h)

end FGModuleCat
