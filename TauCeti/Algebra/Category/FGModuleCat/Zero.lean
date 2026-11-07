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
exactly when its carrier is subsingleton. The zero module is finitely generated, so the
finitely generated modules contain a zero object of `ModuleCat`; Mathlib then provides the zero
object of `FGModuleCat`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

/-- A finitely generated module is a zero object exactly when its carrier is subsingleton. -/
theorem _root_.FGModuleCat.isZero_iff_subsingleton {R : Type u} [Ring R]
    {M : FGModuleCat.{v} R} : IsZero M ↔ Subsingleton M := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  exact ⟨(ObjectProperty.ι _).map_isZero, .of_full_of_faithful_of_isZero (ObjectProperty.ι _) _⟩

/-- The finitely generated modules contain the zero module, so `FGModuleCat` has a zero
object. -/
instance _root_.ModuleCat.isFG_containsZero {R : Type u} [Ring R] :
    (ModuleCat.isFG.{v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    (ModuleCat.isFG_iff _).2 inferInstance⟩

end TauCeti
