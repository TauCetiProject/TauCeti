/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic

/-!
# Zero finitely generated modules

A finitely generated module with subsingleton carrier is a zero object of the category of
finitely generated modules. This criterion supplies the zero components of finite-projective
matrix factorizations.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

/-- A finitely generated module with subsingleton carrier is a zero object. -/
theorem _root_.FGModuleCat.isZero_of_subsingleton {R : Type u} [Ring R] (M : FGModuleCat.{v} R)
    (hM : Subsingleton M) : IsZero M := by
  apply IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _)
  exact ModuleCat.isZero_iff_subsingleton.mpr hM

end TauCeti
