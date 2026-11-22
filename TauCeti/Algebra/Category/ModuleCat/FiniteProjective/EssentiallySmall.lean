/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.EssentiallySmall
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Basic

/-!
# Essential smallness of finitely generated projective modules

Finitely generated `R`-modules are essentially small in the universe of `R`
(`TauCeti.Algebra.Category.FGModuleCat.EssentiallySmall`), so the subproperty
`TauCeti.finiteProjectiveModules R` of finitely generated projective `R`-modules is also
essentially small in the universe of `R`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

/-- Finitely generated projective `R`-modules form an essentially small subcategory in the universe
of `R`. -/
instance (R : Type u) [Ring R] : ObjectProperty.EssentiallySmall.{u} (finiteProjectiveModules R) :=
  ObjectProperty.EssentiallySmall.of_le (finiteProjectiveModules_le_finiteModules R)

end TauCeti
