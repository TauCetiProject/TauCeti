/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Finiteness instances for finitely presented modules on a scheme

A finitely presented `𝒪_X`-module is quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isFinitePresentation`) and of finite type
(`AlgebraicGeometry.Scheme.Modules.isFiniteType_of_isFinitePresentation`). These are the
corresponding sheaf-of-modules instances, restated for `X.Modules`: typeclass search does not
unfold `Scheme.Modules` to find them.
-/

public section

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules) [M.IsFinitePresentation]

/-- A finitely presented scheme module is quasi-coherent. -/
instance (priority := 100) isQuasicoherent_of_isFinitePresentation : M.IsQuasicoherent :=
  SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M

/-- A finitely presented scheme module is of finite type. -/
instance (priority := 100) isFiniteType_of_isFinitePresentation : M.IsFiniteType :=
  SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M

end AlgebraicGeometry.Scheme.Modules
