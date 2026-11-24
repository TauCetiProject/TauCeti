/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The structure sheaf as an `𝒪_X`-module

Mathlib's structure sheaf of modules `SheafOfModules.unit X.ringCatSheaf` is an object of
`SheafOfModules X.ringCatSheaf`, whose category structure is not reducibly that of the category
`X.Modules` of `𝒪_X`-modules on a scheme `X`. This file names it as an object of `X.Modules`, so
that morphisms of `X.Modules` out of or into `𝒪_X` compose, and are rewritten, in `X.Modules`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.unit X`: the structure sheaf `𝒪_X` as an object of
  `X.Modules`.
-/

public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The structure sheaf `𝒪_X` as an object of `X.Modules`. Since `X.Modules` is not reducibly
`SheafOfModules X.ringCatSheaf`, morphisms of `X.Modules` out of `𝒪_X`, such as the restriction
`Scheme.IdealSheafData.toPushforwardSubscheme`, are stated with this object to stay well-typed at
reducible transparency, where `rw` and `simp` work. -/
noncomputable abbrev unit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

end AlgebraicGeometry.Scheme.Modules
