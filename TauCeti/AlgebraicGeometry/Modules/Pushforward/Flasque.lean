/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Flasqueness of direct images of scheme modules

Direct image preserves flasqueness: its restriction maps are restriction maps of the source
module over inverse images of opens.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Direct image of a flasque scheme module is flasque. -/
instance isFlasque_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    [M.presheaf.IsFlasque] : ((pushforward f).obj M).presheaf.IsFlasque :=
  TopCat.Presheaf.IsFlasque.pushforward_isFlasque M.presheaf f.base

end AlgebraicGeometry.Scheme.Modules
