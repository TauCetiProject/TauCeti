/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The distributive lattice of subfunctors

The subfunctors of a functor `F : C ⥤ Type w` form a distributive lattice, since their suprema
and infima are computed objectwise as unions and intersections of sets.
-/

public section

namespace CategoryTheory.Subfunctor

variable {C : Type*} [Category* C] {F : C ⥤ Type*}

/-- The subfunctors of a functor form a distributive lattice: suprema and infima are computed
objectwise as unions and intersections. -/
instance instDistribLattice : DistribLattice (Subfunctor F) :=
  DistribLattice.ofInfSupLe fun _ _ _ _ ↦ (inf_sup_left (α := Set _) _ _ _).le

end CategoryTheory.Subfunctor
