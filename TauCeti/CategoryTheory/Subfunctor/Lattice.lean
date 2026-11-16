/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The lattice of subfunctors is distributive

Suprema and infima of subfunctors are computed objectwise as unions and intersections of sets, so
the lattice of subfunctors of a functor `F : C ⥤ Type w` is distributive. This applies in
particular to the subcomplexes of a simplicial set.
-/

public section

namespace CategoryTheory.Subfunctor

universe w v u

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w}

instance instDistribLattice : DistribLattice (Subfunctor F) :=
  DistribLattice.ofInfSupLe fun S T T' ↦ (le_def _ _).2 fun U ↦ by
    rw [min_obj, max_obj, max_obj, min_obj, min_obj]
    exact (inf_sup_left _ _ _).le

end CategoryTheory.Subfunctor
