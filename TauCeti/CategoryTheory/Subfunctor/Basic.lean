/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The completely distributive lattice of subfunctors

Arbitrary suprema and infima of subfunctors of a functor `F : C ⥤ Type w` are computed objectwise
as unions and intersections of sets, so the lattice of subfunctors is completely distributive. In
particular it is a frame, a coframe and a distributive lattice. This applies to the subcomplexes of
a simplicial set.
-/

public section

namespace CategoryTheory.Subfunctor

variable {C : Type*} [Category* C] {F : C ⥤ Type*}

/-- The subfunctors of a functor form a completely distributive lattice: arbitrary suprema and
infima are computed objectwise as unions and intersections. -/
instance instCompletelyDistribLattice : CompletelyDistribLattice (Subfunctor F) :=
  .ofMinimalAxioms
    { iInf_iSup_eq := fun f ↦ Subfunctor.ext <| funext fun U ↦ by
        simp only [iInf_obj, iSup_obj]
        -- `⋂` and `⋃` are `⨅` and `⨆` in the completely distributive lattice `Set (F.obj U)`.
        exact iInf_iSup_eq }

end CategoryTheory.Subfunctor
