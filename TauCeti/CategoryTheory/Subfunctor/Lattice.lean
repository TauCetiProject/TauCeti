/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The lattice of subfunctors is completely distributive

Arbitrary suprema and infima of subfunctors are computed objectwise as unions and intersections
of sets, so the lattice of subfunctors of a functor `F : C ⥤ Type w` is completely distributive.
In particular it is a frame, a coframe and a distributive lattice. This applies to the
subcomplexes of a simplicial set.
-/

public section

namespace CategoryTheory.Subfunctor

universe w v u

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w}

instance instCompletelyDistribLattice : CompletelyDistribLattice (Subfunctor F) :=
  .ofMinimalAxioms
    { iInf_iSup_eq := fun f ↦ Subfunctor.ext <| funext fun U ↦ by
        simp only [iInf_obj, iSup_obj]
        -- `⋂` and `⋃` are `⨅` and `⨆` in the completely distributive lattice `Set (F.obj U)`.
        exact iInf_iSup_eq }

end CategoryTheory.Subfunctor
