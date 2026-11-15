/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup

/-!
# Weyl words on the pinned F₄ root table

The empty-word and cons equations for `TauCeti.DynkinType.geckWeylRootIndex`, specialized
to `Fin 4`, evaluate Weyl transport using the explicit forty-eight-root F₄ reflection table.
They use the generic Weyl-word equations and the pinned F₄ simple-root and reflection indices.
-/

public section

namespace TauCeti.DynkinType

/-- The empty Weyl word selects the starting simple root in the pinned F₄ table. -/
@[simp] theorem geckWeylRootIndex_F4_nil (i : Fin 4) :
    F4.geckWeylRootIndex valid_F4 [] i = Fin.castAdd 44 i := by
  exact (F4.geckWeylRootIndex_nil valid_F4 i).trans (simpleIndex_F4 valid_F4 i)

/-- Prepending a node to an F₄ Weyl word applies its tabulated simple reflection. -/
@[simp] theorem geckWeylRootIndex_F4_cons (j : Fin 4) (l : List (Fin 4)) (i : Fin 4) :
    F4.geckWeylRootIndex valid_F4 (j :: l) i =
      f4ReflectionIndex (Fin.castAdd 44 j) (F4.geckWeylRootIndex valid_F4 l i) := by
  calc
    _ = (F4.simplyConnectedRootDatum valid_F4).reflectionPerm (F4.simpleIndex valid_F4 j)
        (F4.geckWeylRootIndex valid_F4 l i) := F4.geckWeylRootIndex_cons valid_F4 j l i
    _ = _ := by
      rw [simplyConnectedRootDatum_F4, simpleIndex_F4 valid_F4 j]
      exact f4SimplyConnectedRootDatum_reflectionPerm _ _

end TauCeti.DynkinType
