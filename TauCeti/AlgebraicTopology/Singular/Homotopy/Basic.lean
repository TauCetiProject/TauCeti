/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Homotopies of maps of topological pairs on singular simplicial sets

A homotopy between maps of topological pairs induces a homotopy between the induced morphisms of
the corresponding pairs of singular simplicial sets, that is, an `SSetPair.Homotopy`.  It is given
on the subspace and on the ambient space by Mathlib's `TopCat.Homotopy.toSSet`, and the two agree
on the subspace because the homotopy is one of maps of pairs.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory

universe w

namespace TopPair.Homotopy

variable {P P' : TopPair.{w}} {f g : P ⟶ P'} (H : Homotopy f g)

/-- The homotopy between the induced maps of pairs of singular simplicial sets. -/
@[no_expose]
def toSSetPair : SSetPair.Homotopy (TopPair.toSSetPair.map f) (TopPair.toSSetPair.map g) where
  left := H.snd.toSSet
  right := H.fst.toSSet
  w := by
    simp [TopCat.Homotopy.toSSet, ← whisker_exchange_assoc, ← Functor.map_comp, H.w]

@[simp] lemma toSSetPair_left : H.toSSetPair.left = H.snd.toSSet := (rfl)

@[simp] lemma toSSetPair_right : H.toSSetPair.right = H.fst.toSSet := (rfl)

end TopPair.Homotopy
