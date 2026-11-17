/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Basic lemmas on `TopCat`

Evaluation lemmas for functors defined in `Mathlib.Topology.Category.TopCat.Basic`.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.TopCat

/-- The functor `TopCat.discrete` acts on morphisms by the underlying function. -/
@[simp]
lemma discrete_map_apply {X Y : Type u} (f : X ⟶ Y) (x : X) :
    _root_.TopCat.discrete.map f x = f x := (rfl)

end TauCeti.TopCat
