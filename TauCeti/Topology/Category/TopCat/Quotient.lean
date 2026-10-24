/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Quotient projections in the category of topological spaces

The canonical projection to the quotient by a setoid, bundled as a morphism in `TopCat`.
-/

public section

open CategoryTheory

namespace TauCeti.TopCat

variable {X : Type*} [TopologicalSpace X] (s : Setoid X)

/-- The continuous projection from a topological space to its quotient by a setoid. -/
-- Expose the projection so inverse-image section domains compute to quotient fibres.
@[expose]
def quotientMk : TopCat.of X ⟶ TopCat.of (Quotient s) :=
  TopCat.ofHom ⟨Quotient.mk s, continuous_quotient_mk'⟩

/-- The quotient projection sends a point to its equivalence class. -/
@[simp]
-- Avoid indexing on the two definitionally equal presentations of the continuous-map type.
theorem quotientMk_apply (x : X) :
    DFunLike.coe (F := no_index _) (ConcreteCategory.hom (quotientMk s)) x =
      Quotient.mk s x := rfl

end TauCeti.TopCat
