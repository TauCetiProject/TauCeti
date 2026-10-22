/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import TauCeti.Topology.Constructions.Basic

/-!
# Quotient projections in the category of topological spaces

The canonical projection to the quotient by a setoid, bundled as a morphism in `TopCat`, and
the open set of the quotient given by the image of an open set closed under the setoid.
-/

public section

open CategoryTheory TopologicalSpace

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

variable {s} in
/-- The image of an open set closed under `s`, as an open set of the quotient by `s`. -/
-- Expose the carrier so membership in the image can be destructured downstream.
@[expose]
def saturatedOpen (V : Opens X) (hV : ∀ ⦃w v⦄, w ∈ V → s w v → v ∈ V) :
    Opens (Quotient s) :=
  ⟨Quotient.mk s '' V, Setoid.isOpen_image_quotient_mk s V.isOpen hV⟩

variable {s} in
/-- The points over the image of an open set closed under `s` are the points of that set. -/
theorem mem_map_saturatedOpen (V : Opens X) (hV : ∀ ⦃w v⦄, w ∈ V → s w v → v ∈ V)
    {w : X} : w ∈ (Opens.map (quotientMk s)).obj (saturatedOpen V hV) ↔ w ∈ V := by
  rw [Opens.mem_map, quotientMk_apply]
  exact ⟨fun ⟨v, hv, hvw⟩ ↦ hV hv (Quotient.exact hvw), fun hw ↦ ⟨w, hw, rfl⟩⟩

end TauCeti.TopCat
