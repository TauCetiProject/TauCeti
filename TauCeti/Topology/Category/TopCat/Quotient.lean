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

end TauCeti.TopCat

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X] {s : Setoid X}

/-- The image of an open set closed under `s`, as an open set of the quotient by `s`. -/
def imageQuotientMk (V : Opens X) (hV : ∀ ⦃w v⦄, w ∈ V → s w v → v ∈ V) :
    Opens (Quotient s) :=
  ⟨Quotient.mk s '' V, Setoid.isOpen_image_quotient_mk s V.isOpen hV⟩

/-- The carrier of `V.imageQuotientMk hV` is the image of `V` in the quotient. -/
@[simp]
theorem coe_imageQuotientMk (V : Opens X) (hV : ∀ ⦃w v⦄, w ∈ V → s w v → v ∈ V) :
    (V.imageQuotientMk hV : Set (Quotient s)) = Quotient.mk s '' V :=
  (rfl)

/-- A point of the quotient lies in `V.imageQuotientMk hV` exactly when it is the class of a
point of `V`. -/
theorem mem_imageQuotientMk (V : Opens X) (hV : ∀ ⦃w v⦄, w ∈ V → s w v → v ∈ V)
    {z : Quotient s} : z ∈ V.imageQuotientMk hV ↔ ∃ w ∈ V, Quotient.mk s w = z :=
  Iff.rfl

/-- The class of a point lies in the image of an open set closed under `s` exactly when the
point lies in that set. -/
@[simp]
theorem mk_mem_imageQuotientMk (V : Opens X) (hV : ∀ ⦃w v⦄, w ∈ V → s w v → v ∈ V)
    {w : X} : Quotient.mk s w ∈ V.imageQuotientMk hV ↔ w ∈ V := by
  rw [mem_imageQuotientMk]
  exact ⟨fun ⟨v, hv, hvw⟩ ↦ hV hv (Quotient.exact hvw), fun hw ↦ ⟨w, hw, rfl⟩⟩

/-- The points over the image of an open set closed under `s` are the points of that set. -/
@[simp]
theorem mem_map_imageQuotientMk (V : Opens X) (hV : ∀ ⦃w v⦄, w ∈ V → s w v → v ∈ V)
    {w : X} :
    w ∈ (Opens.map (TauCeti.TopCat.quotientMk s)).obj (V.imageQuotientMk hV) ↔ w ∈ V := by
  rw [Opens.mem_map, TauCeti.TopCat.quotientMk_apply, mk_mem_imageQuotientMk]

end TopologicalSpace.Opens
