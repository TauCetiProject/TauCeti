/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Baire.BaireMeasurable

/-!
# Meagre sets in local coordinates

An open partial homeomorphism preserves meagreness on its source. In particular, a meagre
set in an open coordinate domain remains meagre in the ambient space after applying a chart
inverse. The source restriction is essential: the function outside the source is unconstrained.
-/

public section

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open partial homeomorphism sends a meagre subset of its source to a meagre set in the
ambient target space. -/
theorem isMeagre_image (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hs : IsMeagre s) (hse : s ⊆ e.source) : IsMeagre (e '' s) := by
  have h := e.isEmbedding_restrict.isInducing.isMeagre_image
    (hs.preimage_of_isOpenMap continuous_subtype_val e.open_source.isOpenMap_subtype_val)
  simpa only [image_domRestrict, inter_eq_left.mpr hse, e.toFun_eq_coe] using h

end OpenPartialHomeomorph
