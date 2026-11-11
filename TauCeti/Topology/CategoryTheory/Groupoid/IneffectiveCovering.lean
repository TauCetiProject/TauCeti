/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective

/-!
# The covering of ineffective arrows

When the ineffective arrows of a proper étale groupoid form a closed set, their source map
is a proper covering. Its fibre over an object is the full ineffective kernel, not a quotient
of that kernel. This identifies the ineffective-kernel order with a covering degree.

Closedness of ineffective arrows is a separate hypothesis here: it need not hold for arbitrary
topological étale groupoids.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

section Quiver

variable {C : Type*} [Quiver C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]

/-- If ineffective arrows are closed, their source map is proper: on this closed subspace,
the proper source-target map factors through the diagonal of the object space. -/
theorem isProperMap_source_ineffectiveArrows
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) :
    IsProperMap fun a : ineffectiveArrows C ↦ (a : Quiver.Total C).left := by
  apply isProperMap_of_comp_of_inj
    (hs.comp continuous_subtype_val)
    (continuous_id.prodMk continuous_id) ?_
    (fun _ _ h ↦ congrArg Prod.fst h)
  convert hp.comp hclosed.isClosedEmbedding_subtypeVal.isProperMap using 1
  funext a
  exact Prod.ext rfl (left_eq_right_of_mem_ineffectiveArrows a.property)

/-- The ineffective arrows of a proper étale quiver, when closed, form a finite-fibre
covering of the objects under source. The number of sheets may vary between components. -/
theorem isCoveringMap_source_ineffectiveArrows [T2Space (Quiver.Total C)]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) :
    IsCoveringMap fun a : ineffectiveArrows C ↦ (a : Quiver.Total C).left := by
  have hloc := hs.comp isOpen_ineffectiveArrows.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hproper := isProperMap_source_ineffectiveArrows hs.continuous hp hclosed
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn _ hloc.isLocalHomeomorphOn
  intro x _
  exact (hproper.isCompact_preimage isCompact_singleton).finite
    (hloc.isLocallyInjective.isDiscrete_preimage_singleton x)

end Quiver

end TauCeti
