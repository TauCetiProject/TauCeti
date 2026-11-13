/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Groupoid.Effective
public import TauCeti.Topology.Covering.Degree
public import TauCeti.Topology.Covering.Proper

/-!
# The covering of ineffective arrows

For a quiver with proper source-target map, the source map on closed ineffective arrows is
proper. If the total-arrow space is Hausdorff and source is locally homeomorphic, this restricted
source map is a covering map.

For topological groupoids, `TauCeti.ineffectiveKernelEquivFiber` identifies each ineffective kernel
with a source fibre. Its order equals the covering degree and is locally constant on objects and
the coarse quotient when ineffective arrows are closed. The smooth closedness theorem and
`TauCeti.isLocallyConstant_card_ineffectiveKernel` are in
`TauCeti.Geometry.Manifold.Etale.IneffectiveKernel`.

Closedness is a separate hypothesis here: it need not hold for arbitrary topological étale
groupoids.

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

/-- In a quiver with proper source-target map, source restricted to the ineffective arrows
is proper whenever the ineffective arrows form a closed set. -/
theorem isProperMap_source_ineffectiveArrows
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) :
    IsProperMap fun a : ineffectiveArrows C ↦ (a : Quiver.Total C).left := by
  apply isProperMap_of_comp_of_inj
    ((continuous_fst.comp hp.continuous).comp continuous_subtype_val)
    (continuous_id.prodMk continuous_id) ?_
    (fun _ _ h ↦ congrArg Prod.fst h)
  convert hp.comp hclosed.isClosedEmbedding_subtypeVal.isProperMap using 1
  funext a
  exact Prod.ext rfl (left_eq_right_of_mem_ineffectiveArrows a.property)

/-- In a quiver with Hausdorff total-arrow space, locally homeomorphic source and proper
source-target map, source restricted to closed ineffective arrows is a covering map. -/
theorem isCoveringMap_source_ineffectiveArrows [T2Space (Quiver.Total C)]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) :
    IsCoveringMap fun a : ineffectiveArrows C ↦ (a : Quiver.Total C).left := by
  have hloc := hs.comp isOpen_ineffectiveArrows.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  exact hloc.isCoveringMap_of_isProperMap (isProperMap_source_ineffectiveArrows hp hclosed)

end Quiver

section Groupoid

variable {C : Type*} [Groupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C] [T2Space (Quiver.Total C)]

/-- In a Hausdorff-arrow topological groupoid with locally homeomorphic source and proper
source-target map, the ineffective-kernel order equals the covering degree when ineffective
arrows are closed. -/
theorem card_ineffectiveKernel_eq_degree
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) (x : C) :
    Nat.card (ineffectiveKernel hs x) =
      (isCoveringMap_source_ineffectiveArrows hs hp hclosed).degree x := by
  rw [IsCoveringMap.degree_apply]
  exact Nat.card_congr (ineffectiveKernelEquivFiber hs x)

/-- In a Hausdorff-arrow topological groupoid with locally homeomorphic source and proper
source-target map, the ineffective-kernel order on objects is locally constant if ineffective
arrows are closed. -/
theorem isLocallyConstant_card_ineffectiveKernel_of_isClosed
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) :
    IsLocallyConstant fun x : C ↦ Nat.card (ineffectiveKernel hs x) := by
  have heq : (fun x : C ↦ Nat.card (ineffectiveKernel hs x)) =
      (isCoveringMap_source_ineffectiveArrows hs hp hclosed).degree :=
    funext (card_ineffectiveKernel_eq_degree hs hp hclosed)
  rw [heq]
  exact LocallyConstant.isLocallyConstant _

/-- In a Hausdorff-arrow topological groupoid with locally homeomorphic source and proper
source-target map, the coarse ineffective-kernel order is locally constant if ineffective
arrows are closed. -/
theorem isLocallyConstant_coarseCardIneffectiveKernel_of_isClosed
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) :
    IsLocallyConstant (coarseCardIneffectiveKernel hs) :=
  (isLocallyConstant_coarseCardIneffectiveKernel_iff hs).mpr
    (isLocallyConstant_card_ineffectiveKernel_of_isClosed hs hp hclosed)

end Groupoid

end TauCeti
