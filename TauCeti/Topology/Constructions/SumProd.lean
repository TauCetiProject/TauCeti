/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Interiors and fibres in product spaces

A subset of a product has empty interior if its vertical fibres over a dense set of base
points have empty interior. This lets fibrewise empty-interior results apply to subsets of
arbitrary topological products, without countability, separation, or finite-dimensionality
assumptions on either factor.
In particular, graphs with values in a space without isolated points have empty interior.

The file also records the underlying function of the homeomorphism between functions on a
sum type and pairs of functions.
-/

public section

open Filter Set Topology

/-- The sum-to-product homeomorphism has the same underlying function as the corresponding
coordinate equivalence. -/
theorem Homeomorph.coe_sumArrowHomeomorphProdArrow {X ι ι' : Type*} [TopologicalSpace X] :
    ⇑(sumArrowHomeomorphProdArrow (X := X) (ι := ι) (ι' := ι')) =
      ⇑(Equiv.sumArrowEquivProdArrow ι ι' X) := (rfl)

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A subset of a product has empty interior if its vertical fibres over a dense set of base
points have empty interior. -/
theorem interior_eq_empty_of_dense_setOf_interior_preimage_prodMk_eq_empty {s : Set (X × Y)}
    (hs : Dense {x | interior (Prod.mk x ⁻¹' s) = ∅}) : interior s = ∅ := by
  by_contra h
  obtain ⟨_, hx, ⟨x, y⟩, hxy, rfl⟩ := hs.exists_mem_open (isOpenMap_fst _ isOpen_interior)
    ((nonempty_iff_ne_empty.mpr h).image _)
  exact hx.le (preimage_interior_subset_interior_preimage (Continuous.prodMk_right x) hxy)

/-- A subset of a product has empty interior if every vertical fibre has empty interior. -/
theorem interior_eq_empty_of_forall_interior_preimage_prodMk_eq_empty {s : Set (X × Y)}
    (hs : ∀ x, interior (Prod.mk x ⁻¹' s) = ∅) : interior s = ∅ :=
  interior_eq_empty_of_dense_setOf_interior_preimage_prodMk_eq_empty <| by simp [hs]

/-- A graph with values in a space without isolated points has empty interior, even when
neither the function nor its domain is open or continuous. -/
@[simp]
theorem _root_.Set.interior_graphOn [∀ y : Y, NeBot (𝓝[≠] y)] (s : Set X) (f : X → Y) :
    interior (s.graphOn f) = ∅ := by
  refine interior_eq_empty_of_forall_interior_preimage_prodMk_eq_empty fun x ↦ ?_
  have hsub : Prod.mk x ⁻¹' s.graphOn f ⊆ {f x} := fun y hy ↦ (mem_graphOn.mp hy).2.symm
  simpa using interior_mono hsub

end TauCeti
