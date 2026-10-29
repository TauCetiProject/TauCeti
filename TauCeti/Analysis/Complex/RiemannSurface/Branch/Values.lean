/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Ramification
import TauCeti.Analysis.Complex.RiemannSurface.OpenMapping
public import Mathlib.Topology.Covering.Basic

/-!
# Coverings away from branch values

For a finite holomorphic map of connected Riemann surfaces, the branch values are the images
of the points of local multiplicity greater than one. With compact source this is a finite
closed set, and the map is a covering over its complement. Every fibre of this covering has
cardinality equal to the analytic degree of the map. Conversely, a branch value cannot admit
an evenly covered neighbourhood: a local homeomorphism has local multiplicity one.

These results supply the unbranched covering obtained by removing neighbourhoods of branch
values, used in the topological proof of the Riemann--Hurwitz formula. The restriction is
Mathlib's `Set.restrictPreimage`, so the ordinary covering-map API applies without a new
carrier or notion of covering.

The covering and its sheet count use local multiplicity, finite fibres, and the analytic
fibre-sum degree. Euler characteristic and topological genus are needed for the subsequent
Riemann--Hurwitz application, rather than for these covering results.

## Main declarations

* `FiniteHolomorphicMap.branchValues`: the set of branch values.
* `FiniteHolomorphicMap.isLocalHomeomorphOn_iff`: local homeomorphy is equivalent to local
  multiplicity one at every point of the specified source set.
* `FiniteHolomorphicMap.isCoveringMapOn_iff`: a map with compact source is a covering on
  precisely the subsets disjoint from its branch values.
* `FiniteHolomorphicMap.isCoveringMap_restrictPreimage_branchValues_compl`: the covering
  obtained by deleting the branch values and their preimages.
* `FiniteHolomorphicMap.card_fiber_eq_degree_iff`: a fibre has as many points as the degree
  exactly when its value is not a branch value.
* `FiniteHolomorphicMap.ncard_fiber_restrictPreimage_branchValues_compl`: every fibre of
  the restricted covering has cardinality equal to the analytic degree.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§4 and 17.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.

The covering construction uses Mathlib's
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`.
-/

public section

open Filter Function Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- The branch values of a finite holomorphic map: the images of the points with local
multiplicity greater than one. -/
def branchValues (f : FiniteHolomorphicMap X Y) : Set Y :=
  f '' {x | 1 < localMultiplicity f x}

/-- A value is a branch value exactly when some point above it is ramified. -/
@[simp]
theorem mem_branchValues_iff (f : FiniteHolomorphicMap X Y) (y : Y) :
    y ∈ f.branchValues ↔ ∃ x, f x = y ∧ 1 < localMultiplicity f x := by
  simp [branchValues, and_comm]

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] [PreconnectedSpace X]

/-- Away from branch values, every point of the fibre has local multiplicity one. -/
-- Simplify nonmembership before `mem_branchValues_iff` rewrites the inner membership.
@[simp↓]
theorem notMem_branchValues_iff (f : FiniteHolomorphicMap X Y) (y : Y) :
    y ∉ f.branchValues ↔ ∀ x, f x = y → localMultiplicity f x = 1 := by
  rw [mem_branchValues_iff]
  simp only [not_exists, not_and]
  exact forall_congr' fun x ↦ imp_congr_right fun _ ↦ by
    have := localMultiplicity_pos f x
    omega

/-- A finite holomorphic map is locally homeomorphic on a set exactly when its local
multiplicities on that set are one. No compactness assumption is needed. -/
theorem isLocalHomeomorphOn_iff (f : FiniteHolomorphicMap X Y) (s : Set X) :
    IsLocalHomeomorphOn f s ↔ ∀ x ∈ s, localMultiplicity f x = 1 := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨e, hxe, he⟩ := h x hx
    apply (localMultiplicity_eq_one_iff (.of_forall fun z ↦ f.holomorphic z)).2
    exact ⟨e.source, e.open_source.mem_nhds hxe, he.symm ▸ e.injOn⟩
  · rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
    intro x hx
    obtain ⟨U, hU, hinj⟩ :=
      (localMultiplicity_eq_one_iff (.of_forall fun z ↦ f.holomorphic z)).1 (h x hx)
    refine ⟨interior U, isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hU),
      .of_continuous_injective_isOpenMap
        (f.holomorphic.continuous.comp continuous_subtype_val)
        ((hinj.mono interior_subset).injective) ?_⟩
    exact (isOpenMap_of_forall_not_eventuallyConst f.holomorphic f.not_eventuallyConst).comp
      isOpen_interior.isOpenMap_subtype_val

variable [CompactSpace X]

/-- There are finitely many branch values for a finite holomorphic map with compact source. -/
theorem finite_branchValues (f : FiniteHolomorphicMap X Y) : f.branchValues.Finite :=
  f.finite_setOf_one_lt_localMultiplicity.image f

/-- The branch values form a closed set. -/
theorem isClosed_branchValues [T1Space Y] (f : FiniteHolomorphicMap X Y) :
    IsClosed f.branchValues :=
  f.finite_branchValues.isClosed

/-- The complement of the branch values is open. -/
theorem isOpen_branchValues_compl [T1Space Y] (f : FiniteHolomorphicMap X Y) :
    IsOpen f.branchValuesᶜ :=
  f.isClosed_branchValues.isOpen_compl

variable [T2Space X] [T2Space Y]

/-- A finite holomorphic map with compact source is a covering over exactly those subsets of
the target that contain no branch values. In particular it is not a covering at a branch value. -/
theorem isCoveringMapOn_iff (f : FiniteHolomorphicMap X Y) (s : Set Y) :
    IsCoveringMapOn f s ↔ s ⊆ f.branchValuesᶜ := by
  refine ⟨fun h y hy ↦ ?_, fun h ↦ ?_⟩
  · rw [mem_compl_iff, f.notMem_branchValues_iff]
    intro x hxy
    exact (f.isLocalHomeomorphOn_iff _).1 h.isLocalHomeomorphOn x
      (mem_preimage.2 (hxy.symm ▸ hy))
  · apply f.holomorphic.continuous.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun y _ ↦ f.finite_fiber y)
    rw [f.isLocalHomeomorphOn_iff]
    intro x hx
    exact (f.notMem_branchValues_iff (f x)).1 (h hx) x rfl

/-- Deleting the branch values and their preimages gives an ordinary covering map. -/
theorem isCoveringMap_restrictPreimage_branchValues_compl (f : FiniteHolomorphicMap X Y) :
    IsCoveringMap (f.branchValuesᶜ.restrictPreimage f) :=
  ((f.isCoveringMapOn_iff _).2 subset_rfl).isCoveringMap_restrictPreimage

variable [PreconnectedSpace Y]

/-- A fibre has cardinality equal to the degree exactly when it contains no ramification
points. Thus the covering away from branch values has as many sheets as the analytic degree. -/
theorem card_fiber_eq_degree_iff (f : FiniteHolomorphicMap X Y) (y : Y) :
    (f.finite_fiber y).toFinset.card = degree f ↔ y ∉ f.branchValues := by
  classical
  have hcount := card_fiber_add_sum_localMultiplicity_sub_one f y
  rw [f.notMem_branchValues_iff]
  refine ⟨fun h x hxy ↦ ?_, fun h ↦ ?_⟩
  · have hsum : ∑ x ∈ (f.finite_fiber y).toFinset, (localMultiplicity f x - 1) = 0 := by
      omega
    have hx := Finset.sum_eq_zero_iff.1 hsum x ((f.finite_fiber y).mem_toFinset.2 hxy)
    have := localMultiplicity_pos f x
    omega
  · have hsum : ∑ x ∈ (f.finite_fiber y).toFinset, (localMultiplicity f x - 1) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [h x ((f.finite_fiber y).mem_toFinset.1 hx), Nat.sub_self]
    omega

/-- Every fibre of the covering obtained by deleting branch values has cardinality equal to
the analytic degree of the original map. -/
theorem ncard_fiber_restrictPreimage_branchValues_compl (f : FiniteHolomorphicMap X Y)
    (y : ↥(f.branchValuesᶜ)) :
    ((f.branchValuesᶜ.restrictPreimage f) ⁻¹' {y}).ncard = degree f := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.image_val_preimage_restrictPreimage, Set.image_singleton,
    Set.ncard_eq_toFinset_card _ (f.finite_fiber y)]
  exact (f.card_fiber_eq_degree_iff y).2 y.property

end TauCeti.RiemannSurface.FiniteHolomorphicMap

end
