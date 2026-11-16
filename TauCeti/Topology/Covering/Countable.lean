/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Bases
public import TauCeti.Topology.Covering.Comp

/-!
# Connected coverings of second-countable spaces are second countable

Let `p : E → X` be a covering map with `E` connected and `X` second countable. Then `E` is
second countable. No local connectedness, Hausdorff property or countability of the fibres is
assumed: the countability of the fibres is a consequence (`IsCoveringMap.countable_fiber`).

The proof is a chain argument. Countably many evenly covered open sets `U` cover `X`, and the
sheets over them are open subsets of `E`, each homeomorphic to its base `U` and hence second
countable. Two sheets over the same `U` are disjoint, so a given sheet meets only countably many
sheets over each `U`: they cut out pairwise disjoint nonempty open subsets of a separable space.
Thus every sheet has countably many neighbouring sheets, the sheets reachable from a fixed one by
finite chains of overlapping sheets are countably many, and their union is open and closed in `E`.
By connectedness it is all of `E`, a countable union of open second-countable subspaces
(`TauCeti.secondCountableTopology_of_isOpen_cover`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 4.40.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3.
-/

public section

open Set Topology TopologicalSpace

namespace TauCeti

variable {E : Type*} [TopologicalSpace E]

variable {X : Type*} [TopologicalSpace X] {p : E → X}

/-- **Connected coverings of second-countable spaces are second countable.** The total space of
a covering map with connected total space over a second-countable space is second countable. -/
theorem _root_.IsCoveringMap.secondCountableTopology [SecondCountableTopology X]
    [PreconnectedSpace E] (hp : IsCoveringMap p) : SecondCountableTopology E := by
  choose U hxU hU S hSo hSi _ _ hSd hSU using fun x ↦ (hp x).exists_sheets
  refine secondCountableTopology_of_preimage_isOpen_cover p U hU
    (range_subset_iff.mpr fun e ↦ mem_iUnion.mpr ⟨p e, hxU (p e)⟩) S hSo (fun x j ↦ ?_) hSd
    (fun x ↦ (hSU x).subset)
  have hlocal := hp.isLocalHomeomorph.comp (hSo x j).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hemb := hlocal.isOpenEmbedding_of_injective
    (fun e e' h ↦ Subtype.ext (hSi x j e.property e'.property h))
  exact hemb.isEmbedding.secondCountableTopology

/-- The fibres of a covering map with connected total space over a second-countable space are
countable. -/
theorem _root_.IsCoveringMap.countable_fiber [SecondCountableTopology X] [PreconnectedSpace E]
    (hp : IsCoveringMap p) (x : X) : Countable (p ⁻¹' {x}) := by
  have := hp.secondCountableTopology
  have := (hp x).discreteTopology_fiber
  exact separableSpace_iff_countable.mp inferInstance

end TauCeti
