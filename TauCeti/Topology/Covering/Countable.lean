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
  obtain ⟨T, hTc, hTcover⟩ := isOpen_iUnion_countable U hU
  have := hTc.to_subtype
  let V : (Σ x : T, p ⁻¹' {(x : X)}) → Set E := fun a ↦ S a.1 a.2
  have hVo (a) : IsOpen (V a) := hSo a.1 a.2
  have hVsc (a) : SecondCountableTopology (V a) := by
    have hlocal := hp.isLocalHomeomorph.comp (hVo a).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    have hemb := hlocal.isOpenEmbedding_of_injective
      (fun e e' h ↦ Subtype.ext (hSi a.1 a.2 e.property e'.property h))
    exact hemb.isEmbedding.secondCountableTopology
  refine secondCountableTopology_of_isOpen_cover V hVo ?_ hVsc fun a ↦ ?_
  · refine eq_univ_of_forall fun e ↦ ?_
    have hx : p e ∈ ⋃ i ∈ T, U i := hTcover ▸ mem_iUnion.mpr ⟨p e, hxU (p e)⟩
    obtain ⟨x, hxT, hex⟩ := mem_iUnion₂.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hSU x ▸ hex : e ∈ ⋃ j, S x j)
    exact mem_iUnion.mpr ⟨⟨⟨x, hxT⟩, j⟩, hj⟩
  · have hsub : {b | (V a ∩ V b).Nonempty} ⊆
        ⋃ y : T, Sigma.mk y '' {j | (V a ∩ S y j).Nonempty} := by
      rintro ⟨y, j⟩ hb
      exact mem_iUnion.mpr ⟨y, j, hb, rfl⟩
    refine Countable.mono hsub (countable_iUnion fun y ↦ Countable.image ?_ _)
    have := (hVsc a).to_separableSpace
    have hcount := Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun j ↦ ((↑) : V a → E) ⁻¹' S y j)
      (a := {j | (V a ∩ S y j).Nonempty})
      (fun i _ j _ hij ↦ ((hSd y hij).preimage _))
      (fun j _ ↦ (hSo y j).preimage continuous_subtype_val)
      (fun j ⟨e, he, he'⟩ ↦ ⟨⟨e, he⟩, he'⟩)
    exact hcount

/-- The fibres of a covering map with connected total space over a second-countable space are
countable. -/
theorem _root_.IsCoveringMap.countable_fiber [SecondCountableTopology X] [PreconnectedSpace E]
    (hp : IsCoveringMap p) (x : X) : Countable (p ⁻¹' {x}) := by
  have := hp.secondCountableTopology
  have := (hp x).discreteTopology_fiber
  exact separableSpace_iff_countable.mp inferInstance

end TauCeti
