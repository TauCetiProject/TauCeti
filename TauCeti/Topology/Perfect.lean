/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Separation.Hausdorff

/-!
# Perfect sets and spaces: homeomorphic images, products, and discrete subsets

A homeomorphism carries perfect sets onto perfect sets (`Homeomorph.perfect_image`) and perfect
spaces onto perfect spaces (`Homeomorph.perfectSpace`), so statements about perfect sets and spaces
can be transported along homeomorphisms of the ambient spaces.

In any topological space, removing a subset `S` whose trace `U ∩ S` is discrete from a preperfect
set `U` leaves `U \ S` dense in `U` (`Preperfect.subset_closure_sdiff_of_isDiscrete`, specialized to
open sets in perfect spaces by `IsOpen.subset_closure_sdiff_of_isDiscrete`), so continuous maps into
a Hausdorff space are determined on `U` by their values on `U \ S`
(`Preperfect.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete`,
`IsOpen.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete`). When `U` is open, `U \ S` is also a
punctured neighbourhood of every point of `U ∩ S` (`IsOpen.sdiff_mem_nhdsNE_of_isDiscrete`).

A product of infinitely many nontrivial topological spaces has no isolated points: a
neighbourhood of a point in the product topology constrains only finitely many coordinates, so
changing a coordinate outside them moves the point without leaving the neighbourhood. No
separation axiom is needed. In particular Cantor space `ℕ → Bool` and Baire space `ℕ → ℕ` are
perfect.

## Main results

* `Homeomorph.perfect_image`, `Homeomorph.perfectSpace`: perfect sets and perfect spaces are
  preserved by homeomorphisms.
* `IsOpen.sdiff_mem_nhdsNE_of_isDiscrete`,
  `Preperfect.subset_closure_sdiff_of_isDiscrete`,
  `IsOpen.subset_closure_sdiff_of_isDiscrete`,
  `Preperfect.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete`,
  `IsOpen.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete`: punctured neighbourhoods, density, and
  continuous-extension uniqueness across discrete subsets of preperfect sets and open sets in
  perfect spaces.
* `TauCeti.perfectSpace_pi`: a product of infinitely many nontrivial spaces is a perfect space.

## References

* The argument for Cantor space follows `accPt_univ_natBool` in
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Descriptive/PerfectAntichain.lean`; here it is stated for arbitrary infinite
  products of nontrivial spaces.
-/

public section

open Filter Set Topology

universe u v

namespace Homeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private theorem perfect_image_of_perfect (h : X ≃ₜ Y) {C : Set X} (hC : Perfect C) :
    Perfect (h '' C) :=
  ⟨h.isClosed_image.2 hC.closed, by
    rintro _ ⟨x, hx, rfl⟩
    simpa [Filter.map_principal] using
      AccPt.map (hC.acc x hx) h.continuous.continuousAt h.injective⟩

/-- The image of a set under a homeomorphism is perfect exactly when the set is perfect. -/
@[simp]
theorem perfect_image (h : X ≃ₜ Y) {C : Set X} : Perfect (h '' C) ↔ Perfect C := by
  refine ⟨fun hC => ?_, perfect_image_of_perfect h⟩
  simpa [Set.image_image] using perfect_image_of_perfect h.symm hC

/-- A homeomorphic image of a perfect space is a perfect space. -/
protected theorem perfectSpace [PerfectSpace X] (h : X ≃ₜ Y) : PerfectSpace Y := by
  have hU : Perfect (h '' (univ : Set X)) :=
    h.perfect_image.2 (PerfectSpace.univ_perfect (α := X))
  rw [Set.image_univ, h.surjective.range_eq] at hU
  exact ⟨hU.acc⟩

end Homeomorph

private theorem sdiff_mem_nhdsWithin_of_isDiscrete {X : Type u} [TopologicalSpace X] {U S : Set X}
    (hS : IsDiscrete (U ∩ S)) {x : X} (hxU : x ∈ U) (hxS : x ∈ S) :
    U \ S ∈ 𝓝[≠] x ⊓ 𝓟 U := by
  have hdisj : (U ∩ S)ᶜ ∈ 𝓝[≠] x :=
    disjoint_principal_right.1 (disjoint_iff.2 (isDiscrete_iff_nhdsNE.1 hS x ⟨hxU, hxS⟩))
  filter_upwards [mem_inf_of_left hdisj, mem_inf_of_right (mem_principal_self U)] with y hyS hyU
  exact ⟨hyU, fun h ↦ hyS ⟨hyU, h⟩⟩

/-- If `U` is open and `U ∩ S` is discrete, then `U \ S` is a punctured neighbourhood of every point
of `U ∩ S`. -/
theorem IsOpen.sdiff_mem_nhdsNE_of_isDiscrete {X : Type u} [TopologicalSpace X] {U S : Set X}
    (hU : IsOpen U) (hS : IsDiscrete (U ∩ S)) {x : X} (hxU : x ∈ U) (hxS : x ∈ S) :
    U \ S ∈ 𝓝[≠] x := by
  have hle : 𝓝[≠] x ≤ 𝓝[≠] x ⊓ 𝓟 U :=
    le_inf le_rfl (le_principal_iff.2 (nhdsWithin_le_nhds (hU.mem_nhds hxU)))
  exact hle (sdiff_mem_nhdsWithin_of_isDiscrete hS hxU hxS)

/-- Every preperfect set `U` is contained in the closure of `U \ S` whenever `U ∩ S` is discrete. -/
theorem Preperfect.subset_closure_sdiff_of_isDiscrete {X : Type u} [TopologicalSpace X]
    {U S : Set X} (hU : Preperfect U) (hS : IsDiscrete (U ∩ S)) :
    U ⊆ closure (U \ S) := fun x hx ↦ by
  by_cases hxS : x ∈ S
  · rw [mem_closure_iff_nhdsWithin_neBot]
    exact Filter.NeBot.mono (hU x hx) (le_inf (inf_le_left.trans nhdsWithin_le_nhds)
      (le_principal_iff.2 (sdiff_mem_nhdsWithin_of_isDiscrete hS hx hxS)))
  · exact subset_closure ⟨hx, hxS⟩

/-- In a perfect space, every open set `U` is contained in the closure of `U \ S` whenever `U ∩ S`
is discrete. -/
theorem IsOpen.subset_closure_sdiff_of_isDiscrete {X : Type u} [TopologicalSpace X]
    [PerfectSpace X] {U S : Set X} (hU : IsOpen U) (hS : IsDiscrete (U ∩ S)) :
    U ⊆ closure (U \ S) :=
  hU.preperfect.subset_closure_sdiff_of_isDiscrete hS

/-- **Uniqueness of continuous extensions across a discrete set.** If `U` is preperfect and `U ∩ S`
is discrete, any two maps into a `T₂` space that are continuous on `U` and agree on `U \ S` agree on
all of `U`. -/
theorem Preperfect.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {g₁ g₂ : X → Y} {U S : Set X}
    (hU : Preperfect U) (hS : IsDiscrete (U ∩ S)) (hg₁ : ContinuousOn g₁ U)
    (hg₂ : ContinuousOn g₂ U) (heq : EqOn g₁ g₂ (U \ S)) : EqOn g₁ g₂ U :=
  heq.of_subset_closure hg₁ hg₂ sdiff_subset (hU.subset_closure_sdiff_of_isDiscrete hS)

/-- **Uniqueness of continuous extensions across a discrete set in a perfect space.** If `U` is open
in a perfect space and `U ∩ S` is discrete, any two maps into a `T₂` space that are continuous on
`U` and agree on `U \ S` agree on all of `U`. -/
theorem IsOpen.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PerfectSpace X] [TopologicalSpace Y] [T2Space Y] {g₁ g₂ : X → Y}
    {U S : Set X} (hU : IsOpen U) (hS : IsDiscrete (U ∩ S)) (hg₁ : ContinuousOn g₁ U)
    (hg₂ : ContinuousOn g₂ U) (heq : EqOn g₁ g₂ (U \ S)) : EqOn g₁ g₂ U :=
  hU.preperfect.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete hS hg₁ hg₂ heq

namespace TauCeti

/-- **A product of infinitely many nontrivial spaces is perfect**, with no separation assumption on
the factors. In particular Cantor space `ℕ → Bool` and Baire space `ℕ → ℕ` are perfect. -/
instance perfectSpace_pi {ι : Type u} {π : ι → Type v} [∀ i, TopologicalSpace (π i)]
    [Infinite ι] [∀ i, Nontrivial (π i)] : PerfectSpace (∀ i, π i) := by
  classical
  refine ⟨preperfect_iff_nhds.2 fun x _ U hU => ?_⟩
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, V, hV, hVU⟩ := hU
  obtain ⟨n, -, hn⟩ := infinite_univ.exists_notMem_finite hI
  obtain ⟨z, hz⟩ := exists_ne (x n)
  refine ⟨Function.update x n z, ⟨hVU fun i hi => ?_, trivial⟩, fun h => hz ?_⟩
  · rw [Function.update_of_ne fun h : i = n => hn (h ▸ hi)]
    exact mem_of_mem_nhds (hV i)
  · simpa using congrFun h n

end TauCeti
