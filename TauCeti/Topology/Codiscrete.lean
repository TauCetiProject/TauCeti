/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Open sets, punctured neighborhoods, and density for `Filter.codiscreteWithin`

Let `U` be a subset of a topological space `X`. Mathlib's `isClosed_sdiff_of_codiscreteWithin`
shows that removing a set `t ∈ Filter.codiscreteWithin U` from a closed set `U` yields a closed
set `U \ t`. This file supplies the dual punctured-neighborhood, open-set, and density properties
for sets `s ∈ Filter.codiscreteWithin U` and their complement specializations
`sᶜ ∈ Filter.codiscreteWithin U`:

* `TauCeti.nhdsNE_le_codiscreteWithin`, `TauCeti.inter_mem_nhdsNE_of_mem_codiscreteWithin`,
  `IsOpen.inter_mem_nhdsNE_of_mem_codiscreteWithin`, and
  `IsOpen.sdiff_mem_nhdsNE_of_compl_mem_codiscreteWithin`: whenever `U ∈ 𝓝 x` (in particular for
  `x ∈ U` when `U` is open), `𝓝[≠] x ≤ Filter.codiscreteWithin U`, so `U ∩ s` (and `U \ s` when
  `sᶜ ∈ Filter.codiscreteWithin U`) belongs to `𝓝[≠] x`.
* `IsOpen.inter_of_mem_codiscreteWithin` and `IsOpen.sdiff_of_compl_mem_codiscreteWithin`:
  intersecting an open set `U` with `s ∈ Filter.codiscreteWithin U` (or removing `s` with
  `sᶜ ∈ Filter.codiscreteWithin U`) produces an open set.
* `Preperfect.subset_closure_inter_of_mem_codiscreteWithin` and
  `Preperfect.eqOn_of_eventuallyEq_codiscreteWithin` (with `sdiff` corollaries and `IsOpen`
  specializations in a `PerfectSpace`): when `U` is preperfect and `s ∈ Filter.codiscreteWithin U`,
  `U ∩ s` is dense in `U`, so continuous maps on `U` into a Hausdorff space that agree along
  `Filter.codiscreteWithin U` (or on `U \ s` for `sᶜ ∈ Filter.codiscreteWithin U`) agree on all of
  `U`.
* `IsCompact.finite_inter_of_compl_mem_codiscreteWithin`: any compact subset `K ⊆ U` meets `s` in a
  finite set whenever `sᶜ ∈ Filter.codiscreteWithin U`.
* `TauCeti.compl_mem_codiscreteWithin_of_subset_compl_derivedSet`,
  `TauCeti.subset_compl_derivedSet_of_compl_mem_codiscreteWithin`, and
  `TauCeti.compl_mem_codiscreteWithin_iff_subset_compl_derivedSet`: for `E ⊆ U`,
  `Eᶜ ∈ Filter.codiscreteWithin U` holds exactly when `U` avoids the derived set `derivedSet E`. In
  a `T₁` space this thickens any such `U` to the open superset `(derivedSet E)ᶜ`, within which `Eᶜ`
  remains codiscrete.
* `Homeomorph.preimage_mem_codiscreteWithin`: a homeomorphism `e` carries codiscreteness within
  `t` to codiscreteness of preimages within `e ⁻¹' t`, and back.
-/

public section

open Filter Set Topology

section TopologicalSpace

variable {X : Type*} [TopologicalSpace X] {U K s : Set X}

/-- If `U` is a neighborhood of `x`, the punctured neighborhood filter `𝓝[≠] x` is finer than
`Filter.codiscreteWithin U`. -/
theorem TauCeti.nhdsNE_le_codiscreteWithin {x : X} (hU : U ∈ 𝓝 x) :
    𝓝[≠] x ≤ codiscreteWithin U :=
  (le_inf nhdsWithin_le_nhds
    (le_principal_iff.2 (inter_mem (nhdsWithin_le_nhds hU) self_mem_nhdsWithin))).trans
    (nhdsWithin_le_codiscreteWithin (mem_of_mem_nhds hU))

/-- If `U` is a neighborhood of `x` and `s ∈ Filter.codiscreteWithin U`, then `U ∩ s` is a
punctured neighborhood of `x`. -/
theorem TauCeti.inter_mem_nhdsNE_of_mem_codiscreteWithin {x : X} (hU : U ∈ 𝓝 x)
    (hs : s ∈ codiscreteWithin U) : U ∩ s ∈ 𝓝[≠] x :=
  inter_mem (nhdsWithin_le_nhds hU) (TauCeti.nhdsNE_le_codiscreteWithin hU hs)

/-- If `U` is open and `s ∈ Filter.codiscreteWithin U`, then `U ∩ s` is a punctured neighborhood of
every point of `U`. -/
theorem IsOpen.inter_mem_nhdsNE_of_mem_codiscreteWithin (hU : IsOpen U)
    (hs : s ∈ codiscreteWithin U) {x : X} (hx : x ∈ U) : U ∩ s ∈ 𝓝[≠] x :=
  TauCeti.inter_mem_nhdsNE_of_mem_codiscreteWithin (hU.mem_nhds hx) hs

/-- If `U` is open and `sᶜ ∈ Filter.codiscreteWithin U`, then `U \ s` is a punctured neighborhood of
every point of `U`. -/
theorem IsOpen.sdiff_mem_nhdsNE_of_compl_mem_codiscreteWithin (hU : IsOpen U)
    (hs : sᶜ ∈ codiscreteWithin U) {x : X} (hx : x ∈ U) : U \ s ∈ 𝓝[≠] x :=
  hU.inter_mem_nhdsNE_of_mem_codiscreteWithin hs hx

/-- If `U` is open and `s` belongs to `Filter.codiscreteWithin U`, then `U ∩ s` is open. -/
theorem IsOpen.inter_of_mem_codiscreteWithin (hU : IsOpen U) (hs : s ∈ codiscreteWithin U) :
    IsOpen (U ∩ s) :=
  isOpen_iff_mem_nhds.2 fun _ hx =>
    insert_eq_of_mem hx ▸
      insert_mem_nhds_iff.2 (hU.inter_mem_nhdsNE_of_mem_codiscreteWithin hs hx.1)

/-- Removing a set `s` whose complement belongs to `Filter.codiscreteWithin U` from an open set `U`
yields an open set `U \ s`. -/
theorem IsOpen.sdiff_of_compl_mem_codiscreteWithin (hU : IsOpen U)
    (hs : sᶜ ∈ codiscreteWithin U) : IsOpen (U \ s) :=
  hU.inter_of_mem_codiscreteWithin hs

/-- Intersecting a preperfect set `U` with `s ∈ Filter.codiscreteWithin U` yields a subset whose
closure contains `U`. -/
theorem Preperfect.subset_closure_inter_of_mem_codiscreteWithin
    (hU : Preperfect U) (hs : s ∈ codiscreteWithin U) : U ⊆ closure (U ∩ s) := fun x hx => by
  rw [mem_closure_iff_nhdsWithin_neBot]
  have hne : (𝓝[U \ {x}] x).NeBot := accPt_principal_iff_nhdsWithin.1 (hU x hx)
  have hmem : U ∩ s ∈ 𝓝[U \ {x}] x :=
    mem_of_superset (inter_mem self_mem_nhdsWithin (nhdsWithin_le_codiscreteWithin hx hs))
      fun _ ⟨hyU, hys⟩ => ⟨hyU.1, hys⟩
  exact hne.mono (le_inf nhdsWithin_le_nhds (le_principal_iff.2 hmem))

/-- Removing `s` with `sᶜ ∈ Filter.codiscreteWithin U` from a preperfect set `U` leaves a subset
whose closure contains `U`. -/
theorem Preperfect.subset_closure_sdiff_of_compl_mem_codiscreteWithin
    (hU : Preperfect U) (hs : sᶜ ∈ codiscreteWithin U) : U ⊆ closure (U \ s) :=
  hU.subset_closure_inter_of_mem_codiscreteWithin hs

/-- Two continuous functions on a preperfect set `U` into a Hausdorff space that agree eventually
along `Filter.codiscreteWithin U` agree on all of `U`. -/
theorem Preperfect.eqOn_of_eventuallyEq_codiscreteWithin {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {f g : X → Y} (hU : Preperfect U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfg : f =ᶠ[codiscreteWithin U] g) : EqOn f g U := by
  have heq : EqOn f g (U ∩ {x | f x = g x}) := fun _ hx => hx.2
  exact heq.of_subset_closure hf hg inter_subset_left
    (hU.subset_closure_inter_of_mem_codiscreteWithin hfg)

/-- Two continuous functions on a preperfect set `U` into a Hausdorff space that agree on `U \ s`
for `sᶜ ∈ Filter.codiscreteWithin U` agree on all of `U`. -/
theorem Preperfect.eqOn_of_eqOn_sdiff_of_compl_mem_codiscreteWithin {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {f g : X → Y} (hU : Preperfect U)
    (hs : sᶜ ∈ codiscreteWithin U) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfg : EqOn f g (U \ s)) : EqOn f g U :=
  hU.eqOn_of_eventuallyEq_codiscreteWithin hf hg
    (mem_of_superset (inter_mem (self_mem_codiscreteWithin U) hs) hfg)

/-- In a `PerfectSpace`, intersecting an open set `U` with `s ∈ Filter.codiscreteWithin U` yields a
subset whose closure contains `U`. -/
theorem IsOpen.subset_closure_inter_of_mem_codiscreteWithin [PerfectSpace X]
    (hU : IsOpen U) (hs : s ∈ codiscreteWithin U) : U ⊆ closure (U ∩ s) :=
  hU.preperfect.subset_closure_inter_of_mem_codiscreteWithin hs

/-- In a `PerfectSpace`, removing `s` with `sᶜ ∈ Filter.codiscreteWithin U` from an open set `U`
leaves a subset whose closure contains `U`. -/
theorem IsOpen.subset_closure_sdiff_of_compl_mem_codiscreteWithin [PerfectSpace X]
    (hU : IsOpen U) (hs : sᶜ ∈ codiscreteWithin U) : U ⊆ closure (U \ s) :=
  hU.preperfect.subset_closure_sdiff_of_compl_mem_codiscreteWithin hs

/-- In a `PerfectSpace`, two continuous functions on an open set `U` into a Hausdorff space that
agree eventually along `Filter.codiscreteWithin U` agree on all of `U`. -/
theorem IsOpen.eqOn_of_eventuallyEq_codiscreteWithin [PerfectSpace X] {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {f g : X → Y} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfg : f =ᶠ[codiscreteWithin U] g) : EqOn f g U :=
  hU.preperfect.eqOn_of_eventuallyEq_codiscreteWithin hf hg hfg

/-- In a `PerfectSpace`, two continuous functions on an open set `U` into a Hausdorff space that
agree on `U \ s` for `sᶜ ∈ Filter.codiscreteWithin U` agree on all of `U`. -/
theorem IsOpen.eqOn_of_eqOn_sdiff_of_compl_mem_codiscreteWithin [PerfectSpace X] {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {f g : X → Y} (hU : IsOpen U)
    (hs : sᶜ ∈ codiscreteWithin U) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfg : EqOn f g (U \ s)) : EqOn f g U :=
  hU.preperfect.eqOn_of_eqOn_sdiff_of_compl_mem_codiscreteWithin hs hf hg hfg

/-- If `sᶜ ∈ Filter.codiscreteWithin U`, every compact subset `K ⊆ U` meets `s` in a finite set. -/
theorem IsCompact.finite_inter_of_compl_mem_codiscreteWithin (hK : IsCompact K) (hKU : K ⊆ U)
    (hs : sᶜ ∈ codiscreteWithin U) : (K ∩ s).Finite := by
  simpa only [sdiff_compl] using
    hK.finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono hKU hs)

/-- The complement of `E` is codiscrete within any set avoiding `derivedSet E`. -/
theorem TauCeti.compl_mem_codiscreteWithin_of_subset_compl_derivedSet {E : Set X}
    (hU : U ⊆ (derivedSet E)ᶜ) : Eᶜ ∈ codiscreteWithin U := by
  rw [mem_codiscreteWithin_accPt]
  exact fun x hx hacc =>
    hU hx (hacc.mono (principal_mono.mpr fun y hy => by_contra fun hyE => hy.2 hyE))

/-- If `E ⊆ U` and `Eᶜ ∈ Filter.codiscreteWithin U`, then `U` contains no accumulation point of
`E`. -/
theorem TauCeti.subset_compl_derivedSet_of_compl_mem_codiscreteWithin {E : Set X}
    (hEU : E ⊆ U) (hE : Eᶜ ∈ codiscreteWithin U) : U ⊆ (derivedSet E)ᶜ := fun x hx hxacc =>
  mem_codiscreteWithin_accPt.mp hE x hx
    (hxacc.mono (principal_mono.mpr fun _ hy => ⟨hEU hy, not_not.mpr hy⟩))

/-- For `E ⊆ U`, `Eᶜ ∈ Filter.codiscreteWithin U` holds if and only if `U` is disjoint from
`derivedSet E`. -/
theorem TauCeti.compl_mem_codiscreteWithin_iff_subset_compl_derivedSet {E : Set X}
    (hEU : E ⊆ U) : Eᶜ ∈ codiscreteWithin U ↔ U ⊆ (derivedSet E)ᶜ :=
  ⟨TauCeti.subset_compl_derivedSet_of_compl_mem_codiscreteWithin hEU,
    TauCeti.compl_mem_codiscreteWithin_of_subset_compl_derivedSet⟩

/-- Under a homeomorphism `e`, the preimage `e ⁻¹' s` is codiscrete within `e ⁻¹' t` exactly when
`s` is codiscrete within `t`. -/
theorem Homeomorph.preimage_mem_codiscreteWithin {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y)
    {s t : Set Y} : e ⁻¹' s ∈ codiscreteWithin (e ⁻¹' t) ↔ s ∈ codiscreteWithin t := by
  rw [← e.image_symm]
  exact e.symm.isEmbedding.image_mem_codiscreteWithin

end TopologicalSpace
