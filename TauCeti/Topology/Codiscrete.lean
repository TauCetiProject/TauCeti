/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Open sets, preperfect density, and compact intersections for `Filter.codiscreteWithin`

Let `U` be a subset of a topological space `X`. Mathlib's `isClosed_sdiff_of_codiscreteWithin`
shows that removing a set `t ∈ Filter.codiscreteWithin U` from a closed set `U` yields a closed
set `U \ t`. This file supplies the dual open-set and density properties needed when removing a
relatively closed discrete subset `E` (`Eᶜ ∈ Filter.codiscreteWithin U`) from a domain `U`:

* `IsOpen.inter_of_mem_codiscreteWithin` and `IsOpen.sdiff_of_compl_mem_codiscreteWithin`:
  intersecting an open set `U` with `t ∈ Filter.codiscreteWithin U` (or removing `E` with
  `Eᶜ ∈ Filter.codiscreteWithin U`) produces an open set.
* `IsOpen.sdiff_mem_nhdsNE_of_compl_mem_codiscreteWithin`: `U \ E` is a punctured neighborhood of
  every point of an open set `U`.
* `Preperfect.subset_closure_sdiff_of_compl_mem_codiscreteWithin` and
  `Preperfect.eqOn_of_eqOn_sdiff_of_compl_mem_codiscreteWithin` (with `IsOpen` specializations in a
  `PerfectSpace`): when `U` is preperfect, `U \ E` is dense in `U`, so continuous maps on `U` into
  a Hausdorff space are determined by their values on `U \ E`.
* `IsCompact.finite_inter_of_compl_mem_codiscreteWithin`: any compact subset `K ⊆ U` meets `E` in a
  finite set.
-/

public section

open Filter Set Topology

section TopologicalSpace

variable {X : Type*} [TopologicalSpace X] {U K s : Set X}

/-- If `U` is open and `s` belongs to `Filter.codiscreteWithin U`, then `U ∩ s` is open. -/
theorem IsOpen.inter_of_mem_codiscreteWithin (hU : IsOpen U) (hs : s ∈ codiscreteWithin U) :
    IsOpen (U ∩ s) :=
  isOpen_iff_mem_nhds.2 fun x ⟨hxU, hxs⟩ => by
    have h1 : s ∪ Uᶜ ∈ 𝓝 x :=
      insert_eq_of_mem (mem_union_left Uᶜ hxs) ▸
        insert_mem_nhds_iff.2 (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs x hxU)
    exact mem_of_superset (inter_mem (hU.mem_nhds hxU) h1) fun y ⟨hyU, hy⟩ =>
      ⟨hyU, hy.resolve_right (not_not.2 hyU)⟩

/-- Removing a set `s` whose complement belongs to `Filter.codiscreteWithin U` from an open set `U`
yields an open set `U \ s`. -/
theorem IsOpen.sdiff_of_compl_mem_codiscreteWithin (hU : IsOpen U)
    (hs : sᶜ ∈ codiscreteWithin U) : IsOpen (U \ s) :=
  hU.inter_of_mem_codiscreteWithin hs

/-- If `U` is open and `sᶜ ∈ Filter.codiscreteWithin U`, then `U \ s` is a punctured neighborhood of
every point of `U`. -/
theorem IsOpen.sdiff_mem_nhdsNE_of_compl_mem_codiscreteWithin (hU : IsOpen U)
    (hs : sᶜ ∈ codiscreteWithin U) {x : X} (hx : x ∈ U) : U \ s ∈ 𝓝[≠] x := by
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs x hx
  have h2 : U ∈ 𝓝[≠] x := nhdsWithin_le_nhds (hU.mem_nhds hx)
  exact mem_of_superset (inter_mem h2 h1) fun y ⟨hyU, hy⟩ =>
    ⟨hyU, hy.resolve_right (not_not.2 hyU)⟩

/-- Removing `s` with `sᶜ ∈ Filter.codiscreteWithin U` from a preperfect set `U` leaves a subset
whose closure contains `U`. -/
theorem Preperfect.subset_closure_sdiff_of_compl_mem_codiscreteWithin
    (hU : Preperfect U) (hs : sᶜ ∈ codiscreteWithin U) : U ⊆ closure (U \ s) := fun x hx => by
  rw [mem_closure_iff_nhdsWithin_neBot]
  have hne : (𝓝[U \ {x}] x).NeBot := accPt_principal_iff_nhdsWithin.1 (hU x hx)
  have hmem : U \ s ∈ 𝓝[U \ {x}] x :=
    mem_of_superset
      (inter_mem self_mem_nhdsWithin (mem_codiscreteWithin_iff_forall_mem_nhdsWithin.1 hs x hx))
      fun y ⟨hyU, hys⟩ => ⟨hyU.1, hys⟩
  exact hne.mono (le_inf nhdsWithin_le_nhds (le_principal_iff.2 hmem))

/-- Two continuous functions on a preperfect set `U` into a Hausdorff space that agree on `U \ s`
for `sᶜ ∈ Filter.codiscreteWithin U` agree on all of `U`. -/
theorem Preperfect.eqOn_of_eqOn_sdiff_of_compl_mem_codiscreteWithin {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] {f g : X → Y} (hU : Preperfect U)
    (hs : sᶜ ∈ codiscreteWithin U) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfg : EqOn f g (U \ s)) : EqOn f g U :=
  hfg.of_subset_closure hf hg sdiff_subset
    (hU.subset_closure_sdiff_of_compl_mem_codiscreteWithin hs)

/-- In a `PerfectSpace`, removing `s` with `sᶜ ∈ Filter.codiscreteWithin U` from an open set `U`
leaves a subset whose closure contains `U`. -/
theorem IsOpen.subset_closure_sdiff_of_compl_mem_codiscreteWithin [PerfectSpace X]
    (hU : IsOpen U) (hs : sᶜ ∈ codiscreteWithin U) : U ⊆ closure (U \ s) :=
  hU.preperfect.subset_closure_sdiff_of_compl_mem_codiscreteWithin hs

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

end TopologicalSpace
