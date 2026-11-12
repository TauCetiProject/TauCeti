/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Induced topologies and infima of nonarchimedean group topologies

Mathlib shows that group topologies are stable under pulling back along a homomorphism
(`isTopologicalGroup_induced`) and under arbitrary infima (`isTopologicalGroup_sInf`). The same
holds for nonarchimedean group topologies, where every neighbourhood of `1` contains an open
subgroup:

* the topology induced by a homomorphism into a nonarchimedean group is nonarchimedean, since the
  preimage of an open subgroup is an open subgroup;
* the infimum of a set of nonarchimedean group topologies is nonarchimedean, since a neighbourhood
  of `1` for the infimum contains a finite intersection of neighbourhoods for members of the set,
  hence a finite intersection of open subgroups.

Together they let one define a topology as the finest nonarchimedean group topology with some
continuity properties, and test continuity out of it against induced topologies.

## Main results

* `TauCeti.nonarchimedeanGroup_induced`, `TauCeti.nonarchimedeanAddGroup_induced`: induced
  topologies.
* `TauCeti.nonarchimedeanGroup_sInf`, `TauCeti.nonarchimedeanAddGroup_sInf`: infima.
-/

public section

open Topology

namespace TauCeti

/-- **Pulling back a nonarchimedean group topology.** The topology on `G` induced by a
homomorphism `f : G →* H` into a nonarchimedean group is nonarchimedean. -/
@[to_additive /-- **Pulling back a nonarchimedean additive group topology.** The topology on `G`
induced by a homomorphism `f : G →+ H` into a nonarchimedean additive group is nonarchimedean. -/]
theorem nonarchimedeanGroup_induced {G H F : Type*} [Group G] [Group H] [TopologicalSpace H]
    [NonarchimedeanGroup H] [FunLike F G H] [MonoidHomClass F G H] (f : F) :
    @NonarchimedeanGroup G _ (TopologicalSpace.induced f ‹_›) := by
  let := TopologicalSpace.induced f ‹_›
  have := isTopologicalGroup_induced f
  refine ⟨fun U hU ↦ ?_⟩
  obtain ⟨V, hV, hVU⟩ := (nhds_induced f 1 ▸ hU : U ∈ Filter.comap f (𝓝 (f 1)))
  obtain ⟨O, hO⟩ := NonarchimedeanGroup.is_nonarchimedean V (by simpa using hV)
  exact ⟨O.comap (f : G →* H) continuous_induced_dom, fun x hx ↦ hVU (hO hx)⟩

/-- **Infima of nonarchimedean group topologies.** The infimum of a set of nonarchimedean group
topologies on `G`, the coarsest topology finer than each of them, is nonarchimedean. -/
@[to_additive /-- **Infima of nonarchimedean additive group topologies.** The infimum of a set of
nonarchimedean additive group topologies on `G`, the coarsest topology finer than each of them, is
nonarchimedean. -/]
theorem nonarchimedeanGroup_sInf {G : Type*} [Group G] {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @NonarchimedeanGroup G _ t) : @NonarchimedeanGroup G _ (sInf ts) := by
  let := sInf ts
  have : IsTopologicalGroup G :=
    isTopologicalGroup_sInf fun t ht ↦ (h t ht).toIsTopologicalGroup
  refine ⟨fun U hU ↦ ?_⟩
  rw [nhds_sInf, ← iInf_subtype''] at hU
  -- a neighbourhood of `1` for the infimum is built from finitely many neighbourhoods for members
  -- of `ts` by intersections; each of them contains an open subgroup, open for the infimum too
  refine Filter.iInf_sets_induct hU ⟨⊤, fun _ _ ↦ trivial⟩ fun {t} {s₁ s₂} hs₁ ⟨O₂, hO₂⟩ ↦ ?_
  obtain ⟨O₁, hO₁⟩ := @NonarchimedeanGroup.is_nonarchimedean G _ t (h t t.2) s₁ hs₁
  exact ⟨⟨@OpenSubgroup.toSubgroup G _ t O₁,
    TopologicalSpace.le_def.mp (sInf_le t.2) _ (@OpenSubgroup.isOpen G _ t O₁)⟩ ⊓ O₂,
    Set.inter_subset_inter hO₁ hO₂⟩

end TauCeti
