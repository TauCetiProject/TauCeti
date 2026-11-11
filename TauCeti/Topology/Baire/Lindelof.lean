/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.GDelta.Basic

/-!
# Meagre images over Lindelöf sets

Meagreness of an image can be checked locally on a Lindelöf set: if every point of a Lindelöf
set `U` has a neighbourhood `N` such that `f '' (N ∩ S)` is meagre, then so is `f '' (U ∩ S)`,
because countably many of these neighbourhoods cover `U` and a countable union of meagre sets is
meagre. This is the local-to-global step of the Sard and Sard--Smale theorems, in which `S` is a
set of critical points.
-/

public section

open Set
open scoped Topology

namespace IsLindelof

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {U S : Set X} {f : X → Y}

/-- If every point of a Lindelöf set `U` has a neighbourhood `N` such that `f '' (N ∩ S)` is
meagre, then `f '' (U ∩ S)` is meagre, since countably many of these neighbourhoods cover `U`. -/
theorem isMeagre_image_inter_of_forall_exists_mem_nhds (hU : IsLindelof U)
    (h : ∀ x ∈ U, ∃ N ∈ 𝓝 x, IsMeagre (f '' (N ∩ S))) : IsMeagre (f '' (U ∩ S)) := by
  choose! N hN hNm using h
  obtain ⟨t, htc, htU, hcover⟩ := hU.elim_nhds_subcover N hN
  refine (isMeagre_biUnion htc fun x hx ↦ hNm x (htU x hx)).mono ?_
  rintro _ ⟨z, ⟨hzU, hzS⟩, rfl⟩
  obtain ⟨x, hx, hzN⟩ := mem_iUnion₂.1 (hcover hzU)
  exact mem_iUnion₂.2 ⟨x, hx, z, ⟨hzN, hzS⟩, rfl⟩

end IsLindelof
