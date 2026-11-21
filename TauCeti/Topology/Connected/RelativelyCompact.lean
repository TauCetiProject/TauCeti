/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Separation.Regular

/-!
# Preconnected open enlargements with compact closure

A nonempty preconnected set with compact proper closure in a preconnected, locally compact,
locally connected Hausdorff space has an open preconnected enlargement containing its closure.
The enlargement has compact proper closure and contains a point outside the original closure.
This supplies strict domain enlargements for scalar Dirichlet eigenvalue monotonicity.

Adapted from Otis Chodosh's original formalization in
`ForTauCeti.Topology.Connected.RelativelyCompact`:
https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/8aec9bbc07081bb020b19f55d4aaa32c13db6667/ForTauCeti/Topology/Connected/RelativelyCompact.lean
-/

public section

open Set

namespace IsPreconnected

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
  [LocallyConnectedSpace X] [T2Space X] [PreconnectedSpace X] {U : Set X}

/-- A preconnected set with compact proper closure admits a preconnected open enlargement
with compact proper closure and points outside the original closure. -/
theorem exists_isOpen_isCompact_closure_superset (hU : IsPreconnected U)
    (hUc : IsCompact (closure U)) (hUn : U.Nonempty) (hproper : closure U ≠ univ) :
    ∃ V : Set X, IsOpen V ∧ IsPreconnected V ∧ IsCompact (closure V) ∧
      closure U ⊆ V ∧ (V \ closure U).Nonempty ∧ closure V ≠ univ := by
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem (closure U)).1 hproper
  have havoid : closure U ⊆ ({z} : Set X)ᶜ := by
    intro y hy hyz
    exact hz (mem_singleton_iff.1 hyz ▸ hy)
  obtain ⟨O, hOo, hUO, hOavoid, hOc⟩ :=
    exists_open_between_and_isCompact_closure hUc isOpen_compl_singleton havoid
  obtain ⟨p, hp⟩ := hUn
  let V := _root_.connectedComponentIn O p
  have hUV : closure U ⊆ V :=
    hU.closure.subset_connectedComponentIn (subset_closure hp) hUO
  have hVo : IsOpen V := hOo.connectedComponentIn
  have hVclO : closure V ⊆ closure O := closure_mono (connectedComponentIn_subset O p)
  have hVc : IsCompact (closure V) :=
    hOc.of_isClosed_subset isClosed_closure hVclO
  have hVproper : closure V ≠ univ := by
    apply (ne_univ_iff_exists_notMem (closure V)).2
    refine ⟨z, fun hzV ↦ ?_⟩
    exact hOavoid (hVclO hzV) (mem_singleton z)
  refine ⟨V, hVo, isPreconnected_connectedComponentIn, hVc, hUV, ?_, hVproper⟩
  by_contra hnone
  have hVU : V ⊆ closure U := by
    intro y hy
    by_contra hyU
    exact hnone ⟨y, hy, hyU⟩
  have heq : closure U = V := Subset.antisymm hUV hVU
  exact hproper ((IsClopen.eq_univ ⟨isClosed_closure, heq.symm ▸ hVo⟩)
    ⟨p, subset_closure hp⟩)

end IsPreconnected
