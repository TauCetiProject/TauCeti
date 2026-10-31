/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Homomorphisms from preconnected topological groups

This file records a local-to-global principle for monoid homomorphisms from a preconnected
topological group: two such homomorphisms that agree near the identity agree everywhere.
-/

public section

open Filter
open scoped Topology

/-- Two monoid homomorphisms from a preconnected topological group that agree near the identity
agree everywhere. -/
@[to_additive /-- Two additive monoid homomorphisms from a preconnected additive topological group
that agree near zero agree everywhere. -/]
theorem MonoidHomClass.eq_of_eventuallyEq_one
    {F G M : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    [PreconnectedSpace G] [Monoid M] [FunLike F G M] [MonoidHomClass F G M]
    {φ ψ : F} (h : φ =ᶠ[𝓝 (1 : G)] ψ) : φ = ψ := by
  -- Membership in the equality locus is pointwise equality, so `h` says it is a neighbourhood
  -- of `1`; an open subgroup is clopen, hence everything in a preconnected group.
  let S := (φ : G →* M).eqLocus ψ
  have hopen : IsOpen (S : Set G) := S.isOpen_of_mem_nhds h
  have huniv := IsClopen.eq_univ ⟨S.isClosed_of_isOpen hopen, hopen⟩ ⟨1, S.one_mem⟩
  exact DFunLike.ext _ _ fun g => Set.eq_univ_iff_forall.1 huniv g
