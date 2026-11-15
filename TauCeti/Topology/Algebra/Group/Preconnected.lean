/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Homomorphisms and preconnected topological groups

This file records a local-to-global principle for monoid homomorphisms from a preconnected
topological group: two such homomorphisms that agree near the identity agree everywhere.
An open homomorphism into a preconnected group is surjective. More directly, since every open
subgroup is clopen and contains the identity, the whole group `⊤` is the unique open subgroup of a
preconnected group; consequently no proper subset contains an open subgroup, and a noncompact
preconnected group has no compact open subgroup.

## Main results

* `MonoidHomClass.eq_of_eventuallyEq_one`: agreement near the identity gives global equality.
* `MonoidHom.surjective_of_isOpenMap` and `AddMonoidHom.surjective_of_isOpenMap`: an open
  homomorphism into a preconnected group is onto.
* `Subgroup.eq_top_of_isOpen`, `OpenSubgroup.eq_top_of_preconnectedSpace`, and
  `OpenSubgroup.instUniqueOfPreconnectedSpace` (with additive counterparts): `⊤` is the only open
  subgroup of a preconnected group with separately continuous multiplication.
* `OpenSubgroup.not_subset_of_ne_univ` and `OpenSubgroup.not_isCompact` (with additive
  counterparts): no proper subset contains an open subgroup, and no open subgroup is compact when
  the ambient group is noncompact.
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

/-- An open homomorphism into a preconnected group is surjective. -/
@[to_additive /-- An open additive homomorphism into a preconnected additive group is
surjective. -/]
theorem MonoidHom.surjective_of_isOpenMap {G K : Type*} [Group G] [TopologicalSpace G]
    [Group K] [TopologicalSpace K] [SeparatelyContinuousMul K] [PreconnectedSpace K]
    (f : G →* K) (hf : IsOpenMap f) : Function.Surjective f := by
  have hopen : IsOpen (f.range : Set K) := hf.isOpen_range
  have hclopen : IsClopen (f.range : Set K) := ⟨f.range.isClosed_of_isOpen hopen, hopen⟩
  have hfull := hclopen.eq_univ ⟨1, f.range.one_mem⟩
  exact Set.range_eq_univ.mp hfull

/-- Every open subgroup of a preconnected topological group with separately continuous
multiplication is the whole group. -/
@[to_additive /-- Every open additive subgroup of a preconnected additive topological group with
separately continuous addition is the whole group. -/]
theorem Subgroup.eq_top_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [PreconnectedSpace G] {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : H = ⊤ :=
  Subgroup.coe_eq_univ.mp (IsClopen.eq_univ ⟨H.isClosed_of_isOpen hH, hH⟩ ⟨1, H.one_mem⟩)

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [PreconnectedSpace G]

/-- Every open subgroup of a preconnected topological group with separately continuous
multiplication equals `⊤`. -/
@[to_additive /-- Every open additive subgroup of a preconnected additive topological group with
separately continuous addition equals `⊤`. -/]
theorem eq_top_of_preconnectedSpace (U : OpenSubgroup G) : U = ⊤ :=
  toSubgroup_injective (U.toSubgroup.eq_top_of_isOpen U.isOpen)

/-- In a preconnected topological group with separately continuous multiplication, `⊤` is the
unique open subgroup. -/
@[to_additive /-- In a preconnected additive topological group with separately continuous addition,
`⊤` is the unique open additive subgroup. -/]
instance instUniqueOfPreconnectedSpace : Unique (OpenSubgroup G) where
  default := ⊤
  uniq := eq_top_of_preconnectedSpace

/-- No proper subset of a preconnected topological group with separately continuous multiplication
contains an open subgroup. -/
@[to_additive /-- No proper subset of a preconnected additive topological group with separately
continuous addition contains an open additive subgroup. -/]
theorem not_subset_of_ne_univ {s : Set G} (hs : s ≠ Set.univ) (U : OpenSubgroup G) :
    ¬(U : Set G) ⊆ s := by
  rw [U.eq_top_of_preconnectedSpace, coe_top, Set.univ_subset_iff]
  exact hs

/-- A noncompact preconnected topological group with separately continuous multiplication has no
compact open subgroup. -/
@[to_additive /-- A noncompact preconnected additive topological group with separately continuous
addition has no compact open additive subgroup. -/]
theorem not_isCompact [NoncompactSpace G] (U : OpenSubgroup G) : ¬IsCompact (U : Set G) := by
  rw [U.eq_top_of_preconnectedSpace, coe_top]
  exact noncompact_univ G

end OpenSubgroup

end
