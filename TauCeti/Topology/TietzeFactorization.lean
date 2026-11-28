/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.TietzeExtension

/-!
# Factorization of continuous maps through closed maps via Tietze extension

Let `p : C(K, X)` be a closed continuous map into a normal topological space `X`, and let
`f : C(K, Y)` be a continuous map into a `TietzeExtension` space `Y` that is constant on the
fibers of `p`. Because `p` is closed, its range is a closed subset of `X` and the corestriction
`K → Set.range p` is a quotient map; hence `f` descends to a continuous map on `Set.range p`,
which extends by the Tietze extension theorem to a continuous map `g : C(X, Y)` satisfying
`g.comp p = f`.

In particular, this applies whenever `K` is compact and `X` is a normal Hausdorff (`T4Space`)
space.

## Main results

* `ContinuousMap.exists_comp_eq_of_isClosedMap`: a continuous map into a `TietzeExtension` space
  that factors set-theoretically through a closed continuous map `p : C(K, X)` into a normal space
  factors continuously through `p`.
* `ContinuousMap.exists_comp_eq_of_compactSpace`: specialization when `K` is compact and `X` is a
  `T4Space`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Weil/Periods/DescentVanishing.lean` (`exists_continuousMap_comp_eq`).
-/

@[expose] public section

namespace ContinuousMap

universe u₁ u v

/-- A continuous map `f : C(K, Y)` into a `TietzeExtension` space that is constant on the fibers of
a closed continuous map `p : C(K, X)` into a normal space factors as `g.comp p` for some
`g : C(X, Y)`. -/
theorem exists_comp_eq_of_isClosedMap {K : Type u₁} {X : Type u} {Y : Type v}
    [TopologicalSpace K] [TopologicalSpace X] [NormalSpace X]
    [TopologicalSpace Y] [TietzeExtension.{u, v} Y]
    {p : C(K, X)} (hp : IsClosedMap p) (f : C(K, Y))
    (hf : Function.FactorsThrough f p) :
    ∃ g : C(X, Y), g.comp p = f := by
  let q : C(K, Set.range p) := ⟨Set.rangeFactorization p, p.continuous.subtype_mk _⟩
  have hq_closed : IsClosedMap q := fun s hs ↦ by
    have heq : q '' s = Subtype.val ⁻¹' (p '' s) := by
      ext ⟨x, hx⟩
      exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a, ha, congrArg Subtype.val h⟩,
        fun ⟨a, ha, h⟩ ↦ ⟨a, ha, Subtype.ext h⟩⟩
    rw [heq]
    exact (hp s hs).preimage continuous_subtypeVal
  have hq : Topology.IsQuotientMap q :=
    hq_closed.isQuotientMap q.continuous Set.rangeFactorization_surjective
  have h_factors : Function.FactorsThrough f q :=
    fun _ _ hab ↦ hf (congrArg Subtype.val hab)
  have hrange : IsClosed (Set.range p) := by
    rw [← Set.image_univ]
    exact hp Set.univ isClosed_univ
  obtain ⟨g, hg⟩ := (hq.lift f h_factors).exists_restrict_eq hrange
  refine ⟨g, ContinuousMap.ext fun a ↦ ?_⟩
  change g.restrict (Set.range p) (q a) = f a
  rw [hg, ← ContinuousMap.comp_apply, hq.lift_comp]

/-- A continuous map `f : C(K, Y)` from a compact space into a `TietzeExtension` space that is
constant on the fibers of a continuous map `p : C(K, X)` into a `T4Space` factors as `g.comp p`
for some `g : C(X, Y)`. -/
theorem exists_comp_eq_of_compactSpace {K : Type u₁} {X : Type u} {Y : Type v}
    [TopologicalSpace K] [CompactSpace K] [TopologicalSpace X] [T4Space X]
    [TopologicalSpace Y] [TietzeExtension.{u, v} Y]
    (p : C(K, X)) (f : C(K, Y)) (hf : Function.FactorsThrough f p) :
    ∃ g : C(X, Y), g.comp p = f :=
  exists_comp_eq_of_isClosedMap p.continuous.isClosedMap f hf

end ContinuousMap
