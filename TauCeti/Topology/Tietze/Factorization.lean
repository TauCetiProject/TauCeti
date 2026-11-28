/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.TietzeExtension

/-!
# Factorization of continuous maps through strict maps via Tietze extension

Let `p : C(K, X)` be a strict map (a continuous map whose corestriction to its range is a quotient
map, `Topology.IsStrictMap`) with closed range in a normal topological space `X`, and let
`f : C(K, Y)` be a continuous map into a `TietzeExtension` space `Y` that is constant on the
fibers of `p`. Then `f` descends to a continuous map on `Set.range p`, which extends by the Tietze
extension theorem to a continuous map `g : C(X, Y)` satisfying `g.comp p = f`.

Closed continuous maps are strict with closed range, so this applies in particular to a
continuous map from a compact space into a `T4Space`.

## Main results

* `ContinuousMap.exists_comp_eq_of_isStrictMap`: a continuous map into a `TietzeExtension` space
  that factors set-theoretically through a strict map `p : C(K, X)` with closed range in a normal
  space factors continuously through `p`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Weil/Periods/DescentVanishing.lean` (`exists_continuousMap_comp_eq`).
-/

@[expose] public section

namespace ContinuousMap

universe u₁ u v

/-- A continuous map `f : C(K, Y)` into a `TietzeExtension` space that is constant on the fibers of
a strict map `p : C(K, X)` with closed range in a normal space factors as `g.comp p` for some
`g : C(X, Y)`. -/
theorem exists_comp_eq_of_isStrictMap {K : Type u₁} {X : Type u} {Y : Type v}
    [TopologicalSpace K] [TopologicalSpace X] [NormalSpace X]
    [TopologicalSpace Y] [TietzeExtension.{u, v} Y]
    {p : C(K, X)} (hp : Topology.IsStrictMap p) (hrange : IsClosed (Set.range p))
    (f : C(K, Y)) (hf : Function.FactorsThrough f p) :
    ∃ g : C(X, Y), g.comp p = f := by
  let q : C(K, Set.range p) := ⟨Set.rangeFactorization p, p.continuous.rangeFactorization⟩
  have hq : Topology.IsQuotientMap q := hp
  have h_factors : Function.FactorsThrough f q :=
    fun _ _ hab ↦ hf (Subtype.ext_iff.mp hab)
  obtain ⟨g, hg⟩ := (hq.lift f h_factors).exists_restrict_eq hrange
  refine ⟨g, ContinuousMap.ext fun a ↦ ?_⟩
  have := congr($(hq.lift_comp f h_factors) a)
  rw [ContinuousMap.comp_apply] at this
  simpa [← hg, q] using this

end ContinuousMap
