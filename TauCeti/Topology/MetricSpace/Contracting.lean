/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Fixed points of families of contractions

If a family of maps `F a`, for `a` in a set `S` of a topological space, contracts one set `s` with
one constant `K`, and `a ↦ F a y` is continuous on `S` for every `y ∈ s`, then the fixed points of
the maps `F a` depend continuously on `a`
(`TauCeti.continuousOn_of_forall_contractingWith`). The proof uses Mathlib's a posteriori estimate
`ContractingWith.dist_le_of_fixedPoint`. Mathlib's `ContractingWith.fixedPoint_lipschitz_in_map`
compares the fixed points of two contractions of a complete space; here the maps are restricted to
`s` and the family is indexed by a topological space.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace TauCeti

/-- **The fixed points of a uniformly contracting family depend continuously on the parameter.**
If every map `F a`, for `a ∈ S`, maps `s` to itself as a contraction with one constant `K` and
fixes a point `v a` of `s`, and `a ↦ F a y` is continuous on `S` for every `y ∈ s`, then `v` is
continuous on `S`: by the a posteriori estimate `ContractingWith.dist_le_of_fixedPoint`,
`dist (v a) (v a')` is at most `dist (F a (v a')) (F a' (v a')) / (1 - K)`. -/
theorem continuousOn_of_forall_contractingWith {α X : Type*} [TopologicalSpace α]
    [MetricSpace X] {S : Set α} {s : Set X} {F : α → X → X} {v : α → X} {K : ℝ≥0}
    (hmaps : ∀ a ∈ S, MapsTo (F a) s s)
    (hF : ∀ a (ha : a ∈ S), ContractingWith K ((hmaps a ha).restrict _ _ _))
    (hv : ∀ a ∈ S, v a ∈ s ∧ F a (v a) = v a)
    (hc : ∀ y ∈ s, ContinuousOn (fun a ↦ F a y) S) : ContinuousOn v S := by
  intro a' ha'
  have hdist : ∀ a ∈ S, dist (v a) (v a') ≤ dist (F a (v a')) (F a' (v a')) / (1 - K) := by
    intro a ha
    have h := (hF a ha).dist_le_of_fixedPoint ⟨v a', (hv a' ha').1⟩
      (y := ⟨v a, (hv a ha).1⟩) (Subtype.ext (hv a ha).2)
    rw [(hv a' ha').2, dist_comm, dist_comm (F a _)]
    simpa only [Subtype.dist_eq, MapsTo.val_restrict_apply] using h
  have hlim : Tendsto (fun a ↦ dist (F a (v a')) (F a' (v a')) / (1 - K)) (𝓝[S] a') (𝓝 0) := by
    simpa using ((hc _ (hv a' ha').1 a' ha').tendsto.dist
      (tendsto_const_nhds (x := F a' (v a')))).div_const (1 - K)
  exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (.of_forall fun _ ↦ dist_nonneg)
    (eventually_nhdsWithin_of_forall hdist) hlim)

end TauCeti
