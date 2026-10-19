/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Completeness of homogeneous locally compact spaces

A transitive action by isometries moves a compact neighbourhood of one point to a compact
neighbourhood of every point, with the same radius. A Cauchy filter eventually lies in one of
these compact balls, and therefore converges. This proves completeness without assuming that
the action depends continuously on the group parameter, or that distances are finite.

This metric argument is the completeness mechanism for homogeneous Riemannian model spaces.
Compare W. Thurston, *Three-Dimensional Geometry and Topology*, Vol. 1, Proposition 3.4.15,
conditions (b) and (e).

The Cauchy-filter argument follows Mathlib's `complete_of_proper` in
`Mathlib/Topology/MetricSpace/ProperSpace.lean`, using compact balls of one uniform radius
in place of properness.
-/

public section

open Filter Metric Set Topology
open scoped ENNReal

namespace TauCeti

variable {G X : Type*} [PseudoEMetricSpace X]
  [Group G] [MulAction G X] [IsIsometricSMul G X]
  [MulAction.IsPretransitive G X] [WeaklyLocallyCompactSpace X]

include G

variable (G) in
/-- In a weakly locally compact space with a transitive isometric action, there is a positive
radius for which every closed ball is compact. -/
theorem exists_pos_isCompact_closedEBall_of_isPretransitive (x : X) :
    ∃ r : ℝ≥0∞, 0 < r ∧ ∀ y : X, IsCompact (closedEBall y r) := by
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.mp hxK
  obtain ⟨r, hr, hrε⟩ := exists_between hε
  have hcompact : IsCompact (closedEBall x r) :=
    hK.of_isClosed_subset isClosed_closedEBall fun z hz ↦
      hball ((mem_closedEBall.mp hz).trans_lt hrε)
  refine ⟨r, hr, fun y ↦ ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  rw [← hg, ← smul_closedEBall]
  exact hcompact.smul g

variable (G X) in
/-- A weakly locally compact pseudoemetric space with a transitive action by isometries is
complete. The action need not be jointly continuous. -/
theorem completeSpace_of_isIsometricSMul_of_isPretransitive : CompleteSpace X where
  complete {f} hf := by
    -- Obtain a uniform compact-ball radius from any point of this nontrivial filter.
    obtain ⟨x, -⟩ := hf.1.nonempty_of_mem (univ_mem : (univ : Set X) ∈ f)
    obtain ⟨r, hr, hcompact⟩ := exists_pos_isCompact_closedEBall_of_isPretransitive G x
    obtain ⟨s, hs, hdiam⟩ := (EMetric.cauchy_iff.mp hf).2 r hr
    obtain ⟨y, hy⟩ := hf.1.nonempty_of_mem hs
    have hball : closedEBall y r ∈ f :=
      mem_of_superset hs fun z hz ↦ (hdiam z hz y hy).le
    obtain ⟨z, -, hz⟩ := (hcompact y).isComplete f hf (le_principal_iff.mpr hball)
    exact ⟨z, hz⟩

end TauCeti
