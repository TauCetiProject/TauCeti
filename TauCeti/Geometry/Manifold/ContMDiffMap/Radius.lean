/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth radii inside product neighbourhoods

An open neighbourhood of a constant section in `M × V` contains a closed ball of positive
smooth radius in each fibre. The radius can tend to zero at infinity; no uniform radius or
compactness of `M` is required. This is the shrinking step used to fit normal disc bundles
inside prescribed neighbourhoods before constructing tubular coordinates.

The construction uses Mathlib's convex-valued smooth selection theorem
`exists_contMDiffMap_forall_mem_convex_of_local_const`.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace IsOpen

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [PseudoMetricSpace V]

/-- Every open neighbourhood of a constant section contains fibrewise closed balls of a
positive smooth radius smaller than any given positive continuous bound.
The second factor can be any pseudometric space. -/
theorem exists_contMDiffMap_closedBall_subset {U : Set (M × V)} (hU : IsOpen U)
    {v₀ : V} (hsection : ∀ x, (x, v₀) ∈ U)
    {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < r x) ∧ (∀ x, r x < ε x) ∧
      ∀ x, ∀ v ∈ Metric.closedBall v₀ (r x), (x, v) ∈ U := by
  let T : M → Set ℝ := fun x => {r | 0 < r ∧ r < ε x ∧
    ∀ v ∈ Metric.closedBall v₀ r, (x, v) ∈ U}
  have hconv : ∀ x, Convex ℝ (T x) := by
    intro x
    apply Set.OrdConnected.convex
    constructor
    rintro a ⟨ha, -⟩ b ⟨-, hbε, hb⟩ c ⟨hac, hcb⟩
    exact ⟨ha.trans_le hac, hcb.trans_lt hbε,
      fun v hv => hb v (Metric.closedBall_subset_closedBall hcb hv)⟩
  have hlocal : ∀ x, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ T y := by
    intro x
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds (hsection x))
    obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp hB
    let c := min (δ / 2) (ε x / 2)
    refine ⟨c, ?_⟩
    filter_upwards [hA, hε.continuousAt.eventually
      (eventually_gt_nhds (half_lt_self (hεpos x)))] with y hy hyε
    refine ⟨lt_min (half_pos hδ) (half_pos (hεpos x)),
      (min_le_right _ _).trans_lt hyε, fun v hv => hAB ⟨hy, hδB ?_⟩⟩
    exact (Metric.mem_closedBall.mp hv).trans_lt
      ((min_le_left _ _).trans_lt (half_lt_self hδ))
  obtain ⟨r, hr⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const I hconv hlocal
  exact ⟨r, fun x => (hr x).1, fun x => (hr x).2.1, fun x => (hr x).2.2⟩

end IsOpen
