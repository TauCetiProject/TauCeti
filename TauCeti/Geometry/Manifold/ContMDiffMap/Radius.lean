/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth radii inside product neighbourhoods

A neighbourhood of a constant section in `M × V` contains a closed ball of positive smooth
radius in each fibre, and the radius can be chosen below any positive lower semicontinuous
bound. The radius can tend to zero at infinity; no uniform radius or compactness of `M` is
required. This is the shrinking step used to fit normal disc bundles
inside prescribed neighbourhoods before constructing tubular coordinates.

The construction uses Mathlib's convex-valued smooth selection theorem
`exists_contMDiffMap_forall_mem_convex_of_local_const`.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [PseudoMetricSpace V]

/-- Every neighbourhood of a constant section contains fibrewise closed balls of a positive
smooth radius smaller than any given positive lower semicontinuous bound.
The second factor can be any pseudometric space. -/
theorem exists_contMDiffMap_closedBall_subset {U : Set (M × V)} {v₀ : V}
    (hU : ∀ x, U ∈ 𝓝 (x, v₀)) {ε : M → ℝ} (hε : LowerSemicontinuous ε)
    (hεpos : ∀ x, 0 < ε x) :
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < r x) ∧ (∀ x, r x < ε x) ∧
      ∀ x, ∀ v ∈ Metric.closedBall v₀ (r x), (x, v) ∈ U := by
  let T : M → Set ℝ := fun x => {r | 0 < r ∧ r < ε x ∧
    ∀ v ∈ Metric.closedBall v₀ r, (x, v) ∈ U}
  have hconv : ∀ x, Convex ℝ (T x) := fun x =>
    Set.OrdConnected.convex ⟨fun a ⟨ha, _⟩ b ⟨_, hbε, hb⟩ c ⟨hac, hcb⟩ =>
      ⟨ha.trans_le hac, hcb.trans_lt hbε,
        fun v hv => hb v (Metric.closedBall_subset_closedBall hcb hv)⟩⟩
  have hlocal : ∀ x, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ T y := by
    intro x
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (hU x)
    obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp hB
    refine ⟨min (δ / 2) (ε x / 2), ?_⟩
    filter_upwards [hA, hε x _ (half_lt_self (hεpos x))] with y hy hyε
    refine ⟨lt_min (half_pos hδ) (half_pos (hεpos x)),
      (min_le_right _ _).trans_lt hyε, fun v hv => hAB ⟨hy, hδB ?_⟩⟩
    exact (Metric.mem_closedBall.mp hv).trans_lt
      ((min_le_left _ _).trans_lt (half_lt_self hδ))
  obtain ⟨r, hr⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const I hconv hlocal
  exact ⟨r, fun x => (hr x).1, fun x => (hr x).2.1, fun x => (hr x).2.2⟩

end TauCeti
