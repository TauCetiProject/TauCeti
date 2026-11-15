/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Dual

/-!
# Polars of absolutely convex hulls and neighbourhoods of zero

The absolute polar for a bilinear pairing is unchanged by taking an absolutely
convex hull. For the continuous dual pairing, taking the closed absolutely convex
hull also leaves the polar unchanged. This second identity holds for any module
carrying a topology, with no continuity assumed for addition or scalar
multiplication. These identities let separation arguments pass between a
generating set and its closed disked hull.

In addition, the polar of any neighbourhood of zero in a topological module over a
normed field is von Neumann bounded in the strong dual
(`StrongDual.isVonNBounded_polar_of_mem_nhds_zero`), extending
`NormedSpace.isBounded_polar_of_mem_nhds_zero` beyond normed spaces.
-/

public section

open scoped ComplexOrder Topology

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- Taking the absolutely convex hull does not change the absolute polar of a
bilinear pairing. -/
@[simp]
theorem polar_absConvexHull (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E) :
    B.polar (absConvexHull 𝕜 s) = B.polar s :=
  (B.polar_antitone subset_absConvexHull).antisymm <|
    (B.tripolar_eq_polar s).symm.trans_subset <|
      B.polar_antitone <| absConvexHull_min (B.subset_bipolar s) (polar_AbsConvex _)

end LinearMap

namespace StrongDual

section Hull

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- Taking the closed absolutely convex hull does not change the absolute polar. -/
@[simp]
theorem polar_closedAbsConvexHull (s : Set E) :
    polar 𝕜 (closedAbsConvexHull 𝕜 s) = polar 𝕜 s := by
  rw [polar]
  set B := (topDualPairing 𝕜 E).flip
  have hclosed : IsClosed (B.flip.polar (B.polar s)) := by
    simp only [B, LinearMap.polar_eq_iInter, LinearMap.flip_apply, topDualPairing_apply]
    exact isClosed_biInter fun f _ ↦ isClosed_le f.continuous.norm continuous_const
  exact (B.polar_antitone subset_closedAbsConvexHull).antisymm <|
    (B.tripolar_eq_polar s).symm.trans_subset <| B.polar_antitone <|
      closedAbsConvexHull_min (B.subset_bipolar s) (LinearMap.polar_AbsConvex _) hclosed

end Hull

/-- The polar of a neighbourhood of the origin in a topological module over a normed field is
von Neumann bounded in the strong dual. -/
theorem isVonNBounded_polar_of_mem_nhds_zero {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {s : Set E} (hs : s ∈ 𝓝 (0 : E)) :
    Bornology.IsVonNBounded 𝕜 (polar 𝕜 s) := by
  rw [ContinuousLinearMap.isVonNBounded_iff]
  intro A hA
  by_cases hne : (Bornology.cobounded 𝕜).NeBot
  · obtain ⟨c, hc⟩ := (hA hs).eventually.exists
    refine (NormedSpace.isVonNBounded_closedBall 𝕜 𝕜 ‖c‖).subset ?_
    rintro _ ⟨f, hf, x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hc hx
    dsimp only
    rw [mem_closedBall_zero_iff, map_smul, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg c) (hf y hy)
  · intro V _
    rw [Absorbs, Filter.not_neBot.1 hne]
    exact Filter.eventually_bot

end StrongDual
