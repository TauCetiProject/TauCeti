/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Dual

/-!
# Polars of absolutely convex hulls and zero-neighborhoods

The absolute polar for a bilinear pairing is unchanged by taking an absolutely
convex hull. For the continuous dual pairing, taking the closed absolutely convex
hull also leaves the polar unchanged. This second identity holds for any module
carrying a topology, with no continuity assumed for addition or scalar
multiplication. These identities let separation arguments pass between a
generating set and its closed disked hull.

In addition, the polar of any neighborhood of zero in a topological module over a
nontrivially normed field is von Neumann bounded in the strong dual
(`StrongDual.isVonNBounded_polar`): every bounded subset of the primal space is
absorbed by the neighborhood, so functionals in the polar are uniformly bounded on
it.
-/

public section

open Topology
open scoped ComplexOrder Pointwise

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

section RCLike

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

end RCLike

section Bounded

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- The polar of a neighborhood of zero is von Neumann bounded in the strong dual: every
von Neumann bounded subset of `E` is absorbed by the neighborhood, so functionals in the polar are
uniformly bounded on it. -/
theorem isVonNBounded_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    Bornology.IsVonNBounded 𝕜 (polar 𝕜 U) := by
  refine ContinuousLinearMap.isVonNBounded_iff.2 fun s hs ↦ ?_
  obtain ⟨r, -, hr⟩ := (hs hU).exists_pos
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 r
  have hsub : s ⊆ c • U := hr c hc.le
  refine (NormedSpace.isVonNBounded_closedBall 𝕜 𝕜 ‖c‖).subset ?_
  rintro _ ⟨f, hf, x, hx, rfl⟩
  obtain ⟨u, hu, rfl⟩ := hsub hx
  simp only [Metric.mem_closedBall, dist_zero_right, map_smul, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg c) (hf u hu)

end Bounded

end StrongDual
