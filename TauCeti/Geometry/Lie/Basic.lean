/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Basic facts about Lie groups

This file records lightweight consequences of the Lie-group regularity hierarchy.

## Main results

* `ModelWithCorners.t2Space_of_lieGroup`: a Lie group modeled on a normed space is Hausdorff.
* `LieGroup.minSmoothness_of_isRCLikeNormedField`: over a field satisfying
  `IsRCLikeNormedField`, a `Cⁿ` Lie group is a `C^(minSmoothness 𝕜 n)` Lie group; Mathlib's
  tangent Lie algebra `GroupLieAlgebra` assumes regularity `minSmoothness 𝕜 3`.
-/

public section

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

variable (I) in
/-- A Lie group modeled on a normed space is Hausdorff. -/
theorem ModelWithCorners.t2Space_of_lieGroup (n : ℕ∞ω) [LieGroup I n G] : T2Space G := by
  have := I.t1Space G
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I n
  infer_instance

/-- Over a field satisfying `IsRCLikeNormedField`, `minSmoothness 𝕜 n = n`, so a `Cⁿ` Lie group
is a `C^(minSmoothness 𝕜 n)` Lie group. Mathlib's tangent Lie algebra `GroupLieAlgebra` assumes
`LieGroup I (minSmoothness 𝕜 3) G`, which this supplies from `LieGroup I 3 G`. This theorem is
deliberately not a global instance, so the downgrade applies only in files that opt in with
`attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField`. -/
theorem LieGroup.minSmoothness_of_isRCLikeNormedField [IsRCLikeNormedField 𝕜] {n : ℕ∞ω}
    [LieGroup I n G] : LieGroup I (minSmoothness 𝕜 n) G := by
  rwa [_root_.minSmoothness_of_isRCLikeNormedField]
