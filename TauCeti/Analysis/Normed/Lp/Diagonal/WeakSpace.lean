/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Diagonal.Basic
public import TauCeti.Analysis.Normed.Module.WeakSpace.Sphere
public import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Spheres of diagonal operators in the weak topology

For a bounded scalar family `d` indexed by an infinite type, the diagonal operator
`lp.diagonalCLM d` on `ℓ^p(ι, 𝕜)` is injective when no coefficient vanishes
(`lp.injective_diagonalCLM_iff`), and compact when the coefficients tend to zero
(`lp.isCompactOperator_diagonalCLM`), as for `d n = 1 / (n + 1)` on `ℓ²(ℕ)`. For such an operator
the sphere `{u | ‖lp.diagonalCLM d u‖ = r}` of positive radius is weakly sequentially closed but
not weakly closed. This is the concrete instance of the general facts on compact operators in the
weak topology: the operator is continuous from the weak topology to the norm topology on bounded
sets (`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`) but not on the whole
space (`TauCeti.not_continuous_comp_toWeakSpace_symm`).
-/

public section

open Filter Set Topology
open scoped lp ENNReal

namespace lp

variable {ι 𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] {d : ℓ^∞(ι, 𝕜)}

/-- For an infinite index type and nonvanishing coefficients, a sphere of positive radius of a
diagonal operator is not weakly closed. -/
theorem not_isClosed_toWeakSpace_setOf_norm_diagonalCLM_eq [Infinite ι] (hd : ∀ i, d i ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u | ‖diagonalCLM d u‖ = r}) :=
  TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq not_finite
    ((injective_diagonalCLM_iff d).2 hd) hr

/-- If the coefficients tend to zero, every sphere of a diagonal operator is weakly sequentially
closed. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_diagonalCLM_eq
    (hd : Tendsto (fun i ↦ ‖d i‖) cofinite (𝓝 0)) (r : ℝ) :
    IsSeqClosed (toWeakSpace 𝕜 ℓ^p(ι, 𝕜) '' {u | ‖diagonalCLM d u‖ = r}) := by
  have heq : {u : ℓ^p(ι, 𝕜) | ‖diagonalCLM d u‖ = r} =
      diagonalCLM d ⁻¹' Metric.sphere 0 r := by
    ext u
    simp
  rw [heq]
  exact (isCompactOperator_diagonalCLM d hd).isSeqClosed_toWeakSpace_preimage
    Metric.isClosed_sphere

end lp
