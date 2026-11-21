/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Weak lower semicontinuity of quasiconvex functions

In a locally convex space, a convex set has the same closure in the original and in the weak
topology (`Convex.toWeakSpace_closure`). Applied to the sublevel sets of a function, this shows
that a lower semicontinuous function whose sublevel sets are convex, that is, a quasiconvex
function, is also lower semicontinuous for the weak topology. Convex functions are quasiconvex
(`ConvexOn.quasiconvexOn`), so this covers lower semicontinuous convex functions. This is the
semicontinuity step of the direct method of the calculus of variations, where minimizing
sequences are only known to converge weakly.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Corollary 3.9.
-/

public section

open Set

namespace QuasiconvexOn

variable {𝕜 E β : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [LinearOrder β] {f : E → β}

/-- **Weak lower semicontinuity.** A lower semicontinuous quasiconvex function on a locally convex
space is lower semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_comp_toWeakSpace_symm (hf : QuasiconvexOn ℝ univ f)
    (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage] at hlsc ⊢
  intro c
  have hconv : Convex ℝ {x | f x ≤ c} := by simpa only [mem_univ, true_and] using hf c
  have hclosed : IsClosed (toWeakSpace 𝕜 E '' {x | f x ≤ c}) := by
    have hc : IsClosed {x | f x ≤ c} := hlsc c
    rw [← hc.closure_eq, hconv.toWeakSpace_closure 𝕜]
    exact isClosed_closure
  rwa [(toWeakSpace 𝕜 E).image_eq_preimage_symm] at hclosed

end QuasiconvexOn
