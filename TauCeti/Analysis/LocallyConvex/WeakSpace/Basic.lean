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
# Weak closedness of convex sets and weak lower semicontinuity of quasiconvex functions

In a locally convex space, a convex set has the same closure in the original and in the weak
topology (`Convex.toWeakSpace_closure`), so a real-convex set is weakly closed if and only if it is
closed in the original topology (`Convex.isClosed_toWeakSpace_iff`). Applied to the sublevel sets
of a function, this shows that a lower semicontinuous function whose sublevel sets are convex, that
is, a quasiconvex function, is also lower semicontinuous for the weak topology. Convex functions
are quasiconvex (`ConvexOn.quasiconvexOn`), so this covers lower semicontinuous convex functions.
This is the semicontinuity step of the direct method of the calculus of variations, where
minimizing sequences are only known to converge weakly.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Theorem 3.7 and Corollary 3.9.
-/

public section

open Set

namespace Convex

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] {s : Set E}

/-- A closed real-convex set in a locally convex space is closed in the weak topology. -/
theorem isClosed_toWeakSpace (hs : Convex ℝ s) (hc : IsClosed s) :
    IsClosed (toWeakSpace 𝕜 E '' s) := by
  rw [← hc.closure_eq, hs.toWeakSpace_closure 𝕜]
  exact isClosed_closure

/-- A real-convex set in a locally convex space is weakly closed if and only if it is closed in the
original topology. -/
theorem isClosed_toWeakSpace_iff (hs : Convex ℝ s) :
    IsClosed (toWeakSpace 𝕜 E '' s) ↔ IsClosed s := by
  refine ⟨fun h ↦ ?_, hs.isClosed_toWeakSpace⟩
  have hcoe : (toWeakSpaceCLM 𝕜 E : E → WeakSpace 𝕜 E) = toWeakSpace 𝕜 E :=
    funext (toWeakSpaceCLM_eq_toWeakSpace 𝕜 E)
  simpa only [hcoe, preimage_image_eq _ (toWeakSpace 𝕜 E).injective]
    using h.preimage (toWeakSpaceCLM 𝕜 E).continuous

end Convex

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
  have hclosed : IsClosed (toWeakSpace 𝕜 E '' {x | f x ≤ c}) :=
    hconv.isClosed_toWeakSpace (hlsc c)
  rwa [(toWeakSpace 𝕜 E).image_eq_preimage_symm] at hclosed

end QuasiconvexOn
