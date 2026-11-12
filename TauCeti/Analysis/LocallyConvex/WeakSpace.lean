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
topology (`Convex.toWeakSpace_closure`). Consequently, a real-convex set is weakly closed if and
only if it is closed in the original topology (`Convex.isClosed_toWeakSpace_iff`).

Applied to the sublevel sets `{x ∈ s | f x ≤ c}` of a function on an arbitrary set `s`, this shows
that a function lower semicontinuous and quasiconvex on `s` is also lower semicontinuous on `s`
for the weak topology (`QuasiconvexOn.lowerSemicontinuousOn_comp_toWeakSpace_symm`), without any
closedness assumption on `s`. Convex functions are quasiconvex (`ConvexOn.quasiconvexOn`), so this
covers lower semicontinuous convex functions (`ConvexOn.lowerSemicontinuousOn_comp_toWeakSpace_symm`
and `ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm`). This is the semicontinuity step of the
direct method of the calculus of variations, where minimizing sequences are only known to converge
weakly.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Theorem 3.7 and Corollary 3.9.
-/

public section

open Set

section LocallyConvex

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

variable (𝕜) in
/-- In a locally convex space, a closed real-convex set is weakly closed. -/
theorem Convex.isClosed_toWeakSpace {s : Set E} (hs : Convex ℝ s) (hsc : IsClosed s) :
    IsClosed (toWeakSpace 𝕜 E '' s) := by
  rw [← hsc.closure_eq, hs.toWeakSpace_closure 𝕜]
  exact isClosed_closure

variable (𝕜) in
/-- In a locally convex space, a real-convex set is weakly closed if and only if it is closed in
the original topology. -/
theorem Convex.isClosed_toWeakSpace_iff {s : Set E} (hs : Convex ℝ s) :
    IsClosed (toWeakSpace 𝕜 E '' s) ↔ IsClosed s := by
  refine ⟨fun h ↦ ?_, hs.isClosed_toWeakSpace 𝕜⟩
  convert h.preimage (map_continuous (toWeakSpaceCLM 𝕜 E)) using 1
  ext
  simp [(toWeakSpace 𝕜 E).injective.mem_set_image]

namespace QuasiconvexOn

variable {β : Type*} [LinearOrder β] {s : Set E} {f : E → β}

/-- **Weak lower semicontinuity on a set.** A function that is quasiconvex and lower semicontinuous
on a subset `s` of a locally convex space is lower semicontinuous on `s` for the weak topology. No
closedness assumption on `s` is needed. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm (hf : QuasiconvexOn ℝ s f)
    (hlsc : LowerSemicontinuousOn f s) :
    LowerSemicontinuousOn (fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u))
      (toWeakSpace 𝕜 E '' s) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hlsc ⊢
  intro c
  obtain ⟨v, hv, hsv⟩ := hlsc c
  set A : Set E := s ∩ f ⁻¹' Iic c
  have hconv : Convex ℝ A := hf c
  have hsA : s ∩ closure A = A := subset_antisymm
    ((inter_subset_inter_right s
      (closure_minimal (hsv ▸ inter_subset_right) hv)).trans_eq hsv.symm)
    (subset_inter inter_subset_left subset_closure)
  refine ⟨closure (toWeakSpace 𝕜 E '' A), isClosed_closure, ?_⟩
  have hpre : (toWeakSpace 𝕜 E '' s) ∩
      (fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u)) ⁻¹' Iic c =
      toWeakSpace 𝕜 E '' A := by
    rw [← Function.comp_def f, preimage_comp, ← (toWeakSpace 𝕜 E).image_eq_preimage_symm,
      image_inter (toWeakSpace 𝕜 E).injective]
  rw [hpre, ← hconv.toWeakSpace_closure 𝕜, ← image_inter (toWeakSpace 𝕜 E).injective, hsA]

/-- **Weak lower semicontinuity.** A lower semicontinuous quasiconvex function on a locally convex
space is lower semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_comp_toWeakSpace_symm (hf : QuasiconvexOn ℝ univ f)
    (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u) := by
  rw [← lowerSemicontinuousOn_univ_iff, ← (toWeakSpace 𝕜 E).surjective.range_eq, ← image_univ]
  exact hf.lowerSemicontinuousOn_comp_toWeakSpace_symm (hlsc.lowerSemicontinuousOn univ)

end QuasiconvexOn

namespace ConvexOn

variable {β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [Module ℝ β] [PosSMulMono ℝ β] {s : Set E} {f : E → β}

/-- A function that is real-convex and lower semicontinuous on a subset `s` of a locally convex
space is lower semicontinuous on `s` for the weak topology. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm (hf : ConvexOn ℝ s f)
    (hlsc : LowerSemicontinuousOn f s) :
    LowerSemicontinuousOn (fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u))
      (toWeakSpace 𝕜 E '' s) :=
  hf.quasiconvexOn.lowerSemicontinuousOn_comp_toWeakSpace_symm hlsc

/-- A lower semicontinuous real-convex function on a locally convex space is lower semicontinuous
for the weak topology. -/
theorem lowerSemicontinuous_comp_toWeakSpace_symm (hf : ConvexOn ℝ univ f)
    (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u) :=
  hf.quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm hlsc

end ConvexOn

end LocallyConvex
