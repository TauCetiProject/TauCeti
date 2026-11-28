/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.Foliation.Leaf

/-!
# Flows of vector fields tangent to a foliation

Let `F` be a foliation of a Hausdorff boundaryless manifold modelled on a Banach space, and let
`v` be a `C¹` vector field tangent to `F`: `v y` lies in the tangent space `F.distribution y` of
`F` at every point `y`. Every trajectory of `v` is then a curve tangent to `F`, so its maximal
local flow `φ` (`TauCeti.flowOf`) moves points within their leaves: `φₜ x` lies on the leaf of `F`
through `x` whenever it is defined (`TauCeti.Foliation.sameLeaf_flowOf`,
`TauCeti.Foliation.flowOf_mem_leaf`). The field need not be complete.

Fields tangent to a foliation are how one moves along its leaves: for the characteristic
foliation of a presymplectic form, the flows of such fields also preserve the form.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19
  (integral manifolds and leaves of foliations).
-/

public section

open Set TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti.Foliation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [BoundarylessManifold I M]
  {k : ℕ} [IsManifold I (n + 1) M] [IsManifold I 1 M] {F : Foliation I n M k}
  {v : (x : M) → TangentSpace I x} {t : ℝ} {x : M}

/-- **Flows of fields tangent to a foliation stay in the leaves.** If a `C¹` vector field `v` is
tangent to the foliation `F`, then the time-`t` map of its maximal flow carries `x` to a point on
the same leaf of `F`, wherever it is defined. -/
theorem sameLeaf_flowOf (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hvF : ∀ y, v y ∈ F.distribution y) (ht : (t, x) ∈ flowDomain v) :
    F.SameLeaf x (flowOf v t x) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [flowOf_zero]
  -- The trajectory of `x` is defined on the whole interval between `0` and `t`.
  have hsub : uIcc 0 t ⊆ {s | (s, x) ∈ flowDomain v} := by
    intro s hs
    exact mem_flowDomain.2 <| ordConnected_maximalIntegralCurveInterval.uIcc_subset
      (mem_flowDomain.1 (mem_flowDomain_zero_of_mem ht)) (mem_flowDomain.1 ht) hs
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun s ↦ flowOf v s x) (uIcc 0 t) :=
    (contMDiffOn_flowOf le_rfl hv).comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      fun _ hs ↦ hsub hs
  -- Along it, the velocity is the field, which is tangent to `F`.
  have htan (s : ℝ) (hs : s ∈ uIcc 0 t) :
      curveVelocityWithin I (fun s ↦ flowOf v s x) (uIcc 0 t) s ∈
        F.distribution (flowOf v s x) := by
    rw [curveVelocityWithin_eq_of_hasMFDerivWithinAt
      (((isMIntegralCurveOn_flowOf hv x) s (hsub hs)).mono hsub)
      (uniqueDiffOn_Icc (min_lt_max.2 ht0.symm) s hs)]
    exact hvF _
  simpa only [flowOf_zero] using
    sameLeaf_of_contMDiffOn_of_tangent hγ htan left_mem_uIcc right_mem_uIcc

/-- The flow of a `C¹` vector field tangent to the foliation `F` carries `x` into the leaf of `F`
through `x`, wherever it is defined. -/
theorem flowOf_mem_leaf (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hvF : ∀ y, v y ∈ F.distribution y) (ht : (t, x) ∈ flowDomain v) :
    flowOf v t x ∈ F.leaf x :=
  mem_leaf.2 (sameLeaf_flowOf hv hvF ht)

end TauCeti.Foliation
