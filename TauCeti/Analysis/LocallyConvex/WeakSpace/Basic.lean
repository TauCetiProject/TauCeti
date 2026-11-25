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
# Weak lower semicontinuity of quasiconvex functions and Hermitian forms

In a locally convex space, a convex set has the same closure in the original and in the weak
topology (`Convex.toWeakSpace_closure`). Applied to the sublevel sets of a function, this shows
that a lower semicontinuous function whose sublevel sets are convex, that is, a quasiconvex
function, is also lower semicontinuous for the weak topology. Convex functions are quasiconvex
(`ConvexOn.quasiconvexOn`), so this covers lower semicontinuous convex functions. This is the
semicontinuity step of the direct method of the calculus of variations, where minimizing
sequences are only known to converge weakly.

The quadratic form `u ↦ re (a u u)` of a bounded Hermitian sesquilinear form `a` with nonnegative
real part on the diagonal is weakly lower semicontinuous as well
(`ContinuousLinearMap.lowerSemicontinuous_re_apply_self_comp_toWeakSpace_symm`). It is the
supremum of the weakly continuous functions `u ↦ 2 re (a v u) - re (a v v)`, attained at `v = u`;
this argument needs no real scalar structure on the space.

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

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- **Weak lower semicontinuity of a nonnegative Hermitian form.** If `a` is a bounded Hermitian
sesquilinear form with `0 ≤ re (a u u)` for every `u`, then `u ↦ re (a u u)` is lower
semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_re_apply_self_comp_toWeakSpace_symm (a : E →L⋆[𝕜] E →L[𝕜] 𝕜)
    (ha : ∀ u v, a u v = star (a v u)) (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) :
    LowerSemicontinuous fun w : WeakSpace 𝕜 E ↦
      RCLike.re (a ((toWeakSpace 𝕜 E).symm w) ((toWeakSpace 𝕜 E).symm w)) := by
  intro w y hy
  set u := (toWeakSpace 𝕜 E).symm w
  -- The weakly continuous function `x ↦ 2 re (a u x) - re (a u u)` lies below the quadratic
  -- form, since the form is nonnegative at `x - u`, and agrees with it at `u`.
  have hle : ∀ x, 2 * RCLike.re (a u x) - RCLike.re (a u u) ≤ RCLike.re (a x x) := by
    intro x
    have hx := hpos (x - u)
    have hux : RCLike.re (a x u) = RCLike.re (a u x) := by
      rw [ha x u, RCLike.star_def, RCLike.conj_re]
    simp only [map_sub, sub_apply] at hx
    linarith
  -- `WeakSpace 𝕜 E` is by definition `WeakBilin (topDualPairing 𝕜 E).flip`, and evaluating the
  -- functional `a u` at `x` is `(topDualPairing 𝕜 E).flip x (a u) = a u ((toWeakSpace 𝕜 E).symm x)`
  -- by definition, so `WeakBilin.eval_continuous` gives the weak continuity of `a u`.
  have hcont : Continuous fun x : WeakSpace 𝕜 E ↦
      2 * RCLike.re (a u ((toWeakSpace 𝕜 E).symm x)) - RCLike.re (a u u) :=
    ((continuous_const.mul (RCLike.continuous_re.comp
      (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (a u)))).sub continuous_const)
  have hw : y < 2 * RCLike.re (a u ((toWeakSpace 𝕜 E).symm w)) - RCLike.re (a u u) := by
    simp only [u] at hy ⊢
    linarith
  filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hw)] with x hx
  exact hx.trans_le (hle _)

end ContinuousLinearMap
