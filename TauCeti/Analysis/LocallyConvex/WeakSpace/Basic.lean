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
topology (`Convex.toWeakSpace_closure`), so any closed convex set is weakly closed
(`Convex.isClosed_toWeakSpace_image`). Applied to the relative sublevel sets of a function on a
set `s`, this shows that a relatively lower semicontinuous function whose sublevel sets in `s` are
convex, that is, a quasiconvex function on `s`, is also lower semicontinuous on the weak image
`toWeakSpace 𝕜 E '' s` (`QuasiconvexOn.lowerSemicontinuousOn_comp_toWeakSpace_symm`), without
requiring `s` itself to be closed; taking `s = Set.univ` gives global weak lower semicontinuity
(`QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm`). Convex functions are quasiconvex
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

namespace Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [LocallyConvexSpace ℝ E]

/-- A closed convex set in a locally convex space has closed image in `WeakSpace 𝕜 E`. -/
theorem isClosed_toWeakSpace_image (𝕜 : Type*) [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    [ContinuousSMul 𝕜 E] {s : Set E} (hs : Convex ℝ s) (hc : IsClosed s) :
    IsClosed (toWeakSpace 𝕜 E '' s) := by
  rw [← hc.closure_eq, hs.toWeakSpace_closure 𝕜]
  exact isClosed_closure

end Convex

namespace QuasiconvexOn

variable {𝕜 E β : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] [LinearOrder β] {s : Set E} {f : E → β}

/-- **Relative weak lower semicontinuity.** A function that is quasiconvex and lower semicontinuous
on a subset `s` of a locally convex space is lower semicontinuous on `toWeakSpace 𝕜 E '' s` in the
weak topology; `s` itself need not be closed. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm (hf : QuasiconvexOn ℝ s f)
    (hlsc : LowerSemicontinuousOn f s) :
    LowerSemicontinuousOn
      (fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u)) (toWeakSpace 𝕜 E '' s) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hlsc ⊢
  intro b
  obtain ⟨t, ht, hst⟩ := hlsc b
  have hsub_eq : {x ∈ s | f x ≤ b} = s ∩ t := hst
  have hconv : Convex ℝ {x ∈ s | f x ≤ b} := hf b
  have hinter : s ∩ closure {x ∈ s | f x ≤ b} = {x ∈ s | f x ≤ b} := by
    refine Subset.antisymm ?_ (subset_inter (fun _ hx ↦ hx.left) subset_closure)
    rw [hsub_eq]
    exact inter_subset_inter_right s (closure_minimal inter_subset_right ht)
  refine ⟨closure (toWeakSpace 𝕜 E '' {x ∈ s | f x ≤ b}), isClosed_closure, ?_⟩
  rw [← hconv.toWeakSpace_closure 𝕜, ← image_inter (toWeakSpace 𝕜 E).injective, hinter]
  ext u
  simp [(toWeakSpace 𝕜 E).image_eq_preimage_symm]

/-- **Weak lower semicontinuity.** A lower semicontinuous quasiconvex function on a locally convex
space is lower semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_comp_toWeakSpace_symm (hf : QuasiconvexOn ℝ univ f)
    (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u) := by
  rw [← lowerSemicontinuousOn_univ_iff] at hlsc ⊢
  simpa only [image_univ, EquivLike.range_eq_univ] using
    hf.lowerSemicontinuousOn_comp_toWeakSpace_symm hlsc

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
