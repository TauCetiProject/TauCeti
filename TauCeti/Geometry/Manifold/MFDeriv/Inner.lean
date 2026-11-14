/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The derivative of an inner product of vector-valued functions on a manifold

For two functions `g, g' : M → F` from a real manifold to an `RCLike` inner product space, both
differentiable at `x`, the derivative of `y ↦ ⟪g y, g' y⟫` obeys the product rule
`d⟪g, g'⟫ = ⟪dg, g'⟫ + ⟪g, dg'⟫`. This is the manifold counterpart of Mathlib's
`fderiv_inner_apply`, stated for `mvfderiv`.

On an open subset of a real inner product space, the derivative of the squared distance
`y ↦ ‖y - a‖ ^ 2` vanishes exactly at the centre `a`.
The squared-norm chain rule gives the differential for any differentiable map into a real inner
product space; at a zero of the map, this differential vanishes.

## Main results

* `TauCeti.mvfderiv_inner_apply`: the product rule for the inner product.
* `TauCeti.mvfderiv_norm_sq_comp`: the chain rule for the squared norm in a real inner product
  space.
* `TauCeti.mvfderiv_norm_sq_comp_eq_zero_of_eq_zero`: the squared norm of a differentiable
  map into a real inner product space has vanishing differential at a zero.
* `TauCeti.mvfderiv_norm_sq_sub_subtypeVal_eq_zero_iff`: along the inclusion of an open subset,
  the only critical point of squared distance is the centre.
-/

public section

open TopologicalSpace
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {𝕜 : Type*} [RCLike 𝕜]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedSpace ℝ F]

namespace TauCeti

/-- The **product rule** for the inner product of two vector-valued functions on a manifold. -/
theorem mvfderiv_inner_apply {g g' : M → F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ inner 𝕜 (g y) (g' y)) x v =
      inner 𝕜 (mvfderiv I g x v) (g' x) + inner 𝕜 (g x) (mvfderiv I g' x v) := by
  have hpair : HasMFDerivAt I 𝓘(ℝ, F × F) (fun y ↦ (g y, g' y)) x
      ((mvfderiv I g x).prod (mvfderiv I g' x)) :=
    hg.hasMFDerivAt.prodMk hg'.hasMFDerivAt
  have hinner : HasFDerivAt (fun p : F × F ↦ inner 𝕜 p.1 p.2)
      (fderivInnerCLM 𝕜 (g x, g' x)) (g x, g' x) :=
    isBoundedBilinearMap_inner.hasFDerivAt (g x, g' x)
  have hpair' : mvfderiv I (fun y ↦ (g y, g' y)) x =
      (mvfderiv I g x).prod (mvfderiv I g' x) := by
    apply ContinuousLinearMap.ext
    intro w
    rw [mvfderiv_apply_eq_mfderiv_apply (fun y ↦ (g y, g' y)) x w, hpair.mfderiv]
    exact ContinuousLinearMap.prod_apply _ _ _
  rw [← Function.comp_def (fun p : F × F ↦ inner 𝕜 p.1 p.2) fun y ↦ (g y, g' y),
    TauCeti.mvfderiv_comp_apply_of_differentiableAt
    (g := fun y ↦ (g y, g' y)) (φ := fun p : F × F ↦ inner 𝕜 p.1 p.2)
    hinner.differentiableAt hpair.mdifferentiableAt, hinner.fderiv,
    hpair']
  simp only [fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, add_comm]

section Real

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] {p : M}

/-- The differential of the squared norm of a differentiable map into a real inner product
space is twice the inner product with the value of the map, composed with its differential. -/
theorem mvfderiv_norm_sq_comp {f : M → G} (hf : MDiffAt f p) :
    mvfderiv I (fun q ↦ ‖f q‖ ^ 2) p =
      2 • (innerSL ℝ (f p)).comp (mvfderiv I f p) := by
  ext v
  simpa only [Function.comp_def, fderiv_norm_sq_apply, smul_apply,
    ContinuousLinearMap.comp_apply] using
    mvfderiv_comp_apply_of_differentiableAt (φ := fun z : G ↦ ‖z‖ ^ 2)
      ((contDiff_norm_sq ℝ (n := 2)).differentiable (by norm_num)).differentiableAt hf v

/-- At a zero of a differentiable map into a real inner product space, its squared norm has
vanishing differential. -/
theorem mvfderiv_norm_sq_comp_eq_zero_of_eq_zero {f : M → G} (hf : MDiffAt f p)
    (hzero : f p = 0) : mvfderiv I (fun q ↦ ‖f q‖ ^ 2) p = 0 := by
  simp [mvfderiv_norm_sq_comp hf, hzero]

/-- Along the inclusion of an open subset of a real inner product space, the squared distance
from `a` has a critical point exactly at `a`. -/
@[simp]
theorem mvfderiv_norm_sq_sub_subtypeVal_eq_zero_iff (U : Opens G) (a : G) (x : U) :
    mvfderiv 𝓘(ℝ, G) (fun y : U ↦ ‖(y : G) - a‖ ^ 2) x = 0 ↔ (x : G) = a := by
  have hval : MDifferentiableAt 𝓘(ℝ, G) 𝓘(ℝ, G) (Subtype.val : U → G) x :=
    (contMDiff_subtype_val (U := U) x).mdifferentiableAt one_ne_zero
  have hd := mvfderiv_norm_sq_comp (hval.sub (mdifferentiableAt_const (c := a)))
  rw [mvfderiv_sub hval mdifferentiableAt_const, mvfderiv_const, sub_zero] at hd
  have hd_apply (v : TangentSpace 𝓘(ℝ, G) x) :
      mvfderiv 𝓘(ℝ, G) (fun y : U ↦ ‖(y : G) - a‖ ^ 2) x v =
        2 * inner ℝ ((x : G) - a) (mvfderiv 𝓘(ℝ, G) (Subtype.val : U → G) x v) := by
    simpa only [Pi.sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, two_smul, add_apply, two_mul] using DFunLike.congr_fun hd v
  have happ (v : G) : mvfderiv 𝓘(ℝ, G) (fun y : U ↦ ‖(y : G) - a‖ ^ 2) x v =
      2 * inner ℝ ((x : G) - a) v := by
    -- Read the inclusion's tangent vector in `G` using the canonical derivative identity.
    exact (hd_apply v).trans (congrArg (fun w : G ↦ 2 * inner ℝ ((x : G) - a) w)
      (Manifold.mvfderiv_subtype_val_apply x v))
  constructor
  · intro h
    have h0 := happ ((x : G) - a)
    rw [h, real_inner_self_eq_norm_sq] at h0
    have h1 : 2 * ‖(x : G) - a‖ ^ 2 = 0 := h0.symm
    simpa [sub_eq_zero] using h1
  · intro h
    -- Tangent vectors of the open subset are read as vectors of `G`.
    refine ContinuousLinearMap.ext fun v : G ↦ ?_
    rw [happ v, h, sub_self, inner_zero_left, mul_zero]
    rfl

end Real

end TauCeti
