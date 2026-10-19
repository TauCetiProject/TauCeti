/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The derivative of an inner product of vector-valued functions on a manifold

For two functions `g, g' : M → F` from a manifold to a real inner product space, both
differentiable at `x`, the derivative of `y ↦ ⟪g y, g' y⟫` obeys the product rule
`d⟪g, g'⟫ = ⟪dg, g'⟫ + ⟪g, dg'⟫`. This is the manifold counterpart of Mathlib's
`fderiv_inner_apply`, stated for `mvfderiv`.

## Main result

* `mvfderiv_inner_apply`: the product rule for the inner product.
-/

public section

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The **product rule** for the inner product of two vector-valued functions on a manifold. -/
theorem mvfderiv_inner_apply {g g' : M → F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ inner ℝ (g y) (g' y)) x v =
      inner ℝ (mvfderiv I g x v) (g' x) + inner ℝ (g x) (mvfderiv I g' x v) := by
  have hpair : HasMFDerivAt I 𝓘(ℝ, F × F) (fun y ↦ (g y, g' y)) x
      ((mvfderiv I g x).prod (mvfderiv I g' x)) :=
    hg.hasMFDerivAt.prodMk hg'.hasMFDerivAt
  have hinner : HasFDerivAt (fun p : F × F ↦ inner ℝ p.1 p.2)
      (fderivInnerCLM ℝ (g x, g' x)) (g x, g' x) :=
    isBoundedBilinearMap_inner.hasFDerivAt (g x, g' x)
  have h := mvfderiv_comp_apply x hinner.differentiableAt.mdifferentiableAt
    hpair.mdifferentiableAt v
  rw [Function.comp_def] at h
  rw [h, mvfderiv_eq_fderiv, hpair.mfderiv, hinner.fderiv, ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply, add_comm]
  -- What remains differs only by `NormedSpace.fromTangentSpace`, the identity of `F × F`.
  rfl
