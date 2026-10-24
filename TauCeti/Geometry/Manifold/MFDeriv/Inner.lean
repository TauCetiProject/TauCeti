/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The derivative of an inner product of vector-valued functions on a manifold

For two functions `g, g' : M → F` from a real manifold to an `RCLike` inner product space, both
differentiable at `x`, the derivative of `y ↦ ⟪g y, g' y⟫` obeys the product rule
`d⟪g, g'⟫ = ⟪dg, g'⟫ + ⟪g, dg'⟫`. This is the manifold counterpart of Mathlib's
`fderiv_inner_apply`, stated for `mvfderiv`.

## Main result

* `TauCeti.mvfderiv_inner_apply`: the product rule for the inner product.
-/

public section

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

end TauCeti
