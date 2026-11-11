/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# The product rule for applying a family of continuous linear maps

For maps `A : M → F₁ →L[𝕜] F₂` and `p : M → F₁` on a manifold, both differentiable at `x`, the
derivative of `y ↦ A y (p y)` obeys the product rule `d(A p) = (dA) p + A (dp)`. This is the
manifold counterpart of Mathlib's `fderiv_clm_apply`, stated for `mvfderiv`.

## Main results

* `TauCeti.mvfderiv_clm_apply`: the product rule for the application of continuous linear maps.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

namespace TauCeti

/-- The **product rule** for the application `y ↦ A y (p y)` of a family of continuous linear maps
to a vector-valued function on a manifold. -/
theorem mvfderiv_clm_apply {A : M → F₁ →L[𝕜] F₂} {p : M → F₁} {x : M} (hA : MDiffAt A x)
    (hp : MDiffAt p x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ A y (p y)) x v = mvfderiv I A x v (p x) + A x (mvfderiv I p x v) := by
  have hpair : HasMFDerivAt I 𝓘(𝕜, (F₁ →L[𝕜] F₂) × F₁) (fun y ↦ (A y, p y)) x
      ((mvfderiv I A x).prod (mvfderiv I p x)) :=
    hA.hasMFDerivAt.prodMk hp.hasMFDerivAt
  have happ : HasFDerivAt (fun q : (F₁ →L[𝕜] F₂) × F₁ ↦ q.1 q.2)
      (isBoundedBilinearMap_apply.deriv (A x, p x)) (A x, p x) :=
    isBoundedBilinearMap_apply.hasFDerivAt (A x, p x)
  have hpair' : mvfderiv I (fun y ↦ (A y, p y)) x = (mvfderiv I A x).prod (mvfderiv I p x) := by
    apply ContinuousLinearMap.ext
    intro w
    rw [mvfderiv_apply_eq_mfderiv_apply (fun y ↦ (A y, p y)) x w, hpair.mfderiv]
    exact ContinuousLinearMap.prod_apply _ _ _
  rw [← Function.comp_def (fun q : (F₁ →L[𝕜] F₂) × F₁ ↦ q.1 q.2) fun y ↦ (A y, p y),
    mvfderiv_comp_apply_of_differentiableAt (g := fun y ↦ (A y, p y))
      (φ := fun q : (F₁ →L[𝕜] F₂) × F₁ ↦ q.1 q.2) happ.differentiableAt hpair.mdifferentiableAt,
    happ.fderiv, hpair']
  simp [IsBoundedBilinearMap.deriv_apply, add_comm]

end TauCeti
