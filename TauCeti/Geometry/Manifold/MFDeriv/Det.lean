/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Analysis.Calculus.FDeriv.Det
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Jacobi's formula on a manifold

Let `A` be a square-matrix-valued function on a manifold whose entries are differentiable at `x`,
with `A x` invertible. Then the determinant of `A` is differentiable at `x`, and along a tangent
vector `v` its derivative is given by Jacobi's formula

`d (det A) (v) = det (A x) * trace ((A x)⁻¹ * dA (v))`,

where `dA (v)` is the matrix of the derivatives of the entries of `A` along `v`. The statement
only involves derivatives of scalar functions, so no normed structure on matrices appears in it;
the proof reads `A` as a map into the product space of its entries and applies the flat formula
`Matrix.fderiv_det_apply`.
-/

public section

open scoped Manifold Matrix

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
/-- **Jacobi's formula on a manifold.** If the entries of a matrix-valued function `A` are
differentiable at `x` and `A x` has invertible determinant, then along a tangent vector `v` the
derivative of `det A` is `det (A x) * trace ((A x)⁻¹ * dA (v))`, where `dA (v)` is the matrix of
the derivatives of the entries of `A` along `v`. -/
theorem mvfderiv_det_apply {A : M → Matrix n n 𝕜} {x : M}
    (hA : ∀ i j, MDifferentiableAt I 𝓘(𝕜) (fun y ↦ A y i j) x) (hdet : IsUnit (A x).det)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ (A y).det) x v =
      (A x).det * ((A x)⁻¹ * Matrix.of fun i j ↦ mvfderiv I (fun y ↦ A y i j) x v).trace := by
  -- Read `A` as the map `A'` into the product space `n → n → 𝕜` of its entries, and the
  -- determinant as a function on that space through the identification `L` with matrices.
  let A' : M → n → n → 𝕜 := fun y ↦ Matrix.of.symm (A y)
  let L : (n → n → 𝕜) →L[𝕜] Matrix n n 𝕜 :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv 𝕜).toLinearMap
  have hA'row (i : n) : MDifferentiableAt I 𝓘(𝕜, n → 𝕜) (fun y ↦ A' y i) x :=
    mdifferentiableAt_pi_space.2 fun j ↦ hA i j
  have hA' : MDifferentiableAt I 𝓘(𝕜, n → n → 𝕜) A' x := mdifferentiableAt_pi_space.2 hA'row
  have hentry (i j : n) : mvfderiv I (fun y ↦ A y i j) x v = mvfderiv I A' x v i j := by
    have h₁ := congrArg (fun f ↦ f v) (mvfderiv_apply hA' i)
    have h₂ := congrArg (fun f ↦ f v) (mvfderiv_apply (hA'row i) j)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h₁ h₂
    rw [← h₁]
    exact h₂
  have hdet' : HasFDerivAt (fun B : n → n → 𝕜 ↦ (L B).det)
      (((A x).det • (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n 𝕜 𝕜)).comp
        (LinearMap.toContinuousLinearMap (LinearMap.mulLeft 𝕜 (A x)⁻¹))).comp L) (A' x) :=
    (Matrix.hasFDerivAt_det hdet).comp (A' x) L.hasFDerivAt
  have hLA : (fun y ↦ (L (A' y)).det) = fun y ↦ (A y).det := funext fun y ↦ by simp [L, A']
  have hcomp := mvfderiv_comp_apply_of_differentiableAt hdet'.differentiableAt hA' v
  rw [Function.comp_def, hLA] at hcomp
  rw [hcomp, hdet'.fderiv]
  simp only [hentry]
  generalize mvfderiv I A' x v = B
  simp [L]

end TauCeti
