/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Calculus.IteratedGradient
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The Laplacian as the trace of the Hessian endomorphism

For a scalar function `f` on a finite-dimensional real inner product space `E`, the derivative of
the gradient, `TauCeti.iteratedGradientChain f 1 x : E →L[ℝ] E`, is the Hessian of `f` at `x`
represented as an endomorphism of `E`. This file records that its trace is the Laplacian:
`Δ f x = tr (D∇f x)`. The identity is basis-free, and holds without any differentiability
hypothesis because both sides are built from Mathlib's totalized Fréchet derivative.

It is the classical form of the statement that the Laplacian of a Sobolev function in
`W^{2,p}` is the trace of its weak Hessian, which identifies `Δ` with a bounded linear image of the
second derivatives in `Lᵖ` estimates.

## Main declarations

* `TauCeti.laplacian_eq_trace_iteratedGradientChain_one`: `Δ f x = tr (D∇f x)`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Laplacian is the trace of the Hessian endomorphism.** For every scalar function `f` and
every point `x`, `Δ f x` is the trace of the derivative of the gradient of `f` at `x`. No
differentiability is needed: both sides use Mathlib's totalized Fréchet derivative. -/
theorem laplacian_eq_trace_iteratedGradientChain_one (f : E → ℝ) (x : E) :
    Δ f x = LinearMap.trace ℝ E (iteratedGradientChain f 1 x) := by
  set b := stdOrthonormalBasis ℝ E
  -- The derivative of the gradient is the Riesz representative of the second derivative.
  have hD :
      iteratedGradientChain f 1 x = continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ f) x) := by
    -- `∇f = (toDual ℝ E).symm ∘ fderiv ℝ f`, and `continuousLinearMapOfBilin B` is
    -- `(toDual ℝ E).symm` composed with `B`.
    have hgrad : gradient f = (toDual ℝ E).symm.toContinuousLinearEquiv ∘ fderiv ℝ f := by
      funext y
      simp only [gradient, Function.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [iteratedGradientChain_succ, iteratedGradientChain_zero, hgrad, continuousLinearMapOfBilin,
      ContinuousLinearEquiv.comp_fderiv]
  rw [LinearMap.trace_eq_sum_inner _ b, laplacian_eq_iteratedFDeriv_orthonormalBasis f b, hD]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply, ContinuousLinearMap.coe_coe, real_inner_comm,
    continuousLinearMapOfBilin_apply]
  simp

end TauCeti
