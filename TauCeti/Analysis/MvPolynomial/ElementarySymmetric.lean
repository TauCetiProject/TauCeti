/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PDeriv

/-!
# Derivatives of the elementary symmetric functions

Over a nontrivially normed field `𝕜`, the elementary symmetric function
`σ_{k+1}(μ) = e_{k+1}(μ)` of `μ : σ → 𝕜` is differentiable, and its partial derivative in the
`i`-th coordinate is `σ_{k;i}(μ)`, the value of `e_k` with the `i`-th entry of `μ` set to zero:

`∂σ_{k+1}/∂μ_i = σ_{k;i}`.

This is the analytic form of `TauCeti.eval_pderiv_esymm_succ`. It is the gradient of `σ_{k+1}`
that enters the ellipticity of the Hessian operators `σ_k^{1/k}` on the Gårding cones and the
concavity of Hessian quotients. The derivative of `σ_0 = 1` is zero (`MvPolynomial.esymm_zero`).

## Main results

* `TauCeti.hasFDerivAt_eval_esymm_succ`: the Fréchet derivative of `σ_{k+1}` at `μ` is
  `v ↦ ∑_i σ_{k;i}(μ) v_i`.
* `TauCeti.fderiv_eval_esymm_succ_single`: the partial derivative `∂σ_{k+1}/∂μ_i (μ)` is
  `σ_{k;i}(μ)`.
-/

public section

open Function MvPolynomial

namespace TauCeti

variable {𝕜 σ : Type*} [NontriviallyNormedField 𝕜] [Fintype σ] [DecidableEq σ]

/-- **The derivative of an elementary symmetric function**: the Fréchet derivative of
`σ_{k+1}` at `μ` is `v ↦ ∑_i σ_{k;i}(μ) v_i`, where `σ_{k;i}(μ)` is the value of `e_k` with the
`i`-th entry of `μ` set to zero. -/
theorem hasFDerivAt_eval_esymm_succ (μ : σ → 𝕜) (k : ℕ) :
    HasFDerivAt (fun ν ↦ eval ν (esymm σ 𝕜 (k + 1)))
      (∑ i, eval (update μ i 0) (esymm σ 𝕜 k) •
        (ContinuousLinearMap.proj i : (σ → 𝕜) →L[𝕜] 𝕜)) μ := by
  simpa only [eval_pderiv_esymm_succ] using (esymm σ 𝕜 (k + 1)).hasFDerivAt_eval μ

/-- **The partial derivatives of an elementary symmetric function**:
`∂σ_{k+1}/∂μ_i (μ) = σ_{k;i}(μ)`, the value of `e_k` with the `i`-th entry of `μ` set to zero. -/
@[simp]
theorem fderiv_eval_esymm_succ_single (μ : σ → 𝕜) (i : σ) (k : ℕ) :
    fderiv 𝕜 (fun ν ↦ eval ν (esymm σ 𝕜 (k + 1))) μ (Pi.single i 1) =
      eval (update μ i 0) (esymm σ 𝕜 k) := by
  simp [(hasFDerivAt_eval_esymm_succ μ k).fderiv, Pi.single_apply]

end TauCeti
