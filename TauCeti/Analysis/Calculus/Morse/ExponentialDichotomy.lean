/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.HessianFlow
public import TauCeti.Analysis.ODE.ExponentialDichotomy

/-!
# Exponential bounds for a linearized Morse flow

The linearized negative-gradient flow contracts the positive Hessian subspace exponentially in
forward time and the negative Hessian subspace exponentially in backward time, with one common
positive rate.  At a nondegenerate critical point these are the complementary stable and unstable
linear subspaces, so the bounds form an exponential dichotomy.

This is the quantitative hyperbolicity estimate used by the Lyapunov--Perron proof of the local
stable-manifold theorem.  The subspaces and the qualitative identification of their asymptotic
sets are provided by `TauCeti.Analysis.Calculus.Morse.SpectralSplitting` and
`TauCeti.Analysis.Calculus.Morse.HessianFlow`; this file supplies the uniform spectral gap that
turns convergence into contraction.

## Main declaration

* `ContDiffAt.exists_linearized_flow_exponential_bounds`: the stable and unstable linearized
  flows contract exponentially with a common positive rate.
* `ContDiffAt.exists_stableProjection_exponential_bounds`: the same estimates in the projection
  form consumed by the Lyapunov--Perron construction.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open InnerProductSpace
open scoped NNReal

noncomputable section

namespace ContDiffAt

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

/-- At a twice continuously differentiable point, the linearized negative-gradient flow contracts
the positive Hessian subspace exponentially in forward time and the negative Hessian subspace
exponentially in backward time.  The same positive rate works in both directions. -/
theorem exists_linearized_flow_exponential_bounds (hf : ContDiffAt ℝ 2 f x) :
    ∃ alpha > 0,
      (∀ (t : ℝ), 0 ≤ t → ∀ v ∈ hf.stableLinearSubspace,
        ‖linearizedNegativeGradientFlow f x t v‖ ≤ Real.exp (-alpha * t) * ‖v‖) ∧
      (∀ (t : ℝ), t ≤ 0 → ∀ v ∈ hf.unstableLinearSubspace,
        ‖linearizedNegativeGradientFlow f x t v‖ ≤ Real.exp (alpha * t) * ‖v‖) := by
  let hT := hf.isSelfAdjoint_hessianOperator.isSymmetric
  obtain ⟨alpha, halpha, hstable, hunstable⟩ :=
    hT.exists_exponential_bounds_spectralSubspaces rfl
  refine ⟨alpha, halpha, ?_, ?_⟩
  · intro t ht v hv
    rw [linearizedNegativeGradientFlow_apply]
    simpa only [ContinuousLinearMap.flow_apply, smul_neg, neg_smul] using
      hstable t ht v ((hT.mem_positiveSpectralSubspace_iff rfl).2
        (hf.mem_stableLinearSubspace_iff.mp hv))
  · intro t ht v hv
    rw [linearizedNegativeGradientFlow_apply]
    simpa only [ContinuousLinearMap.flow_apply, smul_neg, neg_smul] using
      hunstable t ht v ((hT.mem_negativeSpectralSubspace_iff rfl).2
        (hf.mem_unstableLinearSubspace_iff.mp hv))

/-- When the Hessian is injective, the stable projection gives an exponential dichotomy for the
negative Hessian operator. The common constant `K` absorbs the operator norms of the projection
and its complementary projection. -/
theorem exists_stableProjection_exponential_bounds (hf : ContDiffAt ℝ 2 f x)
    (hker : LinearMap.ker (hessianOperator f x).toLinearMap = ⊥) :
    ∃ (K alpha : ℝ≥0), 0 < K ∧ 0 < alpha ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E,
        ‖NormedSpace.exp (t • (-hessianOperator f x)) (hf.stableProjection hker v)‖ ≤
          K * Real.exp (-alpha * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E,
        ‖NormedSpace.exp (t • (-hessianOperator f x)) (v - hf.stableProjection hker v)‖ ≤
          K * Real.exp (alpha * t) * ‖v‖) := by
  obtain ⟨alpha, halpha, hs, hu⟩ := hf.exists_linearized_flow_exponential_bounds
  have hs' : ∀ (t : ℝ), 0 ≤ t → ∀ w ∈ (hf.stableProjection hker).range,
      ‖NormedSpace.exp (t • (-hessianOperator f x)) w‖ ≤
        Real.exp (-alpha * t) * ‖w‖ := by
    intro t ht w hw
    have hw' : w ∈ hf.stableLinearSubspace := by
      simpa only [hf.range_stableProjection hker] using hw
    rw [smul_neg, ← neg_smul]
    simpa only [linearizedNegativeGradientFlow_apply] using hs t ht w hw'
  have hu' : ∀ (t : ℝ), t ≤ 0 → ∀ w ∈ (hf.stableProjection hker).ker,
      ‖NormedSpace.exp (t • (-hessianOperator f x)) w‖ ≤
        Real.exp (alpha * t) * ‖w‖ := by
    intro t ht w hw
    have hw' : w ∈ hf.unstableLinearSubspace := by
      simpa only [hf.ker_stableProjection hker] using hw
    rw [smul_neg, ← neg_smul]
    simpa only [linearizedNegativeGradientFlow_apply] using hu t ht w hw'
  exact ContinuousLinearMap.exists_projection_exponential_bounds
    (hf.isIdempotentElem_stableProjection hker) halpha hs' hu'

end ContDiffAt

end
