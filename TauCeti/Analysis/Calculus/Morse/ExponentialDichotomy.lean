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
* `TauCeti.IsNondegenerateCriticalPoint.exists_stableProjection_exponential_bounds`: the same
  estimates in the projection form consumed by the Lyapunov--Perron construction.

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

end ContDiffAt

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

/-- The stable projection at a nondegenerate critical point gives an exponential dichotomy for
the negative Hessian operator. The common constant `K` absorbs the operator norms of the
projection and its complementary projection. -/
theorem IsNondegenerateCriticalPoint.exists_stableProjection_exponential_bounds
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ (K alpha : ℝ≥0), 0 < K ∧ 0 < alpha ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E,
        ‖NormedSpace.exp (t • (-hessianOperator f x))
          (h.contDiffAt.stableProjection
            (LinearMap.ker_eq_bot.2 h.isInvertible_hessianOperator.injective) v)‖ ≤
          K * Real.exp (-alpha * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E,
        ‖NormedSpace.exp (t • (-hessianOperator f x))
          (v - h.contDiffAt.stableProjection
            (LinearMap.ker_eq_bot.2 h.isInvertible_hessianOperator.injective) v)‖ ≤
          K * Real.exp (alpha * t) * ‖v‖) := by
  let hker : LinearMap.ker (hessianOperator f x).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.2 h.isInvertible_hessianOperator.injective
  let P := h.contDiffAt.stableProjection hker
  obtain ⟨alpha, halpha, hs, hu⟩ := h.contDiffAt.exists_linearized_flow_exponential_bounds
  have hs' : ∀ (t : ℝ), 0 ≤ t → ∀ w ∈ P.range,
      ‖NormedSpace.exp (t • (-hessianOperator f x)) w‖ ≤
        Real.exp (-alpha * t) * ‖w‖ := by
    intro t ht w hw
    have hw' : w ∈ h.contDiffAt.stableLinearSubspace := by
      simpa only [P, h.contDiffAt.range_stableProjection hker] using hw
    rw [smul_neg, ← neg_smul]
    simpa only [linearizedNegativeGradientFlow_apply] using hs t ht w hw'
  have hu' : ∀ (t : ℝ), t ≤ 0 → ∀ w ∈ P.ker,
      ‖NormedSpace.exp (t • (-hessianOperator f x)) w‖ ≤
        Real.exp (alpha * t) * ‖w‖ := by
    intro t ht w hw
    have hw' : w ∈ h.contDiffAt.unstableLinearSubspace := by
      simpa only [P, h.contDiffAt.ker_stableProjection hker] using hw
    rw [smul_neg, ← neg_smul]
    simpa only [linearizedNegativeGradientFlow_apply] using hu t ht w hw'
  simpa only [P, hker] using
    ContinuousLinearMap.exists_projection_exponential_bounds
      (h.contDiffAt.isIdempotentElem_stableProjection hker) halpha hs' hu'

end TauCeti

end
