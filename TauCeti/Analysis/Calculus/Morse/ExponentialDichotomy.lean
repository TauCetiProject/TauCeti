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
        ‖NormedSpace.exp (t • (-hessianOperator f x)) (h.stableProjection v)‖ ≤
          K * Real.exp (-alpha * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E,
        ‖NormedSpace.exp (t • (-hessianOperator f x)) (v - h.stableProjection v)‖ ≤
          K * Real.exp (alpha * t) * ‖v‖) := by
  let P := h.stableProjection
  let K : ℝ≥0 := ‖P‖₊ + ‖ContinuousLinearMap.id ℝ E - P‖₊ + 1
  obtain ⟨alpha, halpha, hs, hu⟩ := h.contDiffAt.exists_linearized_flow_exponential_bounds
  have hP_le : ‖P‖ ≤ (K : ℝ) := by
    dsimp only [K]
    push_cast
    nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ E - P)]
  have hPc_le : ‖ContinuousLinearMap.id ℝ E - P‖ ≤ (K : ℝ) := by
    dsimp only [K]
    push_cast
    nlinarith [norm_nonneg P]
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, ⟨alpha, halpha.le⟩, hK, by exact_mod_cast halpha, ?_, ?_⟩
  · intro t ht v
    have hPv : P v ∈ h.contDiffAt.stableLinearSubspace := by
      rw [← h.range_stableProjection]
      exact ⟨v, rfl⟩
    have hbound := hs t ht (P v) hPv
    have hop := P.le_opNorm v
    rw [linearizedNegativeGradientFlow_apply] at hbound
    calc
      ‖NormedSpace.exp (t • (-hessianOperator f x)) (P v)‖ =
          ‖NormedSpace.exp ((-t) • hessianOperator f x) (P v)‖ := by
            rw [smul_neg, neg_smul]
      _ ≤ Real.exp (-alpha * t) * ‖P v‖ := hbound
      _ ≤ Real.exp (-alpha * t) * (‖P‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left hop (Real.exp_nonneg _)
      _ = Real.exp (-alpha * t) * ‖P‖ * ‖v‖ := by ring
      _ ≤ Real.exp (-alpha * t) * (K : ℝ) * ‖v‖ := by
        gcongr
      _ = (K : ℝ) * Real.exp (-alpha * t) * ‖v‖ := by ring
      _ = (K : ℝ) * Real.exp (-((⟨alpha, halpha.le⟩ : ℝ≥0) : ℝ) * t) * ‖v‖ := rfl
  · intro t ht v
    have hPP : P (P v) = P v := by
      dsimp only [P]
      rw [← mul_apply_eq_comp, h.isIdempotentElem_stableProjection]
    have hvP : v - P v ∈ h.contDiffAt.unstableLinearSubspace := by
      rw [← h.ker_stableProjection, LinearMap.mem_ker, map_sub]
      dsimp only [P] at hPP ⊢
      exact sub_eq_zero.mpr hPP.symm
    have hbound := hu t ht (v - P v) hvP
    have hop := (ContinuousLinearMap.id ℝ E - P).le_opNorm v
    rw [linearizedNegativeGradientFlow_apply] at hbound
    have hdiff : ‖v - P v‖ ≤ ‖ContinuousLinearMap.id ℝ E - P‖ * ‖v‖ := by
      simpa using hop
    calc
      ‖NormedSpace.exp (t • (-hessianOperator f x)) (v - P v)‖ =
          ‖NormedSpace.exp ((-t) • hessianOperator f x) (v - P v)‖ := by
            rw [smul_neg, neg_smul]
      _ ≤ Real.exp (alpha * t) * ‖v - P v‖ := hbound
      _ ≤ Real.exp (alpha * t) * (‖ContinuousLinearMap.id ℝ E - P‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left hdiff (Real.exp_nonneg _)
      _ = Real.exp (alpha * t) * ‖ContinuousLinearMap.id ℝ E - P‖ * ‖v‖ := by ring
      _ ≤ Real.exp (alpha * t) * (K : ℝ) * ‖v‖ := by
        gcongr
      _ = (K : ℝ) * Real.exp (alpha * t) * ‖v‖ := by ring
      _ = (K : ℝ) * Real.exp (((⟨alpha, halpha.le⟩ : ℝ≥0) : ℝ) * t) * ‖v‖ := rfl

end TauCeti

end
