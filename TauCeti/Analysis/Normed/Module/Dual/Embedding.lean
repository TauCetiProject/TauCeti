/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Evaluation on the dual unit ball

The map sending `x` to the bounded family `(φ x)` indexed by the closed unit ball of the
continuous dual preserves norms, by Hahn–Banach. Bundling it as a linear isometry gives a
canonical realization of a normed space inside a scalar-valued `ℓ∞` space. In particular,
scalar-valued extension theorems can be applied coordinatewise in this larger space.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

variable (𝕜 E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The canonical norm-preserving evaluation map into `ℓ∞` of the dual unit ball. -/
noncomputable def dualBallEmbedding :
    E →ₗᵢ[𝕜] lp (fun _ : Metric.closedBall (0 : StrongDual 𝕜 E) 1 ↦ 𝕜) ∞ := by
  let f (φ : Metric.closedBall (0 : StrongDual 𝕜 E) 1) : E →L[𝕜] 𝕜 := φ.1
  have hf (φ : Metric.closedBall (0 : StrongDual 𝕜 E) 1) : ‖f φ‖₊ ≤ 1 := by
    exact_mod_cast mem_closedBall_zero_iff.mp φ.2
  let J := ContinuousLinearMap.piLpInfty f 1 hf
  refine ⟨J.toLinearMap, fun x ↦ le_antisymm ?_ ?_⟩
  · have hJ : ‖J‖ ≤ 1 := by
      exact_mod_cast ContinuousLinearMap.nnnorm_piLpInfty_le f 1 hf
    exact (J.le_opNorm x).trans (by
      simpa using mul_le_mul_of_nonneg_right hJ (norm_nonneg x))
  · obtain ⟨φ, hφ, hx⟩ := exists_dual_vector'' 𝕜 x
    let i : Metric.closedBall (0 : StrongDual 𝕜 E) 1 :=
      ⟨φ, mem_closedBall_zero_iff.mpr hφ⟩
    have h := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (J x) i
    simpa [J, f, i, hx] using h

/-- Evaluation at a dual unit-ball coordinate is the original functional. -/
@[simp]
theorem dualBallEmbedding_apply (x : E) (φ : Metric.closedBall (0 : StrongDual 𝕜 E) 1) :
    dualBallEmbedding 𝕜 E x φ = (φ : StrongDual 𝕜 E) x := by
  simp [dualBallEmbedding, ContinuousLinearMap.piLpInfty_apply]

end TauCeti
