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
    E →ₗᵢ[𝕜] lp (fun _ : Metric.closedBall (0 : StrongDual 𝕜 E) 1 ↦ 𝕜) ∞ :=
  have hf (φ : Metric.closedBall (0 : StrongDual 𝕜 E) 1) : ‖(φ.1 : E →L[𝕜] 𝕜)‖ ≤ 1 :=
    mem_closedBall_zero_iff.mp φ.2
  let J := ContinuousLinearMap.piLpInfty (fun φ : Metric.closedBall (0 : StrongDual 𝕜 E) 1 ↦
    (φ.1 : E →L[𝕜] 𝕜)) (bddAbove_def.2 ⟨1, Set.forall_mem_range.2 hf⟩)
  { J.toLinearMap with
    norm_map' x := by
      refine le_antisymm ?_ ?_
      · simpa using J.le_of_opNorm_le (ContinuousLinearMap.norm_piLpInfty_le _ zero_le_one hf) x
      · obtain ⟨φ, hφ, hx⟩ := exists_dual_vector'' 𝕜 x
        simpa [J, hx] using lp.norm_apply_le_norm (by simp) (J x)
          ⟨φ, mem_closedBall_zero_iff.mpr hφ⟩ }

variable {𝕜 E}

/-- Evaluation at a dual unit-ball coordinate is the original functional. -/
@[simp]
theorem dualBallEmbedding_apply (x : E) (φ : Metric.closedBall (0 : StrongDual 𝕜 E) 1) :
    dualBallEmbedding 𝕜 E x φ = (φ : StrongDual 𝕜 E) x := by
  simp [dualBallEmbedding]

/-- Composing the embedding with a dual unit-ball coordinate recovers the functional. -/
@[simp]
theorem evalCLM_comp_dualBallEmbedding (φ : Metric.closedBall (0 : StrongDual 𝕜 E) 1) :
    lp.evalCLM 𝕜 _ ∞ φ ∘L (dualBallEmbedding 𝕜 E).toContinuousLinearMap =
      (φ : StrongDual 𝕜 E) := by
  ext x
  simp

end TauCeti
