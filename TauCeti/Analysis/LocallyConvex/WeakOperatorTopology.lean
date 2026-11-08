/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Comparing the strong and weak operator topologies

The identity from the pointwise-convergence copy of continuous linear maps to the weak
operator copy is continuous. Centralizers of sets of operators are weak-operator closed.
These facts allow strong approximation results to identify weak operator closures without
changing the norm topology on the original operator space.
-/

public section

open scoped Topology

namespace ContinuousLinearMapWOT

variable {𝕜₁ 𝕜₂ E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F]

/-- Pointwise (strong operator) convergence is stronger than weak operator convergence. -/
@[fun_prop]
theorem continuous_ofPointwiseConvergenceCLM :
    Continuous (fun T : E →SLₚₜ[σ] F => ofCLM (T : E →SL[σ] F)) := by
  apply continuous_of_dual_apply_continuous
  intro x y
  exact y.continuous.comp (continuous_eval_const x)

end ContinuousLinearMapWOT

namespace Set

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]
    [SeparatingDual 𝕜 E]

/-- The commutant of any set of operators is closed in the weak operator topology. -/
theorem isClosed_image_ofCLM_centralizer (s : Set (E →L[𝕜] E)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' s.centralizer) := by
  have h : ContinuousLinearMapWOT.ofCLM '' s.centralizer =
      (ContinuousLinearMapWOT.ofCLM '' s).centralizer := by
    ext T
    obtain ⟨T, rfl⟩ := ContinuousLinearMapWOT.ofCLM_surjective T
    rw [ContinuousLinearMapWOT.ofCLM_injective.mem_set_image]
    simp only [mem_centralizer_iff, forall_mem_image,
      ← ContinuousLinearMapWOT.ofCLM_mul, ContinuousLinearMapWOT.ofCLM_injective.eq_iff]
  rw [h]
  exact isClosed_centralizer _

end Set
