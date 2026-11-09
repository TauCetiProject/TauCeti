/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Topology.Algebra.Module.Trace

import Mathlib.LinearAlgebra.PID

/-!
# The trace of an operator on a finite-dimensional inner product space

On a finite-dimensional inner product space `V` over `ℝ` or `ℂ`, the trace of a continuous
endomorphism is bounded by the dimension times its operator norm:
`‖tr T‖ ≤ dim V * ‖T‖` (`ContinuousLinearMap.norm_traceCLM_le`). Expanding the trace in an
orthonormal basis `(bᵢ)` gives `tr T = ∑ᵢ ⟪bᵢ, T bᵢ⟫`, and each term is at most `‖T‖`.

This is the bound that controls a non-divergence-form operator `tr (A ∘ D²u)` by the operator
norms of its coefficient field `A` and of the Hessian `D²u`.

Restricting to the range gives the sharper estimate
`‖tr T‖ ≤ rank T * ‖T‖` (`ContinuousLinearMap.norm_traceCLM_le_finrank_range_mul`).
It applies without self-adjointness or normality and controls traces of low-rank perturbations.
-/

public section

namespace TauCeti

open Module
open scoped InnerProductSpace

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- The trace of a continuous endomorphism of a finite-dimensional inner product space is bounded
by the dimension times the operator norm: `‖tr T‖ ≤ dim V * ‖T‖`. -/
theorem _root_.ContinuousLinearMap.norm_traceCLM_le (T : V →L[𝕜] V) :
    ‖traceCLM 𝕜 V T‖ ≤ finrank 𝕜 V * ‖T‖ := by
  set b := stdOrthonormalBasis 𝕜 V
  rw [traceCLM_apply, LinearMap.trace_eq_sum_inner _ b]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖⟪b i, (T : V →ₗ[𝕜] V) (b i)⟫_𝕜‖
      ≤ ∑ _i : Fin (finrank 𝕜 V), ‖T‖ := by
        refine Finset.sum_le_sum fun i _ => (norm_inner_le_norm _ _).trans ?_
        rw [b.norm_eq_one, one_mul]
        exact (T.le_opNorm _).trans_eq (by rw [b.norm_eq_one, mul_one])
    _ = finrank 𝕜 V * ‖T‖ := by simp

/-- The trace is bounded by the rank times the operator norm, without any normality hypothesis.
In particular, low-rank operators have dimension-independent trace bounds. -/
theorem _root_.ContinuousLinearMap.norm_traceCLM_le_finrank_range_mul (T : V →L[𝕜] V) :
    ‖traceCLM 𝕜 V T‖ ≤ finrank 𝕜 (LinearMap.range T.toLinearMap) * ‖T‖ := by
  let p := LinearMap.range T.toLinearMap
  let S : p →L[𝕜] p := T.restrict (fun x _ => LinearMap.mem_range_self T.toLinearMap x)
  have htrace : traceCLM 𝕜 p S = traceCLM 𝕜 V T := by
    simp only [traceCLM_apply]
    exact LinearMap.trace_restrict_eq_of_forall_mem p T.toLinearMap
      (fun x => LinearMap.mem_range_self T.toLinearMap x)
  have hnorm : ‖S‖ ≤ ‖T‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    exact T.le_opNorm x
  rw [← htrace]
  exact S.norm_traceCLM_le.trans (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _))

end TauCeti
