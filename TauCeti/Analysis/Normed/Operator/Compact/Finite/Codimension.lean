/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Cover

/-!
# Compact operators are small on subspaces of finite codimension

Given a compact operator and a positive tolerance, there is a closed subspace of finite
codimension on which the operator norm is at most that tolerance. Neither space needs to
have the approximation property, and the operator need not be approximated by finite-rank
operators. Taking a finite `(ε / 2)`-cover of the totally bounded unit-ball image and applying
`ContinuousLinearMap.exists_rank_quotient_le_nnnorm_comp_subtypeL_le_of_isCover` intersects the
kernels of norming functionals for the centres of the cover.

This is a functional-analytic input to finite-cover finiteness arguments for analytic
cohomology: compact restrictions can be made uniformly small after finitely many linear
conditions. The analytic construction of those restriction operators and their comparison
with sheaf cohomology are separate inputs.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
* J. B. Conway, *A Course in Functional Analysis*, Chapter VI, compact operators.
-/

public section

namespace IsCompactOperator

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {T : E →L[𝕜] F}

/-- A compact operator becomes arbitrarily small on a closed subspace of finite codimension.
The conclusion controls the actual restricted operator in its native subspace norm. -/
theorem exists_finiteDimensional_quotient_norm_comp_subtype_le (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Submodule 𝕜 E, IsClosed (K : Set E) ∧ FiniteDimensional 𝕜 (E ⧸ K) ∧
      ‖T.comp K.subtypeL‖ ≤ ε := by
  have hδ : (⟨ε / 2, (half_pos hε).le⟩ : NNReal) ≠ 0 :=
    NNReal.coe_ne_zero.mp (half_pos hε).ne'
  obtain ⟨C, -, hC, hcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded hδ (hT.totallyBounded_image_closedBall 1)
  obtain ⟨K, hK_closed, hK_rank, hTK⟩ :=
    T.exists_rank_quotient_le_nnnorm_comp_subtypeL_le_of_isCover hC hcover
  have hfin : FiniteDimensional 𝕜 (E ⧸ K) :=
    Module.rank_lt_aleph0_iff.mp (hK_rank.trans_lt Cardinal.natCast_lt_aleph0)
  refine ⟨K, hK_closed, hfin, ?_⟩
  have hle : ‖T.comp K.subtypeL‖ ≤ 2 * (ε / 2) := by exact_mod_cast hTK
  linarith

end IsCompactOperator
