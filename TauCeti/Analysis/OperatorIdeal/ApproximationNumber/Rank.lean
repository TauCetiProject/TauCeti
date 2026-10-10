/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The exact finite-dimensional rank cutoff

The zero-based approximation number vanishes exactly at and above the rank.
This is a normed-space statement: no inner product, singular-value decomposition,
or choice of orthonormal basis is required. The converse uses openness of a
finite rank lower bound in the operator-norm topology.

This implements OI-A24 using the canonical real-valued `approximationNumber` API.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Vanishing of an approximation number characterizes the rank. Only the source
needs to be finite-dimensional. -/
theorem approximationNumber_eq_zero_iff_rank_le (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n = 0 ↔ T.rank ≤ (n : Cardinal) := by
  constructor
  · intro hz
    by_contra hn
    have hrank (S : E →L[𝕜] F) :
        S.rank = (Module.finrank 𝕜 S.range : Cardinal) :=
      (Module.finrank_eq_rank' 𝕜 S.range).symm
    have hdim : n < Module.finrank 𝕜 T.range := by
      rw [hrank] at hn
      exact not_le.mp (by exact_mod_cast hn)
    have hT : ((n + 1 : ℕ) : Cardinal) ≤ T.rank := by
      rw [hrank]
      exact_mod_cast (Nat.succ_le_of_lt hdim)
    obtain ⟨ε, heps, hball⟩ :=
      Metric.isOpen_iff.mp (isOpen_setOfPred_nat_le_rank (𝕜 := 𝕜) (n + 1)) T hT
    have hlower : ε ≤ T.approximationNumber n :=
      T.le_approximationNumber_iff.mpr fun S hS => by
        by_contra hdist
        have hmem : S ∈ Metric.ball T ε := by
          simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using not_le.mp hdist
        have hmemrank : ((n + 1 : ℕ) : Cardinal) ≤ (S : E →ₗ[𝕜] F).rank :=
          Set.mem_ofPred.mp (hball hmem)
        have hbad := hmemrank.trans hS
        have hbad' : n + 1 ≤ n := by exact_mod_cast hbad
        omega
    rw [hz] at hlower
    exact (not_le_of_gt heps) hlower
  · exact T.approximationNumber_eq_zero_of_rank_le

/-- The finite-rank version with a natural-number dimension. -/
theorem approximationNumber_eq_zero_iff_finrank_range_le (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n = 0 ↔ Module.finrank 𝕜 T.range ≤ n := by
  rw [approximationNumber_eq_zero_iff_rank_le]
  change Module.rank 𝕜 T.range ≤ (n : Cardinal) ↔ _
  rw [← Module.finrank_eq_rank' 𝕜 T.range]
  exact_mod_cast Iff.rfl

end ContinuousLinearMap
