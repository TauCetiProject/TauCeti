/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence

/-!
# Approximation numbers of completed operators

Over a complete nontrivially normed scalar field `𝕜`, extending a bounded linear map
`T : E →L[𝕜] F` between seminormed spaces to the uniform completions preserves every approximation
number `aₙ(T)`:

* `aₙ(T.completion) = aₙ(T)` (`ContinuousLinearMap.singularValue_completion`);
* `aₙ(T.fromCompletion) = aₙ(T)` when `F` is Hausdorff and complete
  (`ContinuousLinearMap.singularValue_fromCompletion`);
* `aₙ(toComplL ∘L T) = aₙ(T)` (`ContinuousLinearMap.singularValue_toComplL_comp`).

The upper bound `aₙ(T.completion) ≤ aₙ(T)` extends any bounded approximant `R : E →L[𝕜] F` of
rank at most `n` to `R.completion`, which has rank at most `n`
(`ContinuousLinearMap.rank_completion_le_of_le`) and preserves the error norm
(`ContinuousLinearMap.completion_sub`, `ContinuousLinearMap.norm_completion`). Conversely, every
bounded approximant `R' : Completion E →L[𝕜] Completion F` of rank at most `n` is approximated
arbitrarily closely in operator norm by `R.completion` for some `R : E →L[𝕜] F` of rank at most `n`
(`ContinuousLinearMap.exists_rank_le_norm_completion_sub_lt`), giving `aₙ(T) ≤ aₙ(T.completion)`.

Completeness of the scalar field is essential: for the canonical `ℚ`-linear inclusion
`T : ℚ →L[ℚ] ℝ`, `rank T = 1` gives `a₁(T) = 0`, whereas `T.fromCompletion` identifies with the
identity on `ℝ`, whose `ℚ`-rank is uncountable and so has `a₁ = 1`.

## Main declarations

* `ContinuousLinearMap.singularValue_completion`: over a complete scalar field,
  `T.completion.singularValue n = T.singularValue n`.
* `ContinuousLinearMap.singularValue_fromCompletion`: over a complete scalar field,
  `T.fromCompletion.singularValue n = T.singularValue n` when `F` is `T0Space` and `CompleteSpace`.
* `ContinuousLinearMap.singularValue_toComplL_comp`: over a complete scalar field,
  `((Completion.toComplL : F →L[𝕜] Completion F) ∘L T).singularValue n = T.singularValue n`.
* `ContinuousLinearMap.sameSingularValues_completion`,
  `ContinuousLinearMap.sameSingularValues_fromCompletion`,
  `ContinuousLinearMap.sameSingularValues_toComplL_comp`: equivalence of approximation-number
  sequences under completion over a complete scalar field.
* `ContinuousLinearMap.kyFanGauge_completion`,
  `ContinuousLinearMap.kyFanGauge_fromCompletion`,
  `ContinuousLinearMap.kyFanGauge_toComplL_comp`: invariance of Ky Fan prefix gauges under
  completion over a complete scalar field.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.2.
-/

public section

open UniformSpace
open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a complete scalar field, extending a bounded linear map to the completions of its domain
and codomain preserves all approximation numbers. -/
@[simp]
theorem singularValue_completion (T : E →L[𝕜] F) (n : ℕ) :
    T.completion.singularValue n = T.singularValue n := by
  refine le_antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
    (le_singularValue_iff.mpr fun R' hR' ↦ ?_)
  · refine (T.completion.singularValue_le_nnnorm_sub (rank_completion_le_of_le hR)).trans ?_
    rw [← completion_sub, ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, (T - R).norm_completion]
  · refine NNReal.coe_le_coe.mp (le_of_forall_pos_le_add fun ε hε ↦ ?_)
    obtain ⟨R, hR, hnorm⟩ := exists_rank_le_norm_completion_sub_lt hR' hε
    calc (T.singularValue n : ℝ)
        ≤ ‖T - R‖ := NNReal.coe_le_coe.mpr (T.singularValue_le_nnnorm_sub hR)
      _ = ‖T.completion - R.completion‖ := by rw [← (T - R).norm_completion, completion_sub]
      _ ≤ ‖T.completion - R'‖ + ‖R' - R.completion‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖T.completion - R'‖ + ε := by rw [norm_sub_rev R']; gcongr

/-- Over a complete scalar field, extending a bounded linear map into a complete Hausdorff space
to the completion of its domain preserves all approximation numbers. -/
@[simp]
theorem singularValue_fromCompletion [T0Space F] [CompleteSpace F] (T : E →L[𝕜] F) (n : ℕ) :
    T.fromCompletion.singularValue n = T.singularValue n := by
  rw [← T.singularValue_completion]
  refine le_antisymm ?_ ?_
  · have hfac : T.fromCompletion =
        (ContinuousLinearMap.id 𝕜 F).fromCompletion ∘L T.completion :=
      fromCompletion_unique _ _ fun x ↦ by simp
    have hnorm : ‖(ContinuousLinearMap.id 𝕜 F).fromCompletion‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe, coe_nnNorm, norm_fromCompletion]
      exact_mod_cast norm_id_le
    rw [hfac]
    exact (((ContinuousLinearMap.id 𝕜 F).fromCompletion).singularValue_comp_le_left
      T.completion n).trans (mul_le_of_le_one_left' hnorm)
  · have hfac : T.completion =
        (Completion.toComplL : F →L[𝕜] Completion F) ∘L T.fromCompletion :=
      (fromCompletion_unique ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T) T.completion
        fun x ↦ by simp).symm.trans (fromCompletion_unique _ _ fun x ↦ by simp)
    have hnorm : ‖(Completion.toComplL : F →L[𝕜] Completion F)‖₊ ≤ 1 := by
      exact_mod_cast (Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F).norm_toContinuousLinearMap_le
    rw [hfac]
    exact ((Completion.toComplL : F →L[𝕜] Completion F).singularValue_comp_le_left
      T.fromCompletion n).trans (mul_le_of_le_one_left' hnorm)

/-- Over a complete scalar field, composing a bounded linear map with the canonical embedding of
its codomain into the completion preserves all approximation numbers. -/
@[simp]
theorem singularValue_toComplL_comp (T : E →L[𝕜] F) (n : ℕ) :
    ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T).singularValue n = T.singularValue n := by
  have hfac : ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T).fromCompletion =
      T.completion :=
    fromCompletion_unique _ _ fun x ↦ by simp
  rw [← singularValue_fromCompletion, hfac, singularValue_completion]

/-- Over a complete scalar field, a bounded linear map and its extension to the completions have
the same approximation-number sequence. -/
@[simp]
theorem sameSingularValues_completion (T : E →L[𝕜] F) :
    SameSingularValues T.completion T :=
  (sameSingularValues_iff _ _).mpr T.singularValue_completion

/-- Over a complete scalar field, a bounded linear map into a complete Hausdorff space and its
extension to the completion of the domain have the same approximation-number sequence. -/
@[simp]
theorem sameSingularValues_fromCompletion [T0Space F] [CompleteSpace F] (T : E →L[𝕜] F) :
    SameSingularValues T.fromCompletion T :=
  (sameSingularValues_iff _ _).mpr T.singularValue_fromCompletion

/-- Over a complete scalar field, composing a bounded linear map with the canonical embedding into
the completion of its codomain preserves the equivalence class of its approximation-number
sequence. -/
@[simp]
theorem sameSingularValues_toComplL_comp (T : E →L[𝕜] F) :
    SameSingularValues ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T) T :=
  (sameSingularValues_iff _ _).mpr T.singularValue_toComplL_comp

/-- Over a complete scalar field, extending a bounded linear map to the completions preserves all
Ky Fan prefix gauges. -/
@[simp]
theorem kyFanGauge_completion (T : E →L[𝕜] F) (k : ℕ) :
    T.completion.kyFanGauge k = T.kyFanGauge k :=
  T.sameSingularValues_completion.kyFanGauge_eq k

/-- Over a complete scalar field, extending a bounded linear map into a complete Hausdorff space
to the completion of its domain preserves all Ky Fan prefix gauges. -/
@[simp]
theorem kyFanGauge_fromCompletion [T0Space F] [CompleteSpace F] (T : E →L[𝕜] F) (k : ℕ) :
    T.fromCompletion.kyFanGauge k = T.kyFanGauge k :=
  T.sameSingularValues_fromCompletion.kyFanGauge_eq k

/-- Over a complete scalar field, composing a bounded linear map with the canonical embedding into
the completion of its codomain preserves all Ky Fan prefix gauges. -/
@[simp]
theorem kyFanGauge_toComplL_comp (T : E →L[𝕜] F) (k : ℕ) :
    ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T).kyFanGauge k = T.kyFanGauge k :=
  T.sameSingularValues_toComplL_comp.kyFanGauge_eq k

end ContinuousLinearMap
