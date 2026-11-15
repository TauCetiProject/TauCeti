/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence
import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# Approximation numbers of operators extended to completions

Over a complete nontrivially normed scalar field `𝕜`, extending a bounded linear map
`T : E →L[𝕜] F` between seminormed spaces to the bounded map `T.completion` between their
uniform completions preserves its approximation numbers `aₙ(T)` at every index and its Ky Fan
prefix gauges `Kₖ(T)`. When the codomain `F` is already complete and Hausdorff, the one-sided
extension `T.fromCompletion : Completion E →L[𝕜] F` likewise has the same approximation numbers
and Ky Fan gauges as `T`.

* **Upper bound (`aₙ(T.completion) ≤ aₙ(T)`).** If `R : E →L[𝕜] F` has rank at most `n`, then over
  a complete scalar field `R.completion` also has rank at most `n`
  (`ContinuousLinearMap.rank_completion_le_of_rank_le`), while
  `‖T.completion - R.completion‖ = ‖(T - R).completion‖ = ‖T - R‖`.
* **Lower bound (`aₙ(T) ≤ aₙ(T.completion)`).** Conversely, for `R' : Completion E →L[𝕜]
  Completion F` of rank at most `n`, the restriction `S := R' ∘L Completion.toComplL` has
  finite-dimensional range `V ≤ Completion F` of dimension at most `n`. Approximating `V.subtypeL`
  in operator norm by `Completion.toComplL ∘L U` with `U : V →L[𝕜] F`
  (`ContinuousLinearMap.denseRange_comp`) and setting `R := U ∘L S₀` produces a bounded map of
  rank at most `n` within `‖T.completion - R'‖ + ε` of `T`.
* **One-sided completion (`T.fromCompletion`).** When `F` is complete and Hausdorff, `T.completion`
  and `T.fromCompletion` factor through one another via contractions (`Completion.toComplL` and
  `(id 𝕜 F).fromCompletion`), so their approximation numbers agree even without completeness of
  `𝕜`; combining with `singularValue_completion` equates them with `aₙ(T)`.

Completeness of `𝕜` cannot be omitted: for `𝕜 = E = F = ℚ` and `T = id`, `a₁(T) = 0` because
`rank_ℚ ℚ = 1`, whereas `T.completion = id_ℝ : ℝ →L[ℚ] ℝ` admits no nonzero continuous `ℚ`-linear
approximant of finite `ℚ`-rank and thus has `a₁(T.completion) = 1`.

## Main declarations

* `ContinuousLinearMap.singularValue_completion`: `aₙ(T.completion) = aₙ(T)`.
* `ContinuousLinearMap.sameSingularValues_completion`: `SameSingularValues T.completion T`.
* `ContinuousLinearMap.kyFanGauge_completion`: `Kₖ(T.completion) = Kₖ(T)`.
* `ContinuousLinearMap.singularValue_fromCompletion_eq_completion`: for complete Hausdorff `F`,
  `aₙ(T.fromCompletion) = aₙ(T.completion)` over any nontrivially normed field.
* `ContinuousLinearMap.singularValue_fromCompletion`,
  `ContinuousLinearMap.sameSingularValues_fromCompletion`,
  `ContinuousLinearMap.kyFanGauge_fromCompletion`: the corresponding identities for
  `T.fromCompletion` over a complete field.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.2.
-/

public section

open UniformSpace
open scoped NNReal

namespace ContinuousLinearMap

section CompleteField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Approximating the inclusion of the finite-dimensional range of `R' ∘L toComplL` by an operator
into `F` bounds `aₙ(T)` by `‖T.completion - R'‖ + ε` for every `ε > 0`. -/
private theorem singularValue_le_norm_completion_sub_add (T : E →L[𝕜] F) {n : ℕ}
    {R' : Completion E →L[𝕜] Completion F} (hR' : R'.rank ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (T.singularValue n : ℝ) ≤ ‖T.completion - R'‖ + ε := by
  set S : E →L[𝕜] Completion F := R' ∘L Completion.toComplL
  set V : Submodule 𝕜 (Completion F) := LinearMap.range (S : E →ₗ[𝕜] Completion F)
  have hV : Module.rank 𝕜 V ≤ n := (LinearMap.rank_comp_le_left _ _).trans hR'
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  let S₀ : E →L[𝕜] V := S.codRestrict V (LinearMap.mem_range_self _)
  let ιF : F →L[𝕜] Completion F := Completion.toComplL
  let ιE : E →L[𝕜] Completion E := Completion.toComplL
  have hM : 0 < ‖S₀‖ + 1 := by positivity
  obtain ⟨U, hU⟩ := Metric.denseRange_iff.mp
    (ContinuousLinearMap.denseRange_comp (V := V) (g := ιF) Completion.denseRange_coe)
    V.subtypeL (ε / (‖S₀‖ + 1)) (div_pos hε hM)
  let R : E →L[𝕜] F := U ∘L S₀
  have hR_rank : R.rank ≤ n :=
    ((LinearMap.rank_comp_le_left _ _).trans (LinearMap.rank_le_domain _)).trans hV
  refine (NNReal.coe_le_coe.mpr (T.singularValue_le_nnnorm_sub hR_rank)).trans ?_
  rw [coe_nnNorm, ← norm_toComplL_comp (f := T - R)]
  have hdecomp : ιF ∘L (T - R) = (T.completion - R') ∘L ιE + (V.subtypeL - ιF ∘L U) ∘L S₀ := by
    ext x
    simp [ιF, ιE, R, S₀, S, sub_add_sub_cancel]
  rw [hdecomp]
  calc ‖(T.completion - R') ∘L ιE + (V.subtypeL - ιF ∘L U) ∘L S₀‖
      ≤ ‖(T.completion - R') ∘L ιE‖ + ‖(V.subtypeL - ιF ∘L U) ∘L S₀‖ := norm_add_le _ _
    _ ≤ ‖T.completion - R'‖ * ‖ιE‖ + ‖V.subtypeL - ιF ∘L U‖ * ‖S₀‖ :=
        add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ ≤ ‖T.completion - R'‖ * 1 + (ε / (‖S₀‖ + 1)) * (‖S₀‖ + 1) := by
        gcongr
        · exact (Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap_le
        · exact (dist_eq_norm V.subtypeL (ιF ∘L U)).symm.trans_le hU.le
        · linarith
    _ = ‖T.completion - R'‖ + ε := by rw [mul_one, div_mul_cancel₀ ε hM.ne']

/-- Over a complete scalar field, extending a bounded linear map to the completions of its domain
and codomain preserves all approximation numbers. -/
@[simp]
theorem singularValue_completion (T : E →L[𝕜] F) (n : ℕ) :
    T.completion.singularValue n = T.singularValue n := by
  refine le_antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
    (le_singularValue_iff.mpr fun R' hR' ↦ ?_)
  · have hsub : (T - R).completion = T.completion - R.completion := by
      ext x
      refine Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun a ↦ ?_
      simp [← Completion.coe_sub]
    refine (T.completion.singularValue_le_nnnorm_sub (R.rank_completion_le_of_rank_le hR)).trans ?_
    rw [← hsub, ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, norm_completion]
  · rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact le_of_forall_pos_le_add fun ε hε ↦
      T.singularValue_le_norm_completion_sub_add hR' hε

/-- Over a complete scalar field, a bounded linear map and its extension to the completions have
the same approximation-number sequence. -/
@[simp]
theorem sameSingularValues_completion (T : E →L[𝕜] F) :
    SameSingularValues T.completion T :=
  (sameSingularValues_iff _ _).mpr T.singularValue_completion

/-- Over a complete scalar field, extending a bounded linear map to the completions preserves all
Ky Fan prefix gauges. -/
@[simp]
theorem kyFanGauge_completion (T : E →L[𝕜] F) (k : ℕ) :
    T.completion.kyFanGauge k = T.kyFanGauge k :=
  T.sameSingularValues_completion.kyFanGauge_eq k

end CompleteField

section FromCompletion

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [T0Space F] [CompleteSpace F]

/-- When the codomain is complete and Hausdorff, the one-sided extension `T.fromCompletion` and
the two-sided extension `T.completion` have the same approximation numbers over any nontrivially
normed field. -/
theorem singularValue_fromCompletion_eq_completion (T : E →L[𝕜] F) (n : ℕ) :
    T.fromCompletion.singularValue n = T.completion.singularValue n := by
  let ι : F →L[𝕜] Completion F := Completion.toComplL
  let π : Completion F →L[𝕜] F := (ContinuousLinearMap.id 𝕜 F).fromCompletion
  have h₁ : ι ∘L T.fromCompletion = T.completion :=
    ((ι ∘L T).fromCompletion_unique _ fun _ ↦ by simp [ι]).symm.trans
      ((ι ∘L T).fromCompletion_unique _ fun _ ↦ by simp [ι])
  have h₂ : π ∘L T.completion = T.fromCompletion :=
    (T.fromCompletion_unique _ fun _ ↦ by simp [π]).symm
  have hι : ‖ι‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact_mod_cast (Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F).norm_toContinuousLinearMap_le
  have hπ : ‖π‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, norm_fromCompletion]
    exact norm_id_le
  refine le_antisymm ?_ ?_
  · calc T.fromCompletion.singularValue n = (π ∘L T.completion).singularValue n := by rw [h₂]
      _ ≤ ‖π‖₊ * T.completion.singularValue n := π.singularValue_comp_le_left _ n
      _ ≤ 1 * T.completion.singularValue n := by gcongr
      _ = T.completion.singularValue n := one_mul _
  · calc T.completion.singularValue n = (ι ∘L T.fromCompletion).singularValue n := by rw [h₁]
      _ ≤ ‖ι‖₊ * T.fromCompletion.singularValue n := ι.singularValue_comp_le_left _ n
      _ ≤ 1 * T.fromCompletion.singularValue n := by gcongr
      _ = T.fromCompletion.singularValue n := one_mul _

/-- Over a complete scalar field, extending a bounded linear map into a complete Hausdorff space
to the completion of its domain preserves all approximation numbers. -/
@[simp]
theorem singularValue_fromCompletion [CompleteSpace 𝕜] (T : E →L[𝕜] F) (n : ℕ) :
    T.fromCompletion.singularValue n = T.singularValue n :=
  (T.singularValue_fromCompletion_eq_completion n).trans (T.singularValue_completion n)

/-- Over a complete scalar field, a bounded linear map into a complete Hausdorff space and its
extension to the completion of the domain have the same approximation-number sequence. -/
@[simp]
theorem sameSingularValues_fromCompletion [CompleteSpace 𝕜] (T : E →L[𝕜] F) :
    SameSingularValues T.fromCompletion T :=
  (sameSingularValues_iff _ _).mpr T.singularValue_fromCompletion

/-- Over a complete scalar field, extending a bounded linear map into a complete Hausdorff space
to the completion of its domain preserves all Ky Fan prefix gauges. -/
@[simp]
theorem kyFanGauge_fromCompletion [CompleteSpace 𝕜] (T : E →L[𝕜] F) (k : ℕ) :
    T.fromCompletion.kyFanGauge k = T.kyFanGauge k :=
  T.sameSingularValues_fromCompletion.kyFanGauge_eq k

end FromCompletion

end ContinuousLinearMap
