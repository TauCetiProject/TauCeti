/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence

/-!
# Approximation numbers of operators extended to completions

Over a complete nontrivially normed scalar field `𝕜`, extending a bounded linear map
`T : E →L[𝕜] F` between seminormed spaces to the bounded map `T.completion` between their
uniform completions preserves its finite rank bounds, its approximation numbers `aₙ(T)` at every
index, and its Ky Fan prefix gauges `Kₖ(T)`. When the codomain `F` is already complete and
Hausdorff, the one-sided extension `T.fromCompletion : Completion E →L[𝕜] F` likewise has the
same approximation numbers and Ky Fan gauges as `T`.

* **Upper bound (`aₙ(T.completion) ≤ aₙ(T)`).** If `R : E →L[𝕜] F` has rank at most `n`, the
  image of `R` in `Completion F` has rank at most `n`, hence is finite-dimensional and therefore
  closed in `Completion F` because `𝕜` is complete (`Submodule.isClosed_of_finiteDimensional`).
  By density of `E` in `Completion E`, `R.completion` maps all of `Completion E` into that same
  subspace, so `rank R.completion ≤ n` and
  `‖T.completion - R.completion‖ = ‖(T - R).completion‖ = ‖T - R‖`.
* **Lower bound (`aₙ(T) ≤ aₙ(T.completion)`).** Conversely, for `R' : Completion E →L[𝕜]
  Completion F` of rank at most `n`, the restriction `S := R' ∘L Completion.toComplL` has
  finite-dimensional range `V ≤ Completion F` of dimension `k ≤ n`. Choosing a basis `b` of `V`
  makes each coordinate functional `x ↦ (b.repr (S x)) i` continuous (`𝕜` is complete), and
  approximating each `b i` in `Completion F` by a vector `y i : F` produces a bounded map
  `R = ∑ i, φᵢ.smulRight (y i) : E →L[𝕜] F` of rank at most `n` within `‖T.completion - R'‖ + ε`
  of `T`.
* **One-sided completion (`T.fromCompletion`).** When `F` is complete and Hausdorff, `T.completion`
  and `T.fromCompletion` factor through one another via contractions (`Completion.toComplL` and
  `(id 𝕜 F).fromCompletion`), so their approximation numbers agree even without completeness of
  `𝕜`; combining with `singularValue_completion` equates them with `aₙ(T)`.

Completeness of `𝕜` cannot be omitted: for `𝕜 = E = F = ℚ` and `T = id`, `a₁(T) = 0` because
`rank_ℚ ℚ = 1`, whereas `T.completion = id_ℝ : ℝ →L[ℚ] ℝ` admits no nonzero continuous `ℚ`-linear
approximant of finite `ℚ`-rank and thus has `a₁(T.completion) = 1`.

## Main declarations

* `ContinuousLinearMap.rank_completion_le`: over a complete field, `rank T ≤ n` implies
  `rank T.completion ≤ n`.
* `ContinuousLinearMap.singularValue_completion`: `aₙ(T.completion) = aₙ(T)`.
* `ContinuousLinearMap.sameSingularValues_completion`: `SameSingularValues T.completion T`.
* `ContinuousLinearMap.kyFanGauge_completion`: `Kₖ(T.completion) = Kₖ(T)`.
* `ContinuousLinearMap.singularValue_fromCompletion_eq_completion`: for complete Hausdorff `F`,
  `aₙ(T.fromCompletion) = aₙ(T.completion)` over any nontrivially normed field.
* `ContinuousLinearMap.rank_fromCompletion_le`,
  `ContinuousLinearMap.singularValue_fromCompletion`,
  `ContinuousLinearMap.sameSingularValues_fromCompletion`,
  `ContinuousLinearMap.kyFanGauge_fromCompletion`: the corresponding rank bound and identities for
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

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A sum of `k` rank-one operators `(φ i).smulRight (y i)` has rank at most `k`. -/
private theorem rank_sum_smulRight_le {k : ℕ} (φ : Fin k → E →L[𝕜] 𝕜) (y : Fin k → F) :
    (∑ i : Fin k, (φ i).smulRight (y i)).rank ≤ k := by
  let R : E →L[𝕜] F := ∑ i : Fin k, (φ i).smulRight (y i)
  have hsub : LinearMap.range (R : E →ₗ[𝕜] F) ≤ Submodule.span 𝕜 (Set.range y) := by
    rintro _ ⟨x, rfl⟩
    simpa [R] using Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hy_card : Cardinal.mk (Set.range y) ≤ k := by
    simpa using Cardinal.mk_range_le_lift (f := y)
  exact (Submodule.rank_mono hsub).trans <| (rank_span_le _).trans hy_card

variable [CompleteSpace 𝕜]

/-- Over a complete scalar field, extending a bounded linear map of rank at most `n` to the
completions of its domain and codomain preserves the bound `rank ≤ n`. -/
theorem rank_completion_le (T : E →L[𝕜] F) {n : ℕ} (hT : T.rank ≤ n) :
    T.completion.rank ≤ n := by
  set W : Submodule 𝕜 (Completion F) :=
    LinearMap.range ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T : E →ₗ[𝕜] Completion F)
  have hW : Module.rank 𝕜 W ≤ n := by
    have hle := (LinearMap.lift_rank_comp_le_right (T : E →ₗ[𝕜] F)
      ((Completion.toComplL : F →L[𝕜] Completion F) : F →ₗ[𝕜] Completion F)).trans
      (Cardinal.lift_le.mpr hT)
    rwa [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at hle
  have : FiniteDimensional 𝕜 W :=
    Module.rank_lt_aleph0_iff.mp (hW.trans_lt Cardinal.natCast_lt_aleph0)
  have hrange : LinearMap.range (T.completion : Completion E →ₗ[𝕜] Completion F) ≤ W := by
    rintro _ ⟨x, rfl⟩
    refine Completion.induction_on x
      (W.isClosed_of_finiteDimensional.preimage T.completion.continuous) fun a ↦ ?_
    simp [W]
  exact (Submodule.rank_mono hrange).trans hW

/-- Approximating basis vectors of the finite-dimensional range of `R' ∘L toComplL` inside `F`
bounds `aₙ(T)` by `‖T.completion - R'‖ + ε` for every `ε > 0`. -/
private theorem singularValue_le_norm_completion_sub_add (T : E →L[𝕜] F) {n : ℕ}
    {R' : Completion E →L[𝕜] Completion F} (hR' : R'.rank ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (T.singularValue n : ℝ) ≤ ‖T.completion - R'‖ + ε := by
  set S : E →L[𝕜] Completion F := R' ∘L Completion.toComplL
  set V : Submodule 𝕜 (Completion F) := LinearMap.range (S : E →ₗ[𝕜] Completion F)
  have hV : Module.rank 𝕜 V ≤ n := (LinearMap.rank_comp_le_left _ _).trans hR'
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  let k := Module.finrank 𝕜 V
  let b : Module.Basis (Fin k) 𝕜 V := Module.finBasis 𝕜 V
  let S₀ : E →L[𝕜] V := S.codRestrict V (LinearMap.mem_range_self _)
  let φ : Fin k → E →L[𝕜] 𝕜 := fun i ↦ LinearMap.toContinuousLinearMap (b.coord i) ∘L S₀
  set M : ℝ := 1 + ∑ i : Fin k, ‖φ i‖ with hM_def
  have hM : 0 < M := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  choose y hy using fun i : Fin k ↦
    Metric.denseRange_iff.mp Completion.denseRange_coe (b i : Completion F) (ε / M) (div_pos hε hM)
  let R : E →L[𝕜] F := ∑ i : Fin k, (φ i).smulRight (y i)
  have hR_rank : R.rank ≤ n :=
    (rank_sum_smulRight_le φ y).trans (by rwa [Module.finrank_eq_rank])
  refine (NNReal.coe_le_coe.mpr (T.singularValue_le_nnnorm_sub hR_rank)).trans ?_
  rw [coe_nnNorm]
  refine opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have hSx : R' x = ∑ i : Fin k, φ i x • (b i : Completion F) := by
    simpa only [S, S₀, φ, coe_codRestrict_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      b.coord_apply, comp_apply, LinearMap.coe_toContinuousLinearMap', Completion.coe_toComplL]
      using congrArg Subtype.val (b.sum_repr (S₀ x)).symm
  have hRx : ((R x : F) : Completion F) = ∑ i : Fin k, φ i x • (y i : Completion F) := by
    simpa only [R, sum_apply, smulRight_apply, map_smul, Completion.coe_toComplL] using
      map_sum (Completion.toComplL : F →L[𝕜] Completion F) (fun i ↦ φ i x • y i) Finset.univ
  have hdiff : ((T - R) x : Completion F) =
      (T.completion - R') x + ∑ i : Fin k, φ i x • ((b i : Completion F) - y i) := by
    simp only [sub_apply, Completion.coe_sub, completion_apply_coe, hRx, hSx, smul_sub,
      Finset.sum_sub_distrib]; abel
  rw [← Completion.norm_coe, hdiff]
  calc ‖(T.completion - R') x + ∑ i : Fin k, φ i x • ((b i : Completion F) - y i)‖
      ≤ ‖(T.completion - R') x‖ + ∑ i : Fin k, ‖φ i x • ((b i : Completion F) - y i)‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
    _ ≤ ‖T.completion - R'‖ * ‖x‖ + (∑ i : Fin k, ‖φ i‖ * (ε / M)) * ‖x‖ := by
        rw [Finset.sum_mul]
        gcongr with i
        · simpa using (T.completion - R').le_opNorm x
        · rw [norm_smul, mul_right_comm]
          exact mul_le_mul ((φ i).le_opNorm x) (by simpa [dist_eq_norm] using (hy i).le)
            (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (‖T.completion - R'‖ + ε) * ‖x‖ := by
        rw [add_mul, ← Finset.sum_mul]
        gcongr
        calc (∑ i : Fin k, ‖φ i‖) * (ε / M) ≤ M * (ε / M) := by
              gcongr; rw [hM_def]; linarith
          _ = ε := mul_div_cancel₀ ε hM.ne'

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
    refine (T.completion.singularValue_le_nnnorm_sub (R.rank_completion_le hR)).trans ?_
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
  have h₁ : ι ∘L T.fromCompletion = T.completion := by
    ext x
    refine Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun a ↦ by simp [ι]
  have h₂ : π ∘L T.completion = T.fromCompletion := by
    ext x
    refine Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun a ↦ by simp [π]
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

/-- Over a complete scalar field, extending a bounded linear map of rank at most `n` into a
complete Hausdorff space to `Completion E` preserves the bound `rank ≤ n`. -/
theorem rank_fromCompletion_le [CompleteSpace 𝕜] (T : E →L[𝕜] F) {n : ℕ} (hT : T.rank ≤ n) :
    T.fromCompletion.rank ≤ n := by
  have h : (ContinuousLinearMap.id 𝕜 F).fromCompletion ∘L T.completion = T.fromCompletion := by
    ext x
    refine Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun a ↦ by simp
  rw [← h]
  exact (LinearMap.rank_comp_le_right _ _).trans (T.rank_completion_le hT)

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
