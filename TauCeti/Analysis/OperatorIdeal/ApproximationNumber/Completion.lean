/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Free
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
rank at most `n` to `R.completion`: the image of `LinearMap.range R` in `Completion F` has rank at
most `n`, hence is finite-dimensional and closed (`Submodule.isClosed_of_finiteDimensional`) since
`𝕜` is complete, so `R.completion` maps `Completion E` into it by density of `E` and preserves the
error norm (`ContinuousLinearMap.norm_completion`).

Conversely, if `R' : Completion E →L[𝕜] Completion F` has rank at most `n`, expanding `R'` in a
finite basis `(bᵢ)` of `LinearMap.range R'` produces continuous coordinate functionals on `E`
(`LinearMap.toContinuousLinearMap`, again using completeness of `𝕜`). Approximating each basis
vector `bᵢ` arbitrarily closely in `Completion F` by an element of `F` yields a bounded map
`R : E →L[𝕜] F` of rank at most `n` whose distance from `T` is arbitrarily close to
`‖T.completion - R'‖`.

Completeness of the scalar field is essential: for the canonical `ℚ`-linear inclusion
`T : ℚ →L[ℚ] ℝ`, `rank T = 1` gives `a₁(T) = 0`, whereas `T.fromCompletion` identifies with the
identity on `ℝ`, whose `ℚ`-rank is uncountable and so has `a₁ = 1`.

## Main declarations

* `ContinuousLinearMap.singularValue_completion`:
  `T.completion.singularValue n = T.singularValue n`.
* `ContinuousLinearMap.singularValue_fromCompletion`:
  `T.fromCompletion.singularValue n = T.singularValue n` when `F` is `T0Space` and `CompleteSpace`.
* `ContinuousLinearMap.singularValue_toComplL_comp`:
  `((Completion.toComplL : F →L[𝕜] Completion F) ∘L T).singularValue n = T.singularValue n`.
* `ContinuousLinearMap.sameSingularValues_completion`,
  `ContinuousLinearMap.sameSingularValues_fromCompletion`,
  `ContinuousLinearMap.sameSingularValues_toComplL_comp`: equivalence of approximation-number
  sequences under completion.
* `ContinuousLinearMap.kyFanGauge_completion`,
  `ContinuousLinearMap.kyFanGauge_fromCompletion`,
  `ContinuousLinearMap.kyFanGauge_toComplL_comp`: invariance of Ky Fan prefix gauges under
  completion.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.2.
-/

public section

open UniformSpace
open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] in
/-- Perturbing vectors `u : Fin m → Completion F` within `δ` to `y : Fin m → F` moves
`∑ i, ψ i x • u i` by at most `((∑ i, ‖ψ i‖) * δ) * ‖x‖`. -/
private theorem norm_sum_smul_sub_coe_le {m : ℕ} (ψ : Fin m → (E →L[𝕜] 𝕜))
    (u : Fin m → Completion F) (y : Fin m → F) {δ : ℝ}
    (hy : ∀ i, dist (u i) (y i : Completion F) < δ) (x : E) :
    ‖∑ i, ψ i x • u i - ((∑ i, (ψ i).smulRight (y i)) x : F)‖ ≤ ((∑ i, ‖ψ i‖) * δ) * ‖x‖ := by
  have heq : ∑ i, ψ i x • u i - (((∑ i, (ψ i).smulRight (y i)) x : F) : Completion F) =
      ∑ i, ψ i x • (u i - (y i : Completion F)) := by
    have hsum : ((∑ i, (ψ i).smulRight (y i)) x : F) = ∑ i, ψ i x • y i := by simp
    have hcoe : ((∑ i, ψ i x • y i : F) : Completion F) = ∑ i, ψ i x • (y i : Completion F) :=
      (map_sum (Completion.toCompl : F →+ Completion F) (fun i ↦ ψ i x • y i) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ ↦ Completion.coe_smul (ψ i x) (y i))
    rw [hsum, hcoe, ← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
  rw [heq]
  calc ‖∑ i, ψ i x • (u i - (y i : Completion F))‖
      ≤ ∑ i, ‖ψ i x • (u i - (y i : Completion F))‖ := norm_sum_le _ _
    _ ≤ ∑ i, (‖ψ i‖ * ‖x‖) * δ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_smul]
        exact mul_le_mul ((ψ i).le_opNorm x)
          (dist_eq_norm (u i) (y i : Completion F) ▸ (hy i).le) (norm_nonneg _) (by positivity)
    _ = ((∑ i, ‖ψ i‖) * δ) * ‖x‖ := by rw [← Finset.sum_mul, ← Finset.sum_mul, mul_right_comm]

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Extending a bounded map of rank at most `n` to the completions preserves the rank bound `n`:
the image of its range in `Completion F` is finite-dimensional, hence closed. -/
private theorem rank_completion_le_of_le {R : E →L[𝕜] F} {n : ℕ} (hR : R.rank ≤ n) :
    R.completion.rank ≤ n := by
  let V : Submodule 𝕜 (Completion F) :=
    (LinearMap.range (R : E →ₗ[𝕜] F)).map (Completion.toComplL : F →L[𝕜] Completion F).toLinearMap
  have : FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F)) :=
    Module.rank_lt_aleph0_iff.mp (hR.trans_lt Cardinal.natCast_lt_aleph0)
  have hrange : LinearMap.range (R.completion : Completion E →ₗ[𝕜] Completion F) ≤ V := by
    rintro _ ⟨x, rfl⟩
    induction x using Completion.induction_on with
    | hp => exact V.isClosed_of_finiteDimensional.preimage R.completion.continuous
    | ih x =>
      rw [coe_coe, completion_apply_coe]
      exact Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x)
  exact (Submodule.rank_mono hrange).trans ((rank_map_le _ _).trans hR)

/-- Every bounded approximant `R'` of rank at most `n` between completions can be matched on `E`
within any `ε > 0` by a bounded map `R : E →L[𝕜] F` of rank at most `n`. -/
private theorem exists_rank_le_norm_sub_le_of_completion (T : E →L[𝕜] F)
    {R' : Completion E →L[𝕜] Completion F} {n : ℕ} (hR' : R'.rank ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E →L[𝕜] F, R.rank ≤ n ∧ ‖T - R‖ ≤ ‖T.completion - R'‖ + ε := by
  set W : Submodule 𝕜 (Completion F) := LinearMap.range (R' : Completion E →ₗ[𝕜] Completion F)
  have : FiniteDimensional 𝕜 W :=
    Module.rank_lt_aleph0_iff.mp (hR'.trans_lt Cardinal.natCast_lt_aleph0)
  have hm : Module.finrank 𝕜 W ≤ n :=
    Nat.cast_le.mp ((Module.finrank_eq_rank 𝕜 W).trans_le hR')
  let b : Module.Basis (Fin (Module.finrank 𝕜 W)) 𝕜 W := Module.finBasis 𝕜 W
  let R'₀ : Completion E →L[𝕜] W := R'.codRestrict W (LinearMap.mem_range_self _)
  let ψ : Fin (Module.finrank 𝕜 W) → (E →L[𝕜] 𝕜) := fun i ↦
    (b.coord i).toContinuousLinearMap ∘L R'₀ ∘L (Completion.toComplL : E →L[𝕜] Completion E)
  set C : ℝ := (∑ i, ‖ψ i‖) + 1
  have hC : 0 < C :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) zero_lt_one
  choose y hy using fun i ↦
    Metric.denseRange_iff.mp Completion.denseRange_coe (b i : Completion F) (ε / C) (div_pos hε hC)
  let R : E →L[𝕜] F := ∑ i, (ψ i).smulRight (y i)
  have hR_rank : R.rank ≤ n := by
    have hle : LinearMap.range (R : E →ₗ[𝕜] F) ≤ Submodule.span 𝕜 (Set.range y) := by
      rintro _ ⟨x, rfl⟩
      have hRx : (R : E →ₗ[𝕜] F) x = ∑ i, ψ i x • y i := by simp [R]
      rw [hRx]
      exact sum_mem fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    refine (Submodule.rank_mono hle).trans
      ((rank_span_le _).trans (Cardinal.lift_le_nat_iff.mp (Cardinal.mk_range_le_lift.trans ?_)))
    rw [Cardinal.mk_fin, Cardinal.lift_natCast]
    exact Nat.cast_le.mpr hm
  refine ⟨R, hR_rank, opNorm_le_bound _ (by positivity) fun x ↦ ?_⟩
  have hR'_eq : R' x = ∑ i, ψ i x • (b i : Completion F) := by
    have h := (congrArg W.subtype (b.sum_repr (R'₀ x))).symm.trans
      (map_sum W.subtype (fun i ↦ b.repr (R'₀ x) i • b i) Finset.univ)
    exact h.trans (Finset.sum_congr rfl fun i _ ↦ by
      simp [ψ, R'₀, LinearMap.coe_toContinuousLinearMap'])
  have hsplit : ((T - R) x : Completion F) =
      (T.completion - R') x + (∑ i, ψ i x • (b i : Completion F) - (R x : Completion F)) := by
    rw [sub_apply, Completion.coe_sub, sub_apply, completion_apply_coe, hR'_eq]
    abel
  have htail : ‖∑ i, ψ i x • (b i : Completion F) - (R x : Completion F)‖ ≤ ε * ‖x‖ := by
    refine (norm_sum_smul_sub_coe_le ψ (fun i ↦ (b i : Completion F)) y hy x).trans ?_
    have hCδ : (∑ i, ‖ψ i‖) * (ε / C) ≤ ε :=
      (mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hε.le hC.le)).trans_eq
        (mul_div_cancel₀ ε hC.ne')
    exact mul_le_mul_of_nonneg_right hCδ (norm_nonneg x)
  rw [← Completion.norm_coe, hsplit]
  refine (norm_add_le _ _).trans ((add_le_add ?_ htail).trans_eq (add_mul _ _ _).symm)
  simpa only [Completion.norm_coe] using (T.completion - R').le_opNorm x

/-- Extending a bounded linear map to the completions of its domain and codomain preserves all
approximation numbers. -/
@[simp]
theorem singularValue_completion (T : E →L[𝕜] F) (n : ℕ) :
    T.completion.singularValue n = T.singularValue n := by
  refine le_antisymm (le_singularValue_iff.mpr fun R hR ↦ ?_)
    (le_singularValue_iff.mpr fun R' hR' ↦ ?_)
  · have hsub : (T - R).completion = T.completion - R.completion := by
      ext x
      induction x using Completion.induction_on with
      | hp =>
        exact isClosed_eq (T - R).completion.continuous (T.completion - R.completion).continuous
      | ih x => simp [← Completion.coe_sub]
    refine (T.completion.singularValue_le_nnnorm_sub (rank_completion_le_of_le hR)).trans ?_
    rw [← hsub, ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, (T - R).norm_completion]
  · refine NNReal.coe_le_coe.mp (le_of_forall_pos_le_add fun ε hε ↦ ?_)
    obtain ⟨R, hR, hnorm⟩ := exists_rank_le_norm_sub_le_of_completion T hR' hε
    exact (NNReal.coe_le_coe.mpr (T.singularValue_le_nnnorm_sub hR)).trans
      (by simpa only [coe_nnNorm] using hnorm)

/-- Extending a bounded linear map into a complete Hausdorff space to the completion of its domain
preserves all approximation numbers. -/
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

/-- Composing a bounded linear map with the canonical embedding of its codomain into the completion
preserves all approximation numbers. -/
@[simp]
theorem singularValue_toComplL_comp (T : E →L[𝕜] F) (n : ℕ) :
    ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T).singularValue n = T.singularValue n := by
  have hfac : ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T).fromCompletion =
      T.completion :=
    fromCompletion_unique _ _ fun x ↦ by simp
  rw [← singularValue_fromCompletion, hfac, singularValue_completion]

/-- A bounded linear map and its extension to the completions have the same approximation-number
sequence. -/
@[simp]
theorem sameSingularValues_completion (T : E →L[𝕜] F) :
    SameSingularValues T.completion T :=
  (sameSingularValues_iff _ _).mpr T.singularValue_completion

/-- A bounded linear map into a complete Hausdorff space and its extension to the completion of the
domain have the same approximation-number sequence. -/
@[simp]
theorem sameSingularValues_fromCompletion [T0Space F] [CompleteSpace F] (T : E →L[𝕜] F) :
    SameSingularValues T.fromCompletion T :=
  (sameSingularValues_iff _ _).mpr T.singularValue_fromCompletion

/-- Composing a bounded linear map with the canonical embedding into the completion of its codomain
preserves the equivalence class of its approximation-number sequence. -/
@[simp]
theorem sameSingularValues_toComplL_comp (T : E →L[𝕜] F) :
    SameSingularValues ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T) T :=
  (sameSingularValues_iff _ _).mpr T.singularValue_toComplL_comp

/-- Extending a bounded linear map to the completions preserves all Ky Fan prefix gauges. -/
@[simp]
theorem kyFanGauge_completion (T : E →L[𝕜] F) (k : ℕ) :
    T.completion.kyFanGauge k = T.kyFanGauge k :=
  T.sameSingularValues_completion.kyFanGauge_eq k

/-- Extending a bounded linear map into a complete Hausdorff space to the completion of its domain
preserves all Ky Fan prefix gauges. -/
@[simp]
theorem kyFanGauge_fromCompletion [T0Space F] [CompleteSpace F] (T : E →L[𝕜] F) (k : ℕ) :
    T.fromCompletion.kyFanGauge k = T.kyFanGauge k :=
  T.sameSingularValues_fromCompletion.kyFanGauge_eq k

/-- Composing a bounded linear map with the canonical embedding into the completion of its codomain
preserves all Ky Fan prefix gauges. -/
@[simp]
theorem kyFanGauge_toComplL_comp (T : E →L[𝕜] F) (k : ℕ) :
    ((Completion.toComplL : F →L[𝕜] Completion F) ∘L T).kyFanGauge k = T.kyFanGauge k :=
  T.sameSingularValues_toComplL_comp.kyFanGauge_eq k

end ContinuousLinearMap
