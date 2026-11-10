/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Basic
import TauCeti.Algebra.BigOperators.Group.Finset.Indicator
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.MeasurableSpace.Metric

/-!
# Compact integral operators with continuous kernels

Let `K : α → β → (F →L[𝕜] G)` be a kernel that is continuous on a product `s ×ˢ t` of compact
subsets of metric spaces and vanishes outside it. If the target `G` is finite-dimensional, the
integral operator `u ↦ (x ↦ ∫ y, K x y (u y) ∂ν)` of `TauCeti.integralOperatorLp` is a compact
operator `Lᵖ(ν; F) → Lᵖ(μ; G)` for every `1 ≤ p ≤ ∞`, whenever `μ` and `ν` are finite on
compact sets (`TauCeti.isCompactOperator_integralOperatorLp_of_continuousOn`).

The proof approximates `K` uniformly by kernels that are piecewise constant in the first
variable. Cover `s` by finitely many balls of radius `δ` and make the cover disjoint, giving a
measurable partition `s = ⋃ i, Pᵢ` with `Pᵢ ⊆ ball cᵢ δ`; replace `K x y` by `K cᵢ y` for
`x ∈ Pᵢ`. By uniform continuity of `K` on `s ×ˢ t` the difference is at most `ε` on `s ×ˢ t`
and zero outside it, so Schur's test bounds the difference of the operators by
`ε * max (ν t) (μ s)` (`TauCeti.norm_integralOperatorLp_le_max`). The approximating operator
sends `u` to `∑ i, 1_{Pᵢ} • ∫ y, K cᵢ y (u y) ∂ν`, whose range lies in the span of the indicator
classes of the `Pᵢ` with constants in `G`, which is finite-dimensional. Compact operators form a
closed set (`isClosed_setOfPred_isCompactOperator`), so `K` gives a compact operator.

Typical uses are Rellich-type compactness statements, where an operator splits into a part with
a continuous kernel on a compact set and a remainder of small Schur norm.

## Main declarations

* `TauCeti.isCompactOperator_integralOperatorLp_sum_indicator`: an integral operator whose kernel
  is piecewise constant in the output variable on finitely many disjoint sets of finite measure
  has finite rank, so it is compact.
* `TauCeti.isCompactOperator_integralOperatorLp_of_continuousOn`: an integral operator whose
  kernel is continuous on a compact product set and zero outside it, with finite-dimensional
  values, is compact.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  revised edition, Academic Press, 1980, Section VI.5 (compact operators as norm limits of
  finite-rank operators).
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal NNReal

namespace TauCeti

variable {α β 𝕜 F G : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [SFinite μ] [SFinite ν] [NormedSpace ℝ G]
  [SMulCommClass ℝ 𝕜 G] {p : ℝ≥0∞} [Fact (1 ≤ p)]

section FiniteRank

variable [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 G]

/-- An integral operator whose kernel is piecewise constant in the output variable,
`K x y = L i y` for `x ∈ P i` and `0` off `⋃ i, P i`, with pairwise disjoint sets `P i` of finite
measure, has finite rank, so it is compact: its values are the classes of
`∑ i, 1_{P i} • ∫ y, L i y (u y) ∂ν`. -/
theorem isCompactOperator_integralOperatorLp_sum_indicator {ι : Type*} [Fintype ι]
    {P : ι → Set α} (hPm : ∀ i, MeasurableSet (P i)) (hμP : ∀ i, μ (P i) ≠ ∞)
    (hPd : Pairwise (Disjoint on P)) {L : ι → β → F →L[𝕜] G}
    {hK : AEStronglyMeasurable (uncurry fun x y ↦ ∑ i, (P i).indicator (fun _ ↦ L i y) x)
      (μ.prod ν)} {A B : ℝ≥0}
    {hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖∑ i, (P i).indicator (fun _ ↦ L i y) x‖ₑ ∂ν ≤ A}
    {hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖∑ i, (P i).indicator (fun _ ↦ L i y) x‖ₑ ∂μ ≤ B} :
    IsCompactOperator (integralOperatorLp (fun x y ↦ ∑ i, (P i).indicator (fun _ ↦ L i y) x)
      p hK hA hB) := by
  classical
  have : CompleteSpace 𝕜 := IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace 𝕜
  have : CompleteSpace G := FiniteDimensional.complete 𝕜 G
  let ind (i : ι) : G →ₗ[𝕜] Lp G p μ :=
    { toFun := indicatorConstLp p (hPm i) (hμP i)
      map_add' _ _ := indicatorConstLp_add.symm
      map_smul' a v := indicatorConstLp_smul (hPm i) (hμP i) a v }
  let Λ : (ι → G) →ₗ[𝕜] Lp G p μ := ∑ i, ind i ∘ₗ LinearMap.proj i
  set T := integralOperatorLp (fun x y ↦ ∑ i, (P i).indicator (fun _ ↦ L i y) x) p hK hA hB
  have hrange : LinearMap.range (T : Lp F p ν →ₗ[𝕜] Lp G p μ) ≤ LinearMap.range Λ := by
    rintro _ ⟨u, rfl⟩
    refine ⟨fun i ↦ ∫ y, L i y (u y) ∂ν, (integralOperatorLp_eq_iff.2 ?_).symm⟩
    have hΛ : Λ (fun i ↦ ∫ y, L i y (u y) ∂ν) =
        ∑ i, indicatorConstLp p (hPm i) (hμP i) (∫ y, L i y (u y) ∂ν) := by
      simp [Λ, ind]
    rw [hΛ]
    filter_upwards [Lp.coeFn_finsetSum (μ := μ) (p := p) Finset.univ
        fun i ↦ indicatorConstLp p (hPm i) (hμP i) (∫ y, L i y (u y) ∂ν),
      ae_all_iff.2 fun i ↦ indicatorConstLp_coeFn (p := p) (hs := hPm i) (hμs := hμP i)
        (c := ∫ y, L i y (u y) ∂ν)] with x hx hind
    rw [hx, Finset.sum_apply]
    simp only [hind]
    by_cases hxP : ∃ i, x ∈ P i
    · obtain ⟨i, hi⟩ := hxP
      simp only [Finset.sum_indicator_apply_of_mem (hPd.set_pairwise _) (Finset.mem_univ i) hi]
    · push Not at hxP
      simp [indicator_of_notMem (hxP _)]
  have : FiniteDimensional 𝕜 (LinearMap.range (T : Lp F p ν →ₗ[𝕜] Lp G p μ)) :=
    Submodule.finiteDimensional_of_le hrange
  exact LinearMap.HasFiniteRange.isCompactOperator ((Submodule.fg_iff_finiteDimensional _).2 this)

end FiniteRank

variable [MetricSpace α] [OpensMeasurableSpace α] [IsFiniteMeasureOnCompacts μ]
  [MetricSpace β] [OpensMeasurableSpace β] [SecondCountableTopology β]
  [IsFiniteMeasureOnCompacts ν] [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 G]

/-- **Integral operators with continuous kernels on compact sets are compact.** If the kernel
`K : α → β → (F →L[𝕜] G)` is continuous on a product `s ×ˢ t` of compact sets, vanishes outside
it, and `G` is finite-dimensional, then its integral operator on `Lᵖ` is a compact operator,
for every `1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_integralOperatorLp_of_continuousOn {K : α → β → F →L[𝕜] G}
    {s : Set α} {t : Set β} (hs : IsCompact s) (ht : IsCompact t)
    (hKc : ContinuousOn (uncurry K) (s ×ˢ t)) (hK0 : ∀ x y, (x, y) ∉ s ×ˢ t → K x y = 0)
    {hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)} {A B : ℝ≥0}
    {hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A} {hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B} :
    IsCompactOperator (integralOperatorLp K p hK hA hB) := by
  have : CompleteSpace 𝕜 := IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace 𝕜
  have : CompleteSpace G := FiniteDimensional.complete 𝕜 G
  have hsm : MeasurableSet s := hs.isClosed.measurableSet
  have htm : MeasurableSet t := ht.isClosed.measurableSet
  have hμs : μ s ≠ ∞ := hs.measure_lt_top.ne
  have hνt : ν t ≠ ∞ := ht.measure_lt_top.ne
  set m : ℝ≥0 := max (ν t).toNNReal (μ s).toNNReal
  -- It suffices to approximate the operator in norm by compact operators.
  refine isClosed_setOfPred_isCompactOperator.closure_subset (Metric.mem_closure_iff.2
    fun ε hε ↦ ?_)
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ≥0, (ε₀ : ℝ) = ε / (2 * (m + 1)) :=
    ⟨⟨ε / (2 * (m + 1)), by positivity⟩, rfl⟩
  have hε₀ : 0 < ε₀ := by
    rw [← NNReal.coe_pos, hε₀def]
    positivity
  obtain ⟨n, c, P, hcs, hPm, hPs, hPd, hD⟩ := hs.exists_enorm_sub_sum_indicator_le ht hKc hK0 hε₀
  obtain ⟨M, hM⟩ := (hs.prod ht).exists_bound_of_continuousOn hKc
  -- Measurability and Schur bounds of the piecewise constant kernel `Kε`.
  have hslice (i : Fin n) : AEStronglyMeasurable (K (c i)) ν := by
    have heq : K (c i) = t.indicator (K (c i)) := by
      ext1 y
      by_cases hy : y ∈ t
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy, hK0 (c i) y fun h ↦ hy h.2]
    rw [heq, aestronglyMeasurable_indicator_iff htm]
    exact (hKc.comp (continuousOn_const.prodMk continuousOn_id)
      fun y hy ↦ ⟨hcs i, hy⟩).aestronglyMeasurable htm
  have hKεm := aestronglyMeasurable_uncurry_sum_indicator (μ := μ) hPm hslice
  have hKεb (x : α) (y : β) : ‖∑ i, (P i).indicator (fun _ ↦ K (c i) y) x‖ₑ ≤
      s.indicator (fun _ ↦ t.indicator (fun _ ↦ (M.toNNReal : ℝ≥0∞)) y) x := by
    by_cases hxP : ∃ i, x ∈ P i
    · obtain ⟨i, hi⟩ := hxP
      rw [Finset.sum_indicator_apply_of_mem (hPd.set_pairwise _) (Finset.mem_univ i) hi,
        indicator_of_mem (hPs i hi)]
      by_cases hy : y ∈ t
      · rw [indicator_of_mem hy, ← ofReal_norm]
        refine ENNReal.ofReal_le_of_le_toReal ?_
        rw [ENNReal.coe_toReal]
        exact (hM (c i, y) ⟨hcs i, hy⟩).trans (Real.le_coe_toNNReal M)
      · rw [hK0 (c i) y fun h ↦ hy h.2, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
        exact zero_le
    · push Not at hxP
      rw [Finset.sum_eq_zero fun i _ ↦ indicator_of_notMem (hxP i) _, ← ofReal_norm, norm_zero,
        ENNReal.ofReal_zero]
      exact zero_le
  have hμP (i : Fin n) : μ (P i) ≠ ∞ := (measure_mono (hPs i)).trans_lt hs.measure_lt_top |>.ne
  -- The row and column bounds `ε₀ * m` of the difference `K - Kε`, by the uniform approximation.
  have hDA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y - ∑ i, (P i).indicator (fun _ ↦ K (c i) y) x‖ₑ ∂ν ≤
      ((ε₀ * m : ℝ≥0) : ℝ≥0∞) :=
    .of_forall fun x ↦ (lintegral_enorm_row_le_of_le_indicator htm hD x).trans (by
      rw [ENNReal.coe_mul, ← ENNReal.coe_toNNReal hνt]
      gcongr
      exact_mod_cast le_max_left _ _)
  have hDB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y - ∑ i, (P i).indicator (fun _ ↦ K (c i) y) x‖ₑ ∂μ ≤
      ((ε₀ * m : ℝ≥0) : ℝ≥0∞) :=
    .of_forall fun y ↦ (lintegral_enorm_column_le_of_le_indicator hsm hD y).trans (by
      rw [ENNReal.coe_mul, ← ENNReal.coe_toNNReal hμs]
      gcongr
      exact_mod_cast le_max_right _ _)
  refine ⟨integralOperatorLp _ p hKεm
    (A := M.toNNReal * (ν t).toNNReal) (B := M.toNNReal * (μ s).toNNReal)
    (.of_forall fun x ↦ (lintegral_enorm_row_le_of_le_indicator htm hKεb x).trans_eq (by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hνt]))
    (.of_forall fun y ↦ (lintegral_enorm_column_le_of_le_indicator hsm hKεb y).trans_eq (by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hμs])),
    isCompactOperator_integralOperatorLp_sum_indicator hPm hμP hPd, ?_⟩
  -- Schur's test bounds the difference by `ε₀ m < ε`.
  rw [dist_eq_norm, integralOperatorLp_sub (hK := hK.sub hKεm) (hA := hDA) (hB := hDB)]
  refine norm_integralOperatorLp_le_max.trans_lt ?_
  rw [max_self, NNReal.coe_mul]
  calc (ε₀ : ℝ) * m ≤ ε₀ * (m + 1) := by gcongr; exact le_add_of_nonneg_right zero_le_one
    _ = ε / 2 := by rw [hε₀def]; field_simp
    _ < ε := half_lt_self hε

end TauCeti
