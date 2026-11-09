/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
import TauCeti.MeasureTheory.Function.Lp.Indicator

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

* `TauCeti.integralOperatorLp_sub`: the integral operator of `K₁ - K₂` is the difference of the
  integral operators of `K₁` and `K₂`.
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
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

omit [MeasurableSpace α] in
/-- A kernel bounded by `c` on `s ×ˢ t` and zero outside has row integrals at most `c * ν t`. -/
private theorem lintegral_enorm_le_of_le_indicator {L : α → β → F →L[𝕜] G} {s : Set α}
    {t : Set β} (ht : MeasurableSet t) {c : ℝ≥0∞}
    (hL : ∀ x y, ‖L x y‖ₑ ≤ s.indicator (fun _ ↦ t.indicator (fun _ ↦ c) y) x) (x : α) :
    ∫⁻ y, ‖L x y‖ₑ ∂ν ≤ c * ν t := by
  calc ∫⁻ y, ‖L x y‖ₑ ∂ν ≤ ∫⁻ y, t.indicator (fun _ ↦ c) y ∂ν := by
        refine lintegral_mono fun y ↦ (hL x y).trans ?_
        by_cases hx : x ∈ s <;> simp [hx]
    _ = c * ν t := lintegral_indicator_const ht c

omit [MeasurableSpace β] in
/-- A kernel bounded by `c` on `s ×ˢ t` and zero outside has column integrals at most
`c * μ s`. -/
private theorem lintegral_enorm_le_of_le_indicator' {L : α → β → F →L[𝕜] G} {s : Set α}
    {t : Set β} (hs : MeasurableSet s) {c : ℝ≥0∞}
    (hL : ∀ x y, ‖L x y‖ₑ ≤ s.indicator (fun _ ↦ t.indicator (fun _ ↦ c) y) x) (y : β) :
    ∫⁻ x, ‖L x y‖ₑ ∂μ ≤ c * μ s := by
  calc ∫⁻ x, ‖L x y‖ₑ ∂μ ≤ ∫⁻ x, s.indicator (fun _ ↦ c) x ∂μ := by
        refine lintegral_mono fun x ↦ (hL x y).trans ?_
        by_cases hx : x ∈ s <;> by_cases hy : y ∈ t <;> simp [hx, hy]
    _ = c * μ s := lintegral_indicator_const hs c

omit [MeasurableSpace α] in
/-- On a family of pairwise disjoint sets, a sum of indicators of constants takes at `x ∈ P i` the
value of the `i`-th constant. -/
private theorem sum_indicator_apply_of_mem {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    {P : ι → Set α} (hPd : Pairwise (Disjoint on P)) {x : α} {i : ι} (hx : x ∈ P i)
    (f : ι → M) : ∑ j, (P j).indicator (fun _ ↦ f j) x = f i := by
  classical
  rw [Finset.sum_eq_single i (fun j _ hji ↦ indicator_of_notMem
    (Set.disjoint_left.1 (hPd hji.symm) hx) _) (by simp), indicator_of_mem hx]

/-- A kernel that is piecewise constant in the first variable, equal to `L i y` on `P i`, is
measurable when the sets `P i` and the slices `L i` are. -/
private theorem aestronglyMeasurable_sum_indicator {ι : Type*} [Fintype ι]
    {P : ι → Set α} (hPm : ∀ i, MeasurableSet (P i)) {L : ι → β → F →L[𝕜] G}
    (hL : ∀ i, AEStronglyMeasurable (L i) ν) :
    AEStronglyMeasurable (uncurry fun x y ↦ ∑ i, (P i).indicator (fun _ ↦ L i y) x)
      (μ.prod ν) := by
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦ ?_
  have : (fun z : α × β ↦ (P i).indicator (fun _ ↦ L i z.2) z.1) =
      (P i ×ˢ univ).indicator fun z ↦ L i z.2 := by
    ext1 z
    by_cases hz : z.1 ∈ P i <;> simp [hz, indicator]
  simpa only [uncurry_def, this] using ((hL i).comp_snd (μ := μ)).indicator ((hPm i).prod .univ)

variable [SFinite μ] [SFinite ν] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integral operator of the difference of two kernels is the difference of their integral
operators. -/
theorem integralOperatorLp_sub {K₁ K₂ : α → β → F →L[𝕜] G}
    {hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν)} {A₁ B₁ : ℝ≥0}
    {hA₁ : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₁ x y‖ₑ ∂ν ≤ A₁} {hB₁ : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₁ x y‖ₑ ∂μ ≤ B₁}
    {hK₂ : AEStronglyMeasurable (uncurry K₂) (μ.prod ν)} {A₂ B₂ : ℝ≥0}
    {hA₂ : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₂ x y‖ₑ ∂ν ≤ A₂} {hB₂ : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₂ x y‖ₑ ∂μ ≤ B₂}
    {hK : AEStronglyMeasurable (uncurry fun x y ↦ K₁ x y - K₂ x y) (μ.prod ν)} {A B : ℝ≥0}
    {hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₁ x y - K₂ x y‖ₑ ∂ν ≤ A}
    {hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₁ x y - K₂ x y‖ₑ ∂μ ≤ B} :
    integralOperatorLp K₁ p hK₁ hA₁ hB₁ - integralOperatorLp K₂ p hK₂ hA₂ hB₂ =
      integralOperatorLp (fun x y ↦ K₁ x y - K₂ x y) p hK hA hB := by
  refine ContinuousLinearMap.ext fun u ↦ (integralOperatorLp_eq_iff.2 ?_).symm
  filter_upwards [ae_integrable_apply_of_memLp hK₁ (Lp.memLp u) Fact.out hA₁ hB₁,
    ae_integrable_apply_of_memLp hK₂ (Lp.memLp u) Fact.out hA₂ hB₂,
    coeFn_integralOperatorLp (hK := hK₁) (hA := hA₁) (hB := hB₁) u,
    coeFn_integralOperatorLp (hK := hK₂) (hA := hA₂) (hB := hB₂) u,
    Lp.coeFn_sub (integralOperatorLp K₁ p hK₁ hA₁ hB₁ u)
      (integralOperatorLp K₂ p hK₂ hA₂ hB₂ u)] with x h₁ h₂ e₁ e₂ e
  rw [sub_apply, e, Pi.sub_apply, e₁, e₂, ← integral_sub h₁ h₂]
  simp only [sub_apply]

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
      simp only [sum_indicator_apply_of_mem hPd hi]
    · push Not at hxP
      simp [indicator_of_notMem (hxP _)]
  have : FiniteDimensional 𝕜 (LinearMap.range (T : Lp F p ν →ₗ[𝕜] Lp G p μ)) :=
    Submodule.finiteDimensional_of_le hrange
  exact LinearMap.HasFiniteRange.isCompactOperator ((Submodule.fg_iff_finiteDimensional _).2 this)

end FiniteRank

variable [MetricSpace α] [OpensMeasurableSpace α] [IsFiniteMeasureOnCompacts μ]
  [MetricSpace β] [OpensMeasurableSpace β] [SecondCountableTopology β]
  [IsFiniteMeasureOnCompacts ν]

/-- A compact set of a metric space has, for every `δ > 0`, a finite measurable partition into
pieces `P i ⊆ ball (c i) δ` with centers `c i ∈ s`. -/
private theorem exists_measurable_partition_ball {s : Set α} (hs : IsCompact s) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (n : ℕ) (c : Fin n → α) (P : Fin n → Set α), (∀ i, c i ∈ s) ∧
      (∀ i, MeasurableSet (P i)) ∧ (∀ i, P i ⊆ s ∩ Metric.ball (c i) δ) ∧
      Pairwise (Disjoint on P) ∧ ⋃ i, P i = s := by
  obtain ⟨T, hTs, hT, hcover⟩ := finite_cover_balls_of_compact hs hδ
  have := hT.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  set c : Fin n → α := fun i ↦ e.symm i
  set f : Fin n → Set α := fun i ↦ s ∩ Metric.ball (c i) δ
  have hf : ∀ i, MeasurableSet (f i) := fun i ↦ hs.isClosed.measurableSet.inter
    Metric.isOpen_ball.measurableSet
  refine ⟨n, c, disjointed f, fun i ↦ hTs (e.symm i).2, fun i ↦ ?_,
    fun i ↦ disjointed_subset f i, disjoint_disjointed f, ?_⟩
  · rw [disjointed_eq_inter_compl]
    exact (hf i).inter (.iInter fun j ↦ .iInter fun _ ↦ (hf j).compl)
  · rw [iUnion_disjointed]
    refine Subset.antisymm (iUnion_subset fun i ↦ inter_subset_left) fun x hx ↦ ?_
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcover hx)
    exact mem_iUnion.2 ⟨e ⟨y, hy⟩, hx, by simpa [c] using hxy⟩

omit [MeasurableSpace β] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [OpensMeasurableSpace β]
  [SecondCountableTopology β] in
/-- The uniform approximation step: a kernel continuous on a compact product `s ×ˢ t` and zero
outside it is within `ε` of a kernel that is piecewise constant in the first variable, on a finite
measurable partition of `s`, and equal to slices `K (c i)` of `K`. -/
private theorem exists_sum_indicator_approx {K : α → β → F →L[𝕜] G} {s : Set α} {t : Set β}
    (hs : IsCompact s) (ht : IsCompact t) (hKc : ContinuousOn (uncurry K) (s ×ˢ t))
    (hK0 : ∀ x y, (x, y) ∉ s ×ˢ t → K x y = 0) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → α) (P : Fin n → Set α), (∀ i, c i ∈ s) ∧
      (∀ i, MeasurableSet (P i)) ∧ (∀ i, P i ⊆ s) ∧ Pairwise (Disjoint on P) ∧
      ∀ x y, ‖K x y - ∑ i, (P i).indicator (fun _ ↦ K (c i) y) x‖ₑ ≤
        s.indicator (fun _ ↦ t.indicator (fun _ ↦ (ε : ℝ≥0∞)) y) x := by
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    ((hs.prod ht).uniformContinuousOn_of_continuous hKc) ε (by exact_mod_cast hε)
  obtain ⟨n, c, P, hcs, hPm, hPs, hPd, hPU⟩ := exists_measurable_partition_ball hs hδ
  refine ⟨n, c, P, hcs, hPm, fun i x hx ↦ (hPs i hx).1, hPd, fun x y ↦ ?_⟩
  by_cases hx : x ∈ s
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hPU.symm ▸ hx)
    rw [sum_indicator_apply_of_mem hPd hi, indicator_of_mem hx]
    by_cases hy : y ∈ t
    · rw [indicator_of_mem hy, ← ofReal_norm, ← dist_eq_norm]
      refine ENNReal.ofReal_le_of_le_toReal ?_
      have h := hunif (x, y) ⟨hx, hy⟩ (c i, y) ⟨hcs i, hy⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact (hPs i hi).2)
      simpa using h.le
    · rw [hK0 x y fun h ↦ hy h.2, hK0 (c i) y fun h ↦ hy h.2, sub_zero, ← ofReal_norm,
        norm_zero, ENNReal.ofReal_zero]
      exact zero_le
  · rw [Finset.sum_eq_zero fun i _ ↦ indicator_of_notMem (fun h ↦ hx (hPs i h).1) _,
      hK0 x y fun h ↦ hx h.1, sub_zero, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
    exact zero_le

variable [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 G]

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
  obtain ⟨n, c, P, hcs, hPm, hPs, hPd, hD⟩ := exists_sum_indicator_approx hs ht hKc hK0 hε₀
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
  have hKεm := aestronglyMeasurable_sum_indicator (μ := μ) hPm hslice
  have hKεb (x : α) (y : β) : ‖∑ i, (P i).indicator (fun _ ↦ K (c i) y) x‖ₑ ≤
      s.indicator (fun _ ↦ t.indicator (fun _ ↦ (M.toNNReal : ℝ≥0∞)) y) x := by
    by_cases hxP : ∃ i, x ∈ P i
    · obtain ⟨i, hi⟩ := hxP
      rw [sum_indicator_apply_of_mem hPd hi, indicator_of_mem (hPs i hi)]
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
    .of_forall fun x ↦ (lintegral_enorm_le_of_le_indicator htm hD x).trans (by
      rw [ENNReal.coe_mul, ← ENNReal.coe_toNNReal hνt]
      gcongr
      exact_mod_cast le_max_left _ _)
  have hDB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y - ∑ i, (P i).indicator (fun _ ↦ K (c i) y) x‖ₑ ∂μ ≤
      ((ε₀ * m : ℝ≥0) : ℝ≥0∞) :=
    .of_forall fun y ↦ (lintegral_enorm_le_of_le_indicator' hsm hD y).trans (by
      rw [ENNReal.coe_mul, ← ENNReal.coe_toNNReal hμs]
      gcongr
      exact_mod_cast le_max_right _ _)
  refine ⟨integralOperatorLp _ p hKεm
    (A := M.toNNReal * (ν t).toNNReal) (B := M.toNNReal * (μ s).toNNReal)
    (.of_forall fun x ↦ (lintegral_enorm_le_of_le_indicator htm hKεb x).trans_eq (by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hνt]))
    (.of_forall fun y ↦ (lintegral_enorm_le_of_le_indicator' hsm hKεb y).trans_eq (by
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
