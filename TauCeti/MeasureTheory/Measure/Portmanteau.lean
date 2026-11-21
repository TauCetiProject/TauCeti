/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Measure.Portmanteau

import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.Layercake
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Continuity sets, null-boundary thickenings and finite partitions

The portmanteau theorem makes the masses of a set converge along weak convergence as soon as the
limit law does not charge the boundary of the set. Mathlib's `exists_null_frontier_thickening`
supplies, for one set, thickening radii in any interval whose thickenings have null boundary. This
file chooses a single radius that works simultaneously for countably many sets. It then uses this
to cut a separable space into finitely many continuity sets of small diameter, apart from one set
of arbitrarily small probability.

Weak convergence of finite measures also implies convergence of their masses on sets with
null boundary, including when the limit measure is zero. This extends the probability-measure
portmanteau API and is useful when localizing locally finite measures.

Finally, this file provides arbitrary-filter versions of the open-set (`(O) ⇒ (T)`) and bounded
Lipschitz (`(T) ⇔ (Lip)`) portmanteau criteria for `MeasureTheory.ProbabilityMeasure`, removing the
`Filter.IsCountablyGenerated` hypothesis of Mathlib's versions via finite Riemann-sum
approximations of nonnegative bounded continuous functions.

## Main statements

* `MeasureTheory.FiniteMeasure.tendsto_measure_of_null_frontier_of_tendsto` — weak convergence
  of finite measures implies convergence on every continuity set of the limit measure.
* `MeasureTheory.Measure.exists_forall_null_frontier_thickening` — for countably many sets, some
  radius in any nonempty open interval gives thickenings whose boundaries are all null.
* `MeasureTheory.Measure.exists_partition_null_frontier_small_last` — a finite measure on a
  separable pseudometric space admits a finite measurable partition into null-boundary sets, all but
  the last lying in balls of a prescribed radius and the last having arbitrarily small measure.
* `MeasureTheory.Measure.tendsto_measure_nndist_ge_atTop` — the mass of the region at distance at
  least `n` from a basepoint tends to `0` for a finite measure.
* `MeasureTheory.ProbabilityMeasure.exists_measure_nndist_ge_le_of_tendsto` — along a weakly
  convergent family of probability measures, the mass outside some ball about a basepoint is
  eventually at most any prescribed `ε > 0`.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_forall_isOpen_le_liminf` — open-set portmanteau
  implication `(O) ⇒ (T)` along an arbitrary filter, without countable generation.
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto` — bounded
  Lipschitz portmanteau characterization `(T) ⇔ (Lip)` along an arbitrary filter, without countable
  generation.

## Source

* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto` is adapted from
  Mathlib's proof of `MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`
  (`Mathlib/MeasureTheory/Measure/Portmanteau.lean`), replacing the countably generated closed-set
  portmanteau step with the arbitrary-filter finite Riemann-sum `(O) ⇒ (T)` argument in
  `MeasureTheory.ProbabilityMeasure.tendsto_of_forall_isOpen_le_liminf`.

## References

* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Theorem 2.1.
-/

public section

open Filter Function MeasureTheory Set
open scoped ContDiff ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]

/-- For countably many sets `s k` and an s-finite measure `μ`, some radius in any nonempty open
interval gives thickenings whose boundaries are all `μ`-null: for each set only countably many
radii fail, and a nonempty open interval of reals is uncountable. -/
theorem exists_forall_null_frontier_thickening (μ : Measure Ω) [SFinite μ] {ι : Type*}
    [Countable ι] (s : ι → Set Ω) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, ∀ k, μ (frontier (Metric.thickening r (s k))) = 0 := by
  have hcount (k : ι) : {r : ℝ | 0 < μ (frontier (Metric.thickening r (s k)))}.Countable :=
    countable_meas_pos_of_disjoint_iUnion (fun r ↦ isClosed_frontier.measurableSet)
      (Metric.frontier_thickening_disjoint (s k))
  obtain ⟨r, hr, hr'⟩ :
      (Ioo a b \ ⋃ k, {r : ℝ | 0 < μ (frontier (Metric.thickening r (s k)))}).Nonempty := by
    refine nonempty_of_not_subset fun hsub ↦ ?_
    exact (Cardinal.Real.Ioo_countable_iff.1 ((countable_iUnion hcount).mono hsub)).not_gt hab
  refine ⟨r, hr, fun k ↦ ?_⟩
  by_contra hk
  exact hr' (mem_iUnion.2 ⟨k, pos_iff_ne_zero.2 hk⟩)

/-- For a dense sequence `u` and a radius `ρ > 0`, the complement of the union of the first `N`
balls of radius `ρ` around the points `u k` has measure tending to `0` as `N → ∞`. -/
theorem tendsto_measure_compl_biUnion_lt_ball {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {u : ℕ → X} (hu : DenseRange u)
    {ρ : ℝ} (hρ0 : 0 < ρ) :
    Tendsto (fun N ↦ μ (⋃ k < N, Metric.ball (u k) ρ)ᶜ) atTop (𝓝 0) := by
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun N ↦ (⋃ k < N, Metric.ball (u k) ρ)ᶜ)
    (fun N ↦ (MeasurableSet.iUnion fun _ ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_ball).compl.nullMeasurableSet)
    (fun M N hMN ↦ compl_subset_compl.2 <| iUnion_mono fun _ ↦
      iUnion_subset_iUnion_const fun hk ↦ lt_of_lt_of_le hk hMN) ⟨0, measure_ne_top _ _⟩
  have hempty : ⋂ N, (⋃ k < N, Metric.ball (u k) ρ)ᶜ = ∅ := by
    rw [← compl_iUnion, compl_empty_iff, eq_univ_iff_forall]
    intro x
    obtain ⟨k, hk⟩ := (Metric.denseRange_iff.1 hu) x ρ hρ0
    exact mem_iUnion.2 ⟨k + 1, mem_iUnion₂.2 ⟨k, Nat.lt_succ_self k, Metric.mem_ball.2 hk⟩⟩
  simpa only [Function.comp_def, hempty, measure_empty] using hlim

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace.SeparableSpace X]

/-- A finite partition of `X` into pieces of `μ`-null boundary: all but the last piece lie in
balls of radius `r`, and the last piece has `μ`-mass at most `ε`. -/
theorem exists_partition_null_frontier_small_last (μ : Measure X) [IsFiniteMeasure μ] {r : ℝ}
    (hr : 0 < r) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (N : ℕ) (A : Fin (N + 1) → Set X), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (Disjoint on A) ∧ (⋃ i, A i) = univ ∧ (∀ i, μ (frontier (A i)) = 0) ∧
      (∀ i : Fin (N + 1), i ≠ Fin.last N → ∃ x, A i ⊆ Metric.ball x r) ∧
      μ (A (Fin.last N)) ≤ ε := by
  -- On the empty space the single cell `univ` is null.
  cases isEmpty_or_nonempty X
  · refine ⟨0, fun _ ↦ univ, fun _ ↦ .univ,
      fun i j hij ↦ (hij (Subsingleton.elim (α := Fin 1) i j)).elim, iUnion_const _,
      fun _ ↦ by simp, fun i hi ↦ (hi (Subsingleton.elim (α := Fin 1) _ _)).elim, ?_⟩
    simp [univ_eq_empty_iff.2 ‹IsEmpty X›]
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
  obtain ⟨ρ, ⟨hρ0, hρr⟩, hρ⟩ := μ.exists_forall_null_frontier_thickening (fun k ↦ {u k}) hr
  simp only [Metric.thickening_singleton] at hρ
  -- The union of the first `N` balls exhausts the space, so its complement becomes small.
  set G : ℕ → Set X := fun N ↦ ⋃ k < N, Metric.ball (u k) ρ
  have hG : Tendsto (fun N ↦ μ (G N)ᶜ) atTop (𝓝 0) :=
    tendsto_measure_compl_biUnion_lt_ball μ hu hρ0
  obtain ⟨N, hN⟩ := (hG.eventually (ge_mem_nhds hε)).exists
  -- The cells: the first `N` balls made disjoint, followed by the rest of the space.
  set f : Fin (N + 1) → Set X := fun i ↦
    if (i : ℕ) < N then Metric.ball (u i) ρ else univ with hf
  have hfm (i : Fin (N + 1)) : MeasurableSet (f i) := by
    simp only [hf]
    split_ifs
    exacts [measurableSet_ball, MeasurableSet.univ]
  have hff (i : Fin (N + 1)) : μ (frontier (f i)) = 0 := by
    simp only [hf]
    split_ifs
    exacts [hρ _, by simp]
  refine ⟨N, disjointed f, fun i ↦ disjointedRec (p := MeasurableSet)
    (fun t j ht ↦ ht.diff (hfm j)) (hfm i), disjoint_disjointed f, ?_, fun i ↦ ?_, fun i hi ↦ ?_,
    ?_⟩
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    exact fun x ↦ mem_iUnion.2 ⟨Fin.last N, by simp [hf]⟩
  · refine disjointedRec (p := fun t ↦ μ (frontier t) = 0) (fun t j ht ↦ ?_) (hff i)
    rw [Set.sdiff_eq]
    exact null_frontier_inter ht (by rw [frontier_compl]; exact hff j)
  · have hiN : (i : ℕ) < N := by simpa using Fin.val_lt_last hi
    refine ⟨u i, (disjointed_subset f i).trans ?_⟩
    simp only [hf, hiN, ite_true]
    exact Metric.ball_subset_ball hρr.le
  · refine le_trans (measure_mono fun x hx ↦ ?_) hN
    rw [disjointed_eq_inter_compl] at hx
    simp only [mem_inter_iff, mem_iInter, mem_compl_iff] at hx
    simp only [G, mem_compl_iff, mem_iUnion, not_exists]
    intro k hk hxk
    refine hx.2 ⟨k, by omega⟩ (Fin.mk_lt_of_lt_val (by simpa using hk)) ?_
    simp [hf, hk, hxk]

end MeasureTheory.Measure

namespace MeasureTheory.FiniteMeasure

variable {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X] [HasOuterApproxClosed X] {l : Filter ι}
  {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}

/-- Weak convergence of finite measures gives convergence on every continuity set of the
limit measure. No measurability assumption on the set is needed. -/
theorem tendsto_measure_of_null_frontier_of_tendsto
    (h : Tendsto μs l (𝓝 μ)) {s : Set X} (hs : (μ : Measure X) (frontier s) = 0) :
    Tendsto (fun i ↦ (μs i : Measure X) s) l (𝓝 ((μ : Measure X) s)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simpa only [Set.eq_empty_of_isEmpty s, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))
  by_cases hμ : μ = 0
  · subst μ
    simp only [toMeasure_zero, FunLike.coe_zero, Pi.zero_apply]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [Function.comp_def, ennreal_mass, zero_mass, ENNReal.coe_zero] using
        (ENNReal.continuous_coe.tendsto _).comp h.mass)
      (fun _ ↦ bot_le) (fun _ ↦ measure_mono (subset_univ s))
  · have hn := tendsto_normalize_of_tendsto h hμ
    have hboundary : (μ.normalize : Measure X) (frontier s) = 0 := by
      simp [toMeasure_normalize_eq_of_ne_zero μ hμ, hs]
    have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn
      (by simpa only [ProbabilityMeasure.null_iff_toMeasure_null] using hboundary)
    have hprod := h.mass.mul hp
    simp_rw [← self_eq_mass_mul_normalize] at hprod
    simpa only [Function.comp_def, ennreal_coeFn_eq_coeFn_toMeasure] using
      (ENNReal.continuous_coe.tendsto _).comp hprod

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.Measure

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The mass of the closed region at distance at least `n` from a basepoint tends to `0` as `n`
tends to infinity. -/
theorem tendsto_measure_nndist_ge_atTop (μ : Measure X) [IsFiniteMeasure μ] (x : X) :
    Tendsto (fun n : ℕ ↦ μ {y | (n : ℝ≥0) ≤ nndist x y}) atTop (𝓝 0) := by
  have := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun n : ℕ ↦ {y | (n : ℝ≥0) ≤ nndist x y})
    (fun n ↦ (isClosed_le continuous_const
      (continuous_const.nndist continuous_id)).measurableSet.nullMeasurableSet)
    (fun m n hmn y hy ↦ (Nat.cast_le.2 hmn).trans hy) ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n : ℕ, {y | (n : ℝ≥0) ≤ nndist x y}) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (nndist x y)
    exact (not_le.2 hn) (mem_iInter.1 hy n)
  simpa [hempty, Function.comp_def] using this

end MeasureTheory.Measure

namespace MeasureTheory.ProbabilityMeasure

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}

/-- **Mass outside a large ball for a weakly convergent family.** Along a weakly convergent family
of probability measures, for every `ε > 0` there is a radius `R` such that eventually the mass
outside the ball of radius `R` about a basepoint is at most `ε`. -/
theorem exists_measure_nndist_ge_le_of_tendsto (h : Tendsto μs L (𝓝 μ)) (x : X) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, (μs i : Measure X) {y | R ≤ nndist x y} ≤ ε := by
  have hS (r : ℝ≥0) : IsClosed {y | r ≤ nndist x y} :=
    isClosed_le continuous_const (continuous_const.nndist continuous_id)
  obtain ⟨n, hn⟩ := ((Measure.tendsto_measure_nndist_ge_atTop (μ : Measure X) x).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨n, ?_⟩
  have hlt := lt_of_le_of_lt
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h (hS n)) hn
  filter_upwards [Filter.eventually_lt_of_limsup_lt hlt] with i hi using hi.le

/-- Smooth compactly supported test functions determine weak convergence of probability measures
on a finite-dimensional real normed space. -/
theorem tendsto_of_forall_tendsto_integral_contDiff_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (h : ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure E)) l (𝓝 (∫ x, f x ∂(μ : Measure E)))) :
    Tendsto μs l (𝓝 μ) := by
  rcases eq_or_neBot l with rfl | hl
  · simp
  apply tendsto_of_forall_isOpen_le_liminf'
  intro U hU
  rw [hU.measure_eq_iSup_isCompact (μ : Measure E)]
  refine iSup₂_le fun K hKU ↦ iSup_le fun hK ↦ ?_
  obtain ⟨f, hf, h01, h1, hc, hsub⟩ := hK.exists_contDiff_cutoff hU hKU
  have htest := ENNReal.tendsto_ofReal (h f hf hc)
  have hl : ENNReal.ofReal (∫ x, f x ∂(μ : Measure E)) =
      l.liminf (fun i ↦ ENNReal.ofReal (∫ x, f x ∂(μs i : Measure E))) :=
    htest.liminf_eq.symm
  calc
    (μ : Measure E) K ≤ ENNReal.ofReal (∫ x, f x ∂(μ : Measure E)) :=
      (hf.continuous.integrable_of_hasCompactSupport hc).measure_le_integral
        (ae_of_all _ fun x ↦ (h01 (mem_range_self x)).1) fun x hx ↦ by
          have hfx : f x = 1 := interior_subset (h1 hx)
          exact hfx.ge
    _ = _ := hl
    _ ≤ _ := liminf_le_liminf (Eventually.of_forall fun i ↦
      integral_le_measure (fun x _ ↦ (h01 (mem_range_self x)).2) fun x hx ↦
        (Function.notMem_support.mp (fun hs ↦ hx (hsub (subset_tsupport f hs)))).le)

end MeasureTheory.ProbabilityMeasure

namespace MeasureTheory.ProbabilityMeasure

/-- Finite layer-cake approximation of the integral of a nonnegative bounded continuous function by
a Riemann sum of open superlevel-set probabilities. -/
private theorem integral_bounds_mul_sum_measureReal_gt
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (f : BoundedContinuousFunction X ℝ) (hf : 0 ≤ f)
    {k : ℕ} {a : ℝ} (ha : 0 < a) (hka : ∀ x, f x ≤ k * a) :
    ∫ x, f x ∂ν ≤ a * ∑ j ∈ Finset.range k, ν.real {x | (j : ℝ) * a < f x} ∧
      a * ∑ j ∈ Finset.range k, ν.real {x | (j : ℝ) * a < f x} ≤ (∫ x, f x ∂ν) + a := by
  let g : ℝ → ℝ := fun t ↦ ν.real {x | t < f x / a}
  have hg_anti : AntitoneOn g (Set.Icc 0 (0 + k)) :=
    fun _ _ _ _ hst ↦ measureReal_mono fun _ hx ↦ hst.trans_lt hx
  have hint : (∫ x, f x ∂ν) / a = ∫ t in (0 : ℝ)..0 + k, g t := by
    rw [← integral_div, ((f.integrable ν).div_const a).integral_eq_integral_meas_lt
      (ae_of_all _ fun x ↦ div_nonneg (hf x) ha.le)]
    rw [zero_add, intervalIntegral.integral_of_le (Nat.cast_nonneg k)]
    rw [← setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi
      Set.Ioc_subset_Ioi_self]
    refine Eventually.of_forall fun t ht ↦ ?_
    have hkt : (k : ℝ) < t := by
      simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at ht
      exact ht.2 ht.1
    have hempty : {x | t < f x / a} = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx ↦
      not_lt_of_ge ((div_le_iff₀ ha).2 (hka x)) (hkt.trans (Set.mem_ofPred_eq.mp hx))
    simp [g, hempty]
  have hle_sum : (∫ x, f x ∂ν) / a ≤ ∑ j ∈ Finset.range k, g j := by
    simpa only [zero_add] using hint.trans_le hg_anti.integral_le_sum
  have hsum_le : ∑ j ∈ Finset.range k, g j ≤ 1 + (∫ x, f x ∂ν) / a := by
    have hshift : g 0 + ∑ j ∈ Finset.range k, g (0 + ↑(j + 1)) =
        (∑ j ∈ Finset.range k, g j) + g k := by
      simp only [zero_add]
      calc g 0 + ∑ j ∈ Finset.range k, g ↑(j + 1)
          = (∑ j ∈ Finset.range k, g ↑(j + 1)) + g ↑(0 : ℕ) := by rw [Nat.cast_zero, add_comm]
        _ = ∑ j ∈ Finset.range (k + 1), g j := (Finset.sum_range_succ' (fun j : ℕ ↦ g j) k).symm
        _ = (∑ j ∈ Finset.range k, g j) + g k := Finset.sum_range_succ (fun j : ℕ ↦ g j) k
    have hgk : g k = 0 := by
      have hempty : {x | (k : ℝ) < f x / a} = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx ↦
        not_lt_of_ge ((div_le_iff₀ ha).2 (hka x)) (Set.mem_ofPred_eq.mp hx)
      simp [g, hempty]
    have hg0 : g 0 ≤ 1 := measureReal_le_one
    linarith [hg_anti.sum_le_integral]
  have hgj (j : ℕ) : g j = ν.real {x | (j : ℝ) * a < f x} := by
    simp only [g, lt_div_iff₀ ha]
  simp only [hgj] at hle_sum hsum_le
  refine ⟨(div_le_iff₀' ha).1 hle_sum, (le_div_iff₀' ha).1 ?_⟩
  rw [add_div, div_self ha.ne']
  linarith [hsum_le]

/-- Unpack a `liminf` lower bound for `ProbabilityMeasure` into an eventual real-valued bound. -/
private theorem eventually_measureReal_sub_lt_of_le_liminf
    {X ι : Type*} [MeasurableSpace X]
    {L : Filter ι} {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    {U : Set X} (hU : μ U ≤ L.liminf (fun i ↦ μs i U)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i in L, (μ : Measure X).real U - δ < (μs i : Measure X).real U := by
  have hU' : (μ U : ℝ) ≤ L.liminf (fun i ↦ (μs i U : ℝ)) := by
    rw [NNReal.toReal_liminf]
    exact NNReal.coe_le_coe.2 hU
  simpa only [measureReal_eq_coe_coeFn] using Filter.eventually_lt_of_lt_liminf
    ((sub_lt_self _ hδ).trans_le hU') (isBoundedUnder_of ⟨0, fun _ ↦ NNReal.coe_nonneg _⟩)

/-- **Portmanteau `(O) ⇒ (T)` for an arbitrary filter.** If `μ U ≤ liminf (μs · U)` along an
arbitrary filter `L` for every open set `U`, then `μs` converges weakly to `μ`. Unlike Mathlib's
`MeasureTheory.tendsto_of_forall_isOpen_le_liminf`, no countable-generation assumption on `L` is
required; the proof replaces Fatou's lemma along sequences with finite Riemann-sum approximations of
nonnegative bounded continuous functions. -/
theorem tendsto_of_forall_isOpen_le_liminf
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    {L : Filter ι} {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hopen : ∀ U : Set X, IsOpen U → μ U ≤ L.liminf (fun i ↦ μs i U)) :
    Tendsto μs L (𝓝 μ) := by
  rcases L.eq_or_neBot with rfl | _
  · simp
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 ?_
  refine BoundedContinuousFunction.tendsto_integral_of_forall_integral_le_liminf_integral
    fun f hf ↦ ?_
  have hbd_above : IsBoundedUnder (· ≤ ·) L (fun i ↦ ∫ x, f x ∂(μs i : Measure X)) :=
    BddAbove.isBoundedUnder L.univ_mem <| by
      simpa using (BoundedContinuousFunction.isBounded_range_integral
        (fun i ↦ (μs i : Measure X)) f).bddAbove
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set M : ℝ := ‖f‖ + 1
  have hM : 0 < M := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * M / ε)
  set k : ℕ := m + 1
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.succ_pos m)
  set a : ℝ := M / k
  have ha : 0 < a := by positivity
  have ha_lt : a < ε / 2 := by
    rw [show a = M / (k : ℝ) from rfl, div_lt_iff₀ hk_pos]
    nlinarith [(div_lt_iff₀ hε).1 hm, show (m : ℝ) < k from Nat.cast_lt.2 (Nat.lt_succ_self m)]
  have hka (x : X) : f x ≤ k * a := by
    rw [show (k : ℝ) * a = M from mul_div_cancel₀ M hk_pos.ne']
    linarith [le_trans (le_abs_self _) (f.norm_coe_le_norm x)]
  have hev : ∀ᶠ i in L, ∀ j ∈ Finset.range k,
      (μ : Measure X).real {x | (j : ℝ) * a < f x} - ε / (2 * M) <
        (μs i : Measure X).real {x | (j : ℝ) * a < f x} :=
    (Filter.eventually_all_finset (Finset.range k)).2 fun j _ ↦
      eventually_measureReal_sub_lt_of_le_liminf
        (hopen _ (isOpen_lt continuous_const f.continuous)) (by positivity)
  have hev_int : ∀ᶠ i in L, ∫ x, f x ∂(μ : Measure X) - ε ≤ ∫ x, f x ∂(μs i : Measure X) := by
    filter_upwards [hev] with i hi
    have hμ_le := (integral_bounds_mul_sum_measureReal_gt (μ : Measure X) f hf ha hka).1
    have hμi_ge := (integral_bounds_mul_sum_measureReal_gt (μs i : Measure X) f hf ha hka).2
    have hsum : ∑ j ∈ Finset.range k,
        ((μ : Measure X).real {x | (j : ℝ) * a < f x} - ε / (2 * M)) ≤
        ∑ j ∈ Finset.range k, (μs i : Measure X).real {x | (j : ℝ) * a < f x} :=
      Finset.sum_le_sum fun j hj ↦ (hi j hj).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hmul := mul_le_mul_of_nonneg_left hsum ha.le
    have hcancel : a * ((k : ℝ) * (ε / (2 * M))) = ε / 2 := by dsimp [a]; field_simp
    linarith
  linarith [Filter.le_liminf_of_le hbd_above.isCobounded_ge hev_int]

/-- **Portmanteau `(T) ⇔ (Lip)` for an arbitrary filter.** Weak convergence of probability measures
along an arbitrary filter `L` on a pseudo-emetric space with opens-measurable structure is
equivalent to convergence of integrals of all bounded Lipschitz functions. Adapted from Mathlib's
proof of `MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`, replacing the countably
generated closed-set criterion with `tendsto_of_forall_isOpen_le_liminf`. -/
theorem tendsto_iff_forall_lipschitz_integral_tendsto
    {X ι : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {L : Filter ι} {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X} :
    Tendsto μs L (𝓝 μ) ↔
      ∀ F : X → ℝ, (∃ M, ∀ x y, dist (F x) (F y) ≤ M) → (∃ K, LipschitzWith K F) →
        Tendsto (fun i ↦ ∫ x, F x ∂(μs i : Measure X)) L (𝓝 (∫ x, F x ∂(μ : Measure X))) := by
  constructor
  · intro h F hF_bd hF_lip
    let F' : BoundedContinuousFunction X ℝ :=
      { toFun := F
        continuous_toFun := hF_lip.choose_spec.continuous
        map_bounded' := hF_bd }
    simpa [F'] using ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h F'
  intro h
  rcases L.eq_or_neBot with rfl | _
  · simp
  have hclosed_real (s : Set X) (hs : IsClosed s) :
      L.limsup (fun i ↦ (μs i : Measure X).real s) ≤ (μ : Measure X).real s := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    let fs : ℕ → BoundedContinuousFunction X ℝ≥0 := fun n ↦
      thickenedIndicator (δ := (1 : ℝ) / (n + 1)) (by positivity) s
    have key₁ : Tendsto (fun n ↦ ∫ x, (fs n x : ℝ) ∂(μ : Measure X)) atTop
        (𝓝 ((μ : Measure X).real s)) :=
      tendsto_integral_thickenedIndicator_of_isClosed (μ : Measure X) hs
        (δs := fun n ↦ (1 : ℝ) / (n + 1)) (fun _ ↦ by positivity)
        tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨M, hM⟩ := eventually_atTop.1
      (key₁.eventually_lt_const (lt_add_of_pos_right _ (half_pos hε)))
    have hbd : ∃ C, ∀ x y, dist (fs M x : ℝ) (fs M y : ℝ) ≤ C := ⟨1, fun x y ↦ by
      rw [Real.dist_eq, abs_le]
      have h1 (z : X) : (fs M z : ℝ) ≤ 1 := thickenedIndicator_le_one _ _ _
      have h2 (z : X) : 0 ≤ (fs M z : ℝ) := (fs M z).coe_nonneg
      constructor <;> linarith [h1 x, h1 y, h2 x, h2 y]⟩
    have hlip : ∃ K, LipschitzWith K (fun x ↦ (fs M x : ℝ)) :=
      ⟨_, lipschitzWith_thickenedIndicator (δ := (1 : ℝ) / (M + 1)) (by positivity) s⟩
    have ev_near : ∀ᶠ i in L,
        (μs i : Measure X).real s ≤ (∫ x, (fs M x : ℝ) ∂(μ : Measure X)) + ε / 2 := by
      refine ((h (fun x ↦ (fs M x : ℝ)) hbd hlip).eventually_lt_const
        (lt_add_of_pos_right _ (half_pos hε))).mono fun i hi ↦ le_trans ?_ hi.le
      have hle := ENNReal.toReal_mono ((fs M).lintegral_lt_top_of_nnreal _).ne
        (measure_le_lintegral_thickenedIndicator (μs i : Measure X) hs.measurableSet
          (by positivity : (0 : ℝ) < 1 / (M + 1)))
      rwa [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral] at hle
    exact (Filter.limsup_le_of_le (isCoboundedUnder_le_of_le L (x := 0) (by simp)) ev_near).trans
      (by linarith [hM M le_rfl])
  have hclosed : ∀ s : Set X, IsClosed s →
      L.limsup (fun i ↦ (μs i : Measure X) s) ≤ (μ : Measure X) s := fun s hs ↦ by
    have hle := ENNReal.ofReal_le_ofReal (hclosed_real s hs)
    simp only [measureReal_def] at hle
    rwa [ENNReal.ofReal_limsup_toReal (C := 1) (Eventually.of_forall fun _ ↦ prob_le_one),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at hle
  have hopen := limsup_measure_closed_le_iff_liminf_measure_open_ge.mp hclosed
  refine tendsto_of_forall_isOpen_le_liminf fun U hU ↦ ENNReal.coe_le_coe.1 ?_
  simpa only [ENNReal.ofNNReal_liminf
    (isBoundedUnder_of ⟨1, fun _ ↦ apply_le_one _ _⟩).isCoboundedUnder_ge,
    ennreal_coeFn_eq_coeFn_toMeasure] using hopen U hU

end MeasureTheory.ProbabilityMeasure
