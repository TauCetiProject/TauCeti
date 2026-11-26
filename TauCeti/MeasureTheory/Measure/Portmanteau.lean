/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Support

import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.BumpFunction.DerivativeApproximation
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.MeasureTheory.Measure.SmallPartition

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
* `MeasureTheory.ProbabilityMeasure.tendsto_of_forall_tendsto_integral_contDiff_hasCompactSupport`
  — on a finite-dimensional real normed space, smooth compactly supported test functions determine
  weak convergence of probability measures.
* `ProbabilityMeasure.tendsto_integral_sub_integral_of_forall_contDiff_hasCompactSupport` — on a
  real normed space, if the integrals of two families of probability measures against every smooth
  compactly supported function become asymptotically equal, so do their integrals against every
  continuous compactly supported function.
* `MeasureTheory.ProbabilityMeasure.eventually_measure_pos_of_tendsto_of_mem_support` — along a
  weakly convergent family of probability measures, every neighbourhood of a point of the support
  of the limit eventually has positive mass.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_forall_isOpen_le_liminf_of_filter` — open-set
  portmanteau implication `(O) ⇒ (T)` along an arbitrary filter, without countable generation.
* `MeasureTheory.ProbabilityMeasure.limsup_measureReal_le_of_forall_lipschitz_integral_tendsto` —
  convergence of bounded Lipschitz integrals along an arbitrary filter implies the closed-set
  `limsup` bound `limsup (μs ·).real s ≤ μ.real s`.
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto_of_filter` —
  bounded Lipschitz portmanteau characterization `(T) ⇔ (Lip)` along an arbitrary filter, without
  countable generation.

## Source

* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto_of_filter` is
  adapted from Mathlib's proof of `MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`
  (`Mathlib/MeasureTheory/Measure/Portmanteau.lean`), replacing the countably generated closed-set
  portmanteau step with the arbitrary-filter finite Riemann-sum `(O) ⇒ (T)` argument in
  `MeasureTheory.ProbabilityMeasure.tendsto_of_forall_isOpen_le_liminf_of_filter`.

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
  · exact TauCeti.null_frontier_disjointed hff i
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

/-- Smooth compactly supported test functions control vague convergence of differences: if the
integrals of `μs i` and `νs i` against every smooth compactly supported function become
asymptotically equal, then so do their integrals against every continuous compactly supported
function. No tightness is needed. -/
theorem tendsto_integral_sub_integral_of_forall_contDiff_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {ι : Type*} {l : Filter ι}
    {μs νs : ι → ProbabilityMeasure E}
    (h : ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure E) - ∫ x, f x ∂(νs i : Measure E)) l (𝓝 0))
    {f : E → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun i ↦ ∫ x, f x ∂(μs i : Measure E) - ∫ x, f x ∂(νs i : Measure E)) l (𝓝 0) := by
  -- On an infinite-dimensional space a continuous compactly supported function vanishes.
  rcases hc.eq_zero_or_finiteDimensional ℝ hf with rfl | hE
  · simpa using tendsto_const_nhds
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- A smooth compactly supported `g` with `|g - f| < ε / 4` everywhere.
  obtain ⟨u, K, hK, -, hu, hlim⟩ :=
    (contDiff_zero.2 hf).exists_contDiff_hasCompactSupport_tendstoUniformly_iteratedFDeriv hc
      isOpen_univ (subset_univ _)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.1 (hlim 0 le_rfl) (ε / 4) (by positivity)).exists
  let g := u n
  have hg : ContDiff ℝ ∞ g := (hu n).1
  have hgc : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport _) (hu n).2
  have hgf (x : E) : dist (g x) (f x) < ε / 4 := by
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.dist_map,
      dist_comm (f x)] using hn x
  have hclose (σ : ProbabilityMeasure E) :
      |∫ x, f x ∂(σ : Measure E) - ∫ x, g x ∂(σ : Measure E)| ≤ ε / 4 := by
    rw [← integral_sub (hf.integrable_of_hasCompactSupport hc)
      (hg.continuous.integrable_of_hasCompactSupport hgc), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε / 4) (.of_forall fun x ↦ ?_)).trans ?_
    · rw [← dist_eq_norm, dist_comm]
      exact (hgf x).le
    · simp
  filter_upwards [Metric.tendsto_nhds.1 (h g hg hgc) (ε / 4) (by positivity)] with i hi
  rw [Real.dist_eq, sub_zero] at hi ⊢
  calc |∫ x, f x ∂(μs i : Measure E) - ∫ x, f x ∂(νs i : Measure E)|
      = |(∫ x, g x ∂(μs i : Measure E) - ∫ x, g x ∂(νs i : Measure E)) +
          (∫ x, f x ∂(μs i : Measure E) - ∫ x, g x ∂(μs i : Measure E)) -
          (∫ x, f x ∂(νs i : Measure E) - ∫ x, g x ∂(νs i : Measure E))| := by
        congr 1
        ring
    _ ≤ ε / 4 + ε / 4 + ε / 4 := (abs_sub _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add hi.le (hclose _))) (hclose _))
    _ < ε := by linarith

section Support

variable {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
  [HasOuterApproxClosed Ω] {L : Filter ι} {μs : ι → ProbabilityMeasure Ω}
  {μ : ProbabilityMeasure Ω}

/-- Along a weakly convergent family of probability measures, every neighbourhood of a point of
the support of the limit eventually has positive mass. -/
theorem eventually_measure_pos_of_tendsto_of_mem_support (h : Tendsto μs L (𝓝 μ)) {x : Ω}
    (hx : x ∈ (μ : Measure Ω).support) {U : Set Ω} (hU : U ∈ 𝓝 x) :
    ∀ᶠ i in L, 0 < (μs i : Measure Ω) U := by
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
  have hpos := (Measure.mem_support_iff_forall x).1 hx V (hV.mem_nhds hxV)
  filter_upwards [eventually_lt_of_lt_liminf
    (hpos.trans_le (le_liminf_measure_open_of_tendsto h hV))] with i hi
  exact hi.trans_le (measure_mono hVU)

end Support

end MeasureTheory.ProbabilityMeasure

namespace MeasureTheory.ProbabilityMeasure

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
required. -/
theorem tendsto_of_forall_isOpen_le_liminf_of_filter
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
  set M : ℝ := ‖f‖ + 1 with hM_def
  have hM : 0 < M := by rw [hM_def]; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * M / ε)
  set k : ℕ := m + 1 with hk_def
  have hk_pos : (0 : ℝ) < k := by rw [hk_def]; positivity
  set a : ℝ := M / k with ha_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have ha_lt : a < ε / 2 := by
    rw [ha_def, div_lt_iff₀ hk_pos]
    have hmk : (m : ℝ) < k := by
      rw [hk_def]
      exact_mod_cast Nat.lt_succ_self m
    nlinarith [(div_lt_iff₀ hε).1 hm]
  have hka (x : X) : f x ≤ k * a := by
    rw [ha_def, mul_div_cancel₀ M hk_pos.ne', hM_def]
    linarith [le_trans (le_abs_self _) (f.norm_coe_le_norm x)]
  have hev : ∀ᶠ i in L, ∀ j ∈ Finset.range k,
      (μ : Measure X).real {x | (j : ℝ) * a < f x} - ε / (2 * M) <
        (μs i : Measure X).real {x | (j : ℝ) * a < f x} :=
    (Filter.eventually_all_finset (Finset.range k)).2 fun j _ ↦
      eventually_measureReal_sub_lt_of_le_liminf
        (hopen _ (isOpen_lt continuous_const f.continuous)) (by positivity)
  have hev_int : ∀ᶠ i in L, ∫ x, f x ∂(μ : Measure X) - ε ≤ ∫ x, f x ∂(μs i : Measure X) := by
    filter_upwards [hev] with i hi
    have hμ_le := MeasureTheory.integral_le_mul_sum_measureReal_gt (μ : Measure X)
      (f.integrable _) (ae_of_all _ fun x ↦ hf x) ha (ae_of_all _ hka)
    have hμi_ge := MeasureTheory.mul_sum_measureReal_gt_le_integral_add (μs i : Measure X)
      (f.integrable _) (ae_of_all _ fun x ↦ hf x) k ha
    rw [probReal_univ, mul_one] at hμi_ge
    have hsum : ∑ j ∈ Finset.range k,
        ((μ : Measure X).real {x | (j : ℝ) * a < f x} - ε / (2 * M)) ≤
        ∑ j ∈ Finset.range k, (μs i : Measure X).real {x | (j : ℝ) * a < f x} :=
      Finset.sum_le_sum fun j hj ↦ (hi j hj).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hmul := mul_le_mul_of_nonneg_left hsum ha.le
    have hcancel : a * ((k : ℝ) * (ε / (2 * M))) = ε / 2 := by rw [ha_def]; field_simp
    linarith
  linarith [Filter.le_liminf_of_le hbd_above.isCobounded_ge hev_int]

/-- If the integrals of all bounded Lipschitz functions against `μs` converge to their integrals
against `μ` along a nontrivial filter `L`, then `limsup (μs ·).real s ≤ μ.real s` for every
closed set `s`. -/
theorem limsup_measureReal_le_of_forall_lipschitz_integral_tendsto
    {X ι : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {L : Filter ι} [NeBot L] {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (h : ∀ F : X → ℝ, (∃ M, ∀ x y, dist (F x) (F y) ≤ M) → (∃ K, LipschitzWith K F) →
      Tendsto (fun i ↦ ∫ x, F x ∂(μs i : Measure X)) L (𝓝 (∫ x, F x ∂(μ : Measure X))))
    {s : Set X} (hs : IsClosed s) :
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

/-- **Portmanteau `(T) ⇔ (Lip)` for an arbitrary filter.** Weak convergence of probability measures
along an arbitrary filter `L` on a pseudo-emetric space with opens-measurable structure is
equivalent to convergence of integrals of all bounded Lipschitz functions. Unlike Mathlib's
`MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`, no countable-generation assumption
on `L` is required. -/
theorem tendsto_iff_forall_lipschitz_integral_tendsto_of_filter
    {X ι : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {L : Filter ι} {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X} :
    Tendsto μs L (𝓝 μ) ↔
      ∀ F : X → ℝ, (∃ M, ∀ x y, dist (F x) (F y) ≤ M) → (∃ K, LipschitzWith K F) →
        Tendsto (fun i ↦ ∫ x, F x ∂(μs i : Measure X)) L (𝓝 (∫ x, F x ∂(μ : Measure X))) := by
  constructor
  · intro h F hF_bd hF_lip
    simpa only [BoundedContinuousFunction.coe_mk] using
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h
        ⟨⟨F, hF_lip.choose_spec.continuous⟩, hF_bd⟩
  intro h
  rcases L.eq_or_neBot with rfl | _
  · simp
  have hclosed : ∀ s : Set X, IsClosed s →
      L.limsup (fun i ↦ (μs i : Measure X) s) ≤ (μ : Measure X) s := fun s hs ↦ by
    have hle := ENNReal.ofReal_le_ofReal
      (limsup_measureReal_le_of_forall_lipschitz_integral_tendsto h hs)
    simp only [measureReal_def] at hle
    rwa [ENNReal.ofReal_limsup_toReal (C := 1) (Eventually.of_forall fun _ ↦ prob_le_one),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at hle
  have hopen := limsup_measure_closed_le_iff_liminf_measure_open_ge.mp hclosed
  refine tendsto_of_forall_isOpen_le_liminf_of_filter fun U hU ↦ ENNReal.coe_le_coe.1 ?_
  simpa only [ENNReal.ofNNReal_liminf
    (isBoundedUnder_of ⟨1, fun _ ↦ apply_le_one _ _⟩).isCoboundedUnder_ge,
    ennreal_coeFn_eq_coeFn_toMeasure] using hopen U hU

end MeasureTheory.ProbabilityMeasure
