/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Continuous adapted limits from summable uniform errors

An adapted sequence with almost surely continuous paths has an adapted, almost surely
continuous limit if its successive increments exceed summable deterministic bounds with
summable probabilities on each bounded time interval. Convergence holds uniformly on every
finite horizon outside one common null set. The construction works on the original filtration:
it does not repair paths on a future-measurable exceptional event, which could destroy adaptation.

This is the continuous-process selection step for fast approximations to stochastic integrals.
The error probabilities can be obtained from maximal inequalities. A second theorem identifies
the selected process as a version of any prescribed fixed-time limit in measure. Fixed-time
versions are not asserted to be indistinguishable.

On a finite measure space, a sequence that is uniformly Cauchy in probability on every
finite horizon admits such a fast subsequence. Its selected limit is the uniform-in-probability
limit of the full sequence, and the subsequence converges almost surely uniformly on all
finite horizons. This gives a construction from a Cauchy criterion, without presupposing
fixed-time limits or summable errors for the original approximants.

The proofs use Mathlib's Borel–Cantelli lemma, uniform convergence of telescoping series, and
`StronglyMeasurable.limUnder` for a literally measurable choice at each time.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2, construction of the continuous stochastic integral.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {X : ℕ → ℝ≥0 → Ω → E} {u : ℕ → ℝ}

/-- Select a continuous adapted limit from approximants with summable uniform increment errors.
Only almost-sure continuity is required of each approximant. The conclusion uses one common
full-measure event for continuity and uniform convergence on all finite horizons. Neither usual
filtration conditions nor finiteness of the measure are required. The exceptional events in the
hypothesis are measured by outer measure, so no separate measurability premise is needed. -/
theorem exists_stronglyAdapted_tendstoUniformlyOn_of_summable
    (hX : ∀ n, StronglyAdapted ℱ (X n))
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t ↦ X n t ω)) (hu : Summable u)
    (herr : ∀ T : ℕ, (∑' n, P {ω | ∃ t ≤ (T : ℝ≥0),
      u n < ‖X (n + 1) t ω - X n t ω‖}) ≠ ∞) :
    ∃ Y : ℝ≥0 → Ω → E, StronglyAdapted ℱ Y ∧
      ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) ∧ ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun n t ↦ X n t ω) (fun t ↦ Y t ω) atTop (Iic T) := by
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ limUnder atTop (fun n ↦ X n t ω)
  have hY : StronglyAdapted ℱ Y := by
    intro t
    let : MeasurableSpace Ω := ℱ t
    exact StronglyMeasurable.limUnder (fun n ↦ hX n t)
  have hbound : ∀ᵐ ω ∂P, ∀ T : ℕ, ∀ᶠ n in atTop, ∀ t ≤ (T : ℝ≥0),
      ‖X (n + 1) t ω - X n t ω‖ ≤ u n := by
    refine ae_all_iff.2 fun T ↦ ?_
    filter_upwards [ae_eventually_notMem (herr T)] with ω hω
    exact hω.mono fun n hn t ht ↦ le_of_not_gt fun h ↦ hn ⟨t, ht, h⟩
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hbound, ae_all_iff.2 hc] with ω hω hcω
  have hunif : ∀ T : ℕ, TendstoUniformlyOn (fun n t ↦ X n t ω)
      (fun t ↦ Y t ω) atTop (Iic (T : ℝ≥0)) := by
    intro T
    have hs := tendstoUniformlyOn_tsum_nat_eventually
      (f := fun n t ↦ X (n + 1) t ω - X n t ω) (s := Iic (T : ℝ≥0)) hu (hω T)
    have hconst : TendstoUniformlyOn (fun (_ : ℕ) t ↦ X 0 t ω)
        (fun t ↦ X 0 t ω) atTop (Iic (T : ℝ≥0)) := by
      intro V hV
      exact Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hV
    have ht : TendstoUniformlyOn (fun n t ↦ X n t ω)
        (fun t ↦ (∑' n, (X (n + 1) t ω - X n t ω)) + X 0 t ω)
        atTop (Iic (T : ℝ≥0)) := by
      have htel (n : ℕ) (t : ℝ≥0) :
          ∑ i ∈ Finset.range n, (X (i + 1) t ω - X i t ω) = X n t ω - X 0 t ω :=
        Finset.sum_range_sub (fun i ↦ X i t ω) n
      simpa only [Pi.add_def, htel, sub_add_cancel] using hs.add hconst
    exact ht.congr_right fun t ht' ↦ (ht.tendsto_at ht').limUnder_eq.symm
  have hall : ∀ T : ℝ≥0, TendstoUniformlyOn (fun n t ↦ X n t ω)
      (fun t ↦ Y t ω) atTop (Iic T) := by
    intro T
    obtain ⟨N, hN⟩ := exists_nat_ge T
    exact (hunif N).mono (Iic_subset_Iic.2 hN)
  refine ⟨continuous_iff_continuousAt.2 (fun t ↦ ?_), hall⟩
  obtain ⟨N, hN⟩ := exists_nat_gt t
  exact ((hunif N).continuousOn (Frequently.of_forall fun n ↦
    (hcω n).continuousOn) t hN.le).continuousAt (Iic_mem_nhds hN)

/-- A prescribed fixed-time limit in measure has an adapted, almost surely continuous version
when its continuous adapted approximants have summable uniform increment errors. The selected
version is also their almost surely uniform limit on every finite horizon. No finiteness of the
measure, completeness of the filtration, or path regularity of the prescribed limit is assumed. -/
theorem exists_continuous_stronglyAdapted_version_of_summable
    {Z : ℝ≥0 → Ω → E} (hX : ∀ n, StronglyAdapted ℱ (X n))
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t ↦ X n t ω)) (hu : Summable u)
    (herr : ∀ T : ℕ, (∑' n, P {ω | ∃ t ≤ (T : ℝ≥0),
      u n < ‖X (n + 1) t ω - X n t ω‖}) ≠ ∞)
    (hZ : ∀ t, TendstoInMeasure P (fun n ↦ X n t) atTop (Z t)) :
    ∃ Y : ℝ≥0 → Ω → E, StronglyAdapted ℱ Y ∧ (∀ t, Y t =ᵐ[P] Z t) ∧
      ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) ∧ ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun n t ↦ X n t ω) (fun t ↦ Y t ω) atTop (Iic T) := by
  obtain ⟨Y, hY, hlim⟩ :=
    exists_stronglyAdapted_tendstoUniformlyOn_of_summable hX hc hu herr
  refine ⟨Y, hY, fun t ↦ ?_, hlim⟩
  obtain ⟨ns, hns, hsub⟩ := (hZ t).exists_seq_tendsto_ae
  filter_upwards [hlim, hsub] with ω hω hsubω
  exact tendsto_nhds_unique (((hω.2 t).tendsto_at le_rfl).comp hns.tendsto_atTop) hsubω

omit [CompleteSpace E] in
/-- A uniformly Cauchy sequence in probability converges uniformly in probability to any
almost surely pointwise subsequential limit on the same horizon. -/
private lemma tendsto_uniformlyInMeasure_of_cauchy_of_subseq_tendsto_ae
    {Y : ℝ≥0 → Ω → E} {ns : ℕ → ℕ} {T : ℝ≥0}
    (hC : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
        P {ω | ∃ t ≤ T, ε < ‖X n t ω - X m t ω‖} ≤ δ)
    (hns : Tendsto ns atTop atTop)
    (hlim : ∀ᵐ ω ∂P, ∀ t ≤ T,
      Tendsto (fun k ↦ X (ns k) t ω) atTop (𝓝 (Y t ω)))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ∃ t ≤ T, ε < ‖X n t ω - Y t ω‖}) atTop (𝓝 0) := by
  -- Pass the Cauchy bound to the limit using continuity from below of outer measure.
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  obtain ⟨K, hK⟩ := hC (ε / 2) (by positivity) δ hδ
  refine ⟨K, fun n hn ↦ ?_⟩
  let A (k : ℕ) := {ω | ∃ t ≤ T, ε / 2 < ‖X n t ω - X (ns k) t ω‖}
  let B (j : ℕ) := ⋂ k ≥ j, A k
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hns.eventually_ge_atTop K)
  have hB : ∀ j, P (B j) ≤ δ := by
    intro j
    exact (measure_mono (iInter_subset_of_subset (max j J)
      (iInter_subset_of_subset (le_max_left _ _) Subset.rfl))).trans
      (hK n hn (ns (max j J)) (hJ _ (le_max_right _ _)))
  have hmono : Monotone B := by
    intro i j hij ω hω
    exact mem_iInter₂.mpr fun k hk ↦ mem_iInter₂.mp hω k (hij.trans hk)
  have hsub : {ω | ∃ t ≤ T, ε < ‖X n t ω - Y t ω‖} ≤ᵐ[P] ⋃ j, B j := by
    filter_upwards [hlim] with ω hω hbad
    obtain ⟨t, ht, herr⟩ := hbad
    have hp := hω t ht
    have he : ∀ᶠ k in atTop, ε / 2 < ‖X n t ω - X (ns k) t ω‖ :=
      ((tendsto_const_nhds.sub hp).norm).eventually
        (lt_mem_nhds (by linarith : ε / 2 < ‖X n t ω - Y t ω‖))
    obtain ⟨j, hj⟩ := eventually_atTop.1 he
    exact mem_iUnion.mpr ⟨j, mem_iInter₂.mpr fun k hk ↦ ⟨t, ht, hj k hk⟩⟩
  exact (measure_mono_ae hsub).trans (by rw [hmono.measure_iUnion]; exact iSup_le hB)

/-- A continuous adapted sequence uniformly Cauchy in probability on each bounded horizon has
an adapted, almost surely continuous limit. The entire sequence converges uniformly in
probability; one strictly increasing subsequence converges almost surely uniformly on every
finite horizon. The filtration need not be complete or right-continuous. Error events are
measured by outer measure, so no separate measurability of path suprema is required. -/
theorem exists_stronglyAdapted_tendsto_uniformlyInMeasure_of_cauchy [IsFiniteMeasure P]
    (hX : ∀ n, StronglyAdapted ℱ (X n))
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t ↦ X n t ω))
    (hC : ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε → ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
        P {ω | ∃ t ≤ T, ε < ‖X n t ω - X m t ω‖} ≤ δ) :
    ∃ Y : ℝ≥0 → Ω → E, StronglyAdapted ℱ Y ∧
      (∀ (T : ℝ≥0) (ε : ℝ), 0 < ε →
        Tendsto (fun n ↦ P {ω | ∃ t ≤ T, ε < ‖X n t ω - Y t ω‖}) atTop (𝓝 0)) ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) ∧ ∀ T : ℝ≥0,
          TendstoUniformlyOn (fun k t ↦ X (ns k) t ω) (fun t ↦ Y t ω) atTop (Iic T) := by
  -- Diagonalize both horizons and error sizes, then make the selected indices increasing.
  have hr : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) := summable_geometric_two
  have hex (k : ℕ) := hC k ((1 / 2 : ℝ) ^ k) (by positivity)
    (ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) (by positivity)
  choose N hN using hex
  obtain ⟨ns, hns, hnsN⟩ := Filter.extraction_forall_of_eventually'
    (P := fun k n ↦ N k ≤ n) fun k ↦ ⟨N k, fun _ h ↦ h⟩
  have herr (T : ℕ) : (∑' k, P {ω | ∃ t ≤ (T : ℝ≥0),
      (1 / 2 : ℝ) ^ k < ‖X (ns (k + 1)) t ω - X (ns k) t ω‖}) ≠ ∞ := by
    let e (k : ℕ) := P {ω | ∃ t ≤ (T : ℝ≥0),
      (1 / 2 : ℝ) ^ k < ‖X (ns (k + 1)) t ω - X (ns k) t ω‖}
    have he : ∀ᶠ k in atTop, e k ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      filter_upwards [eventually_ge_atTop T] with k hk
      have hsub : {ω | ∃ t ≤ (T : ℝ≥0),
          (1 / 2 : ℝ) ^ k < ‖X (ns (k + 1)) t ω - X (ns k) t ω‖} ⊆
          {ω | ∃ t ≤ (k : ℝ≥0),
            (1 / 2 : ℝ) ^ k < ‖X (ns (k + 1)) t ω - X (ns k) t ω‖} := by
        rintro ω ⟨t, ht, he⟩
        exact ⟨t, ht.trans (by exact_mod_cast hk), he⟩
      exact (measure_mono hsub).trans
        (hN k (ns (k + 1)) ((hnsN k).trans (hns.monotone k.le_succ)) (ns k) (hnsN k))
    have hs : Summable (fun k ↦ (e k).toReal) :=
      hr.of_norm_bounded_eventually_nat (he.mono fun k hk ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ k)] using
          ENNReal.toReal_mono (by finiteness) hk)
    simpa only [e, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hs.tsum_ofReal_ne_top
  obtain ⟨Y, hY, hlim⟩ := exists_stronglyAdapted_tendstoUniformlyOn_of_summable
    (fun k ↦ hX (ns k)) (fun k ↦ hc (ns k)) hr herr
  refine ⟨Y, hY, ?_, ns, hns, hlim⟩
  intro T ε hε
  exact tendsto_uniformlyInMeasure_of_cauchy_of_subseq_tendsto_ae (hC T)
    hns.tendsto_atTop (hlim.mono fun ω hω t ht ↦ (hω.2 T).tendsto_at ht) ε hε

end TauCeti.Probability
