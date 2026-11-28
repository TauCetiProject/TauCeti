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
import TauCeti.MeasureTheory.Function.UniformConvergence

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
fixed-time limits or summable errors for the original approximants. A fixed-horizon version
(`exists_tendsto_uniformlyInMeasure_Iic_of_cauchy`) requires neither adaptedness nor finiteness
of the measure, only almost-sure continuity and a uniform Cauchy bound on `[0, T]`.

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
  have hunif : ∀ᵐ ω ∂P, ∀ T : ℕ, ContinuousOn (fun t ↦ Y t ω) (Iic (T : ℝ≥0)) ∧
      TendstoUniformlyOn (fun n t ↦ X n t ω) (fun t ↦ Y t ω) atTop (Iic (T : ℝ≥0)) :=
    ae_all_iff.2 fun T ↦
      TauCeti.MeasureTheory.ae_continuousOn_and_tendstoUniformlyOn_limUnder_of_summable
        (fun n ↦ (hc n).mono fun ω hω ↦ hω.continuousOn) hu (herr T)
  refine ⟨Y, hY, hunif.mono fun ω hω ↦ ⟨continuous_iff_continuousAt.2 fun t ↦ ?_, fun T ↦ ?_⟩⟩
  · obtain ⟨N, hN⟩ := exists_nat_gt t
    exact (hω N).1.continuousAt (Iic_mem_nhds hN)
  · obtain ⟨N, hN⟩ := exists_nat_ge T
    exact (hω N).2.mono (Iic_subset_Iic.2 hN)

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
/-- A filter-indexed process family uniformly close in probability to a reference sequence
converges uniformly in probability on the same horizon to any almost surely pointwise
subsequential limit of the reference sequence. -/
theorem tendsto_uniformlyInMeasure_of_subseq_tendsto_ae
    {ι : Type*} {l : Filter ι} {Z : ι → ℝ≥0 → Ω → E}
    {Y : ℝ≥0 → Ω → E} {ns : ℕ → ℕ} {T : ℝ≥0} {ε : ℝ}
    (hC : ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ i in l, ∀ᶠ m in atTop,
      P {ω | ∃ t ≤ T, ε / 2 < ‖Z i t ω - X m t ω‖} ≤ δ)
    (hns : Tendsto ns atTop atTop)
    (hlim : ∀ᵐ ω ∂P, ∀ t ≤ T,
      Tendsto (fun k ↦ X (ns k) t ω) atTop (𝓝 (Y t ω))) :
    Tendsto (fun i ↦ P {ω | ∃ t ≤ T, ε < ‖Z i t ω - Y t ω‖}) l (𝓝 0) := by
  -- Pass the uniform comparison to the limit using continuity from below of outer measure.
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  filter_upwards [hC δ hδ] with i hi
  obtain ⟨K, hK⟩ := eventually_atTop.1 hi
  let A (k : ℕ) := {ω | ∃ t ≤ T, ε / 2 < ‖Z i t ω - X (ns k) t ω‖}
  let B (j : ℕ) := ⋂ k ≥ j, A k
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hns.eventually_ge_atTop K)
  have hB : ∀ j, P (B j) ≤ δ := fun j ↦
    (measure_mono (iInter_subset_of_subset (max j J)
      (iInter_subset_of_subset (le_max_left _ _) Subset.rfl))).trans
      (hK (ns (max j J)) (hJ _ (le_max_right _ _)))
  have hmono : Monotone B := fun a b hab ω hω ↦
    mem_iInter₂.mpr fun k hk ↦ mem_iInter₂.mp hω k (hab.trans hk)
  have hsub : {ω | ∃ t ≤ T, ε < ‖Z i t ω - Y t ω‖} ≤ᵐ[P] ⋃ j, B j := by
    filter_upwards [hlim] with ω hω ⟨t, ht, herr⟩
    have he : ∀ᶠ k in atTop, ε / 2 < ‖Z i t ω - X (ns k) t ω‖ :=
      ((tendsto_const_nhds.sub (hω t ht)).norm).eventually
        (lt_mem_nhds (by linarith [norm_nonneg (Z i t ω - Y t ω)] :
          ε / 2 < ‖Z i t ω - Y t ω‖))
    obtain ⟨j, hj⟩ := eventually_atTop.1 he
    exact mem_iUnion.mpr ⟨j, mem_iInter₂.mpr fun k hk ↦ ⟨t, ht, hj k hk⟩⟩
  exact (measure_mono_ae hsub).trans (by rw [hmono.measure_iUnion]; exact iSup_le hB)

omit [CompleteSpace E] in
/-- Extract a strictly increasing subsequence whose successive increments exceed `(1 / 2) ^ k`
on `Iic (R k)` with outer probability at most `(1 / 2) ^ k`. -/
private lemma exists_strictMono_cauchy_subseq (R : ℕ → ℝ≥0)
    (hR : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      P {ω | ∃ t ≤ R k, (1 / 2 : ℝ) ^ k < ‖X n t ω - X m t ω‖} ≤ (1 / 2 : ℝ≥0∞) ^ k) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ k : ℕ,
      P {ω | ∃ t ≤ R k, (1 / 2 : ℝ) ^ k < ‖X (ns (k + 1)) t ω - X (ns k) t ω‖} ≤
        (1 / 2 : ℝ≥0∞) ^ k := by
  choose N hN using hR
  obtain ⟨ns, hns, hnsN⟩ := Filter.extraction_forall_of_eventually'
    (P := fun k n ↦ N k ≤ n) fun k ↦ ⟨N k, fun _ h ↦ h⟩
  exact ⟨ns, hns, fun k ↦ hN k (ns (k + 1)) ((hnsN k).trans (hns.monotone k.le_succ))
    (ns k) (hnsN k)⟩

omit [CompleteSpace E] in
/-- Upgrade a Cauchy condition on `Iic T` and a.e. uniform convergence of a subsequence on
`Iic T` to uniform convergence in outer probability of the full sequence on `Iic T`. -/
private lemma tendsto_uniformlyInMeasure_of_cauchy_of_tendstoUniformlyOn
    {Y : ℝ≥0 → Ω → E} {ns : ℕ → ℕ} {T : ℝ≥0}
    (hC : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
        P {ω | ∃ t ≤ T, ε < ‖X n t ω - X m t ω‖} ≤ δ)
    (hns : StrictMono ns)
    (hlim : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun k t ↦ X (ns k) t ω) (fun t ↦ Y t ω) atTop (Iic T))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ∃ t ≤ T, ε < ‖X n t ω - Y t ω‖}) atTop (𝓝 0) :=
  tendsto_uniformlyInMeasure_of_subseq_tendsto_ae
    (fun δ hδ ↦ let ⟨N, hN⟩ := hC (ε / 2) (half_pos hε) δ hδ
      eventually_atTop.2 ⟨N, fun n hn ↦ eventually_atTop.2 ⟨N, fun m hm ↦ hN n hn m hm⟩⟩)
    hns.tendsto_atTop (hlim.mono fun _ hω _ ht ↦ hω.tendsto_at ht)

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
  obtain ⟨ns, hns, hns_le⟩ := exists_strictMono_cauchy_subseq (X := X) (P := P) Nat.cast
    fun k ↦ hC k ((1 / 2 : ℝ) ^ k) (by positivity)
      ((1 / 2 : ℝ≥0∞) ^ k) (ENNReal.pow_pos (by norm_num) k)
  have herr (T : ℕ) : (∑' k, P {ω | ∃ t ≤ (T : ℝ≥0),
      (1 / 2 : ℝ) ^ k < ‖X (ns (k + 1)) t ω - X (ns k) t ω‖}) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum (g := fun k ↦
        (if k < T then P univ else 0) + (1 / 2 : ℝ≥0∞) ^ k) fun k ↦ ?_)
    · rw [CompleteLattice.summable.tsum_add CompleteLattice.summable,
        tsum_eq_sum (s := Finset.range T) (fun k hk ↦ ite_eq_right (by simpa using hk)),
        ENNReal.tsum_geometric]
      exact ENNReal.add_ne_top.2
        ⟨ENNReal.sum_ne_top.2 fun _ _ ↦ by split_ifs <;> simp, by norm_num⟩
    · by_cases hk : k < T
      · simp only [hk, ↓reduceIte]
        exact (measure_mono (subset_univ _)).trans le_self_add
      · simp only [hk, ↓reduceIte, zero_add]
        refine (measure_mono ?_).trans (hns_le k)
        rintro ω ⟨t, ht, he⟩
        exact ⟨t, ht.trans (by exact_mod_cast not_lt.1 hk), he⟩
  obtain ⟨Y, hY, hlim⟩ := exists_stronglyAdapted_tendstoUniformlyOn_of_summable
    (fun k ↦ hX (ns k)) (fun k ↦ hc (ns k)) summable_geometric_two herr
  refine ⟨Y, hY, fun T ε hε ↦ ?_, ns, hns, hlim⟩
  exact tendsto_uniformlyInMeasure_of_cauchy_of_tendstoUniformlyOn (hC T) hns
    (hlim.mono fun _ hω ↦ hω.2 T) hε

/-- A process sequence that is almost surely continuous on `[0, T]` and uniformly Cauchy in outer
probability on `[0, T]` has a limit process which is almost surely continuous on `[0, T]`: the
entire sequence converges uniformly in outer probability on `[0, T]`, and a strictly increasing
subsequence converges almost surely uniformly on `[0, T]`. Neither finiteness of the measure nor
adaptedness is required. -/
theorem exists_tendsto_uniformlyInMeasure_Iic_of_cauchy {T : ℝ≥0}
    (hc : ∀ n, ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ X n t ω) (Iic T))
    (hC : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
        P {ω | ∃ t ≤ T, ε < ‖X n t ω - X m t ω‖} ≤ δ) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n ↦ P {ω | ∃ t ≤ T, ε < ‖X n t ω - Y t ω‖}) atTop (𝓝 0)) ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ Y t ω) (Iic T) ∧
          TendstoUniformlyOn (fun k t ↦ X (ns k) t ω) (fun t ↦ Y t ω) atTop (Iic T) := by
  obtain ⟨ns, hns, hns_le⟩ := exists_strictMono_cauchy_subseq (X := X) (P := P) (fun _ ↦ T)
    fun k ↦ hC ((1 / 2 : ℝ) ^ k) (by positivity)
      ((1 / 2 : ℝ≥0∞) ^ k) (ENNReal.pow_pos (by norm_num) k)
  have htsum : (∑' k : ℕ, P {ω | ∃ t ≤ T,
      (1 / 2 : ℝ) ^ k < ‖X (ns (k + 1)) t ω - X (ns k) t ω‖}) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [ENNReal.tsum_geometric]; norm_num) (tsum_le_tsum hns_le)
  have hlim := TauCeti.MeasureTheory.ae_continuousOn_and_tendstoUniformlyOn_limUnder_of_summable
    (fun k ↦ hc (ns k)) summable_geometric_two htsum
  exact ⟨_, fun ε hε ↦ tendsto_uniformlyInMeasure_of_cauchy_of_tendstoUniformlyOn hC hns
    (hlim.mono fun _ hω ↦ hω.2) hε, ns, hns, hlim⟩

end TauCeti.Probability
