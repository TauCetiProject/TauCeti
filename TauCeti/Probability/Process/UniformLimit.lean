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

end TauCeti.Probability
