/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.Martingale.WithDensity
public import TauCeti.Probability.Martingale.ContinuousStopping
public import TauCeti.Probability.Process.Predictable.Basic

/-!
# Density-weighted local martingales

Let `Q = P.withDensity w` be equivalent to the finite measure `P`, and let `Z` be a
strongly progressive, almost surely right-continuous version of the conditional density.
If `X` is a native `Q`-local martingale with almost surely continuous paths, then `Z • X`
is a native `P`-local martingale. This is the local form of the density-product
transformation used in changing martingale representations between equivalent measures.

Neither the initial value nor the original process is assumed integrable or literally
adapted. The conclusion uses actual stopping times on the original raw filtration and
retains the native indicator at time zero. No usual conditions, density bounds or reciprocal
moments are required. Only the forward density-product implication is proved here.

For each original localized martingale, choose a predictable indistinguishable version,
weight it by `Z`, and stop again at the original localizer. This second stopping is essential:
the native stopped product contains the stopped density, not the unstopped density.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5 and Chapter 3, §5.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace ProbabilityTheory.Locally

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {w : Ω → ℝ≥0∞} [IsFiniteMeasure (P.withDensity w)]
  {X : ℝ≥0 → Ω → E} {Z : ℝ≥0 → Ω → ℝ}

-- The stage of the weighted process uses the stopped density. Select a progressive version
-- before the second stopping, but retain the original native stage in the conclusion.
private theorem martingale_density_native_stage {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ)
    (hU : Martingale (stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ)
      ℱ (P.withDensity w))
    (hcU : ∀ᵐ ω ∂P.withDensity w,
      Continuous (stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ · ω))
    (hw : AEMeasurable w P) (hPQ : P ≪ P.withDensity w)
    (hZ : IsStronglyProgressive ℱ Z) (hcZ : ∀ᵐ ω ∂P, IsRightContinuous (Z · ω))
    (hZeq : ∀ t, Z t =ᵐ[P] P[fun ω ↦ (w ω).toReal | ℱ t]) :
    Martingale (stoppedProcess
      (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ Z t ω • X t ω)) τ) ℱ P := by
  classical
  let U := stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ
  have hUM : Martingale U ℱ (P.withDensity w) := hU
  obtain ⟨Y, hY, heq⟩ :=
    hUM.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
      (hcU.mono fun _ h ↦ h.isLeftContinuous)
  have hcY : ∀ᵐ ω ∂P, Continuous (Y · ω) := by
    filter_upwards [hPQ.ae_le hcU, hPQ.ae_le heq] with ω hc heqω
    simpa only [heqω] using hc
  have hYM : Martingale Y ℱ (P.withDensity w) :=
    hUM.congr hY.stronglyAdapted (fun t ↦ heq.mono fun _ h ↦ (h t).symm)
  have hweighted : Martingale (fun t ω ↦ Z t ω • Y t ω) ℱ P :=
    (hY.stronglyAdapted.martingale_withDensity_iff_of_ae_eq_condExp hw hYM.integrable
      hZ.stronglyAdapted hZeq).mp hYM
  have hprog : IsStronglyProgressive ℱ (fun t ω ↦ Z t ω • Y t ω) :=
    fun t ↦ (hZ t).smul (hY.isStronglyProgressive t)
  have hright : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ Z t ω • Y t ω) := by
    filter_upwards [hcZ, hcY] with ω hz hy t
    exact (hz t).smul hy.continuousWithinAt
  have hstop := hweighted.stoppedProcess_of_ae_isRightContinuous hprog hright hτ
  have hfactor :
      stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ Z t ω • X t ω)) τ =
        fun t ω ↦ stoppedProcess Z τ t ω • U t ω := by
    ext t ω
    simp [U, stoppedProcess, Set.indicator_apply]
  rw [hfactor]
  refine hstop.congr (fun t ↦ ((hZ.stoppedProcess hτ).stronglyAdapted t).smul
    (hUM.stronglyAdapted t)) (fun t ↦ ?_)
  filter_upwards [hPQ.ae_le heq] with ω hω
  calc
    stoppedProcess (fun t ω ↦ Z t ω • Y t ω) τ t ω =
        stoppedProcess Z τ t ω • stoppedProcess Y τ t ω := rfl
    _ = stoppedProcess Z τ t ω • stoppedProcess U τ t ω := by
      exact congrArg (stoppedProcess Z τ t ω • ·) (hω _)
    _ = stoppedProcess Z τ t ω • U t ω := by
      simp only [U, stoppedProcess_stoppedProcess, inf_idem]

/-- Weighting a continuous local martingale under an equivalent finite density change by a
progressive right-continuous conditional-density version gives a local martingale under the
original measure. Literal adaptation and integrability of `X` itself are not required.
The conditional-density identities are only fixed-time almost-sure identities. -/
theorem smul_of_withDensity
    (hX : Locally (fun Y ↦ Martingale Y ℱ (P.withDensity w)) ℱ X (P.withDensity w))
    (hcX : ∀ᵐ ω ∂P.withDensity w, Continuous (X · ω))
    (hw : AEMeasurable w P) (hPQ : P ≪ P.withDensity w)
    (hZ : IsStronglyProgressive ℱ Z)
    (hcZ : ∀ᵐ ω ∂P, IsRightContinuous (Z · ω))
    (hZeq : ∀ t, Z t =ᵐ[P] P[fun ω ↦ (w ω).toReal | ℱ t]) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ Z t ω • X t ω) P := by
  classical
  obtain ⟨τ, hτ, hmart⟩ := hX
  have hτP : IsLocalizingSequence ℱ τ P :=
    { isStoppingTime := hτ.isStoppingTime
      mono := hPQ.ae_le hτ.mono
      tendsto_top := hPQ.ae_le hτ.tendsto_top }
  refine ⟨τ, hτP, fun n ↦ martingale_density_native_stage (hτ.isStoppingTime n)
    (hmart n) ?_ hw hPQ hZ hcZ hZeq⟩
  filter_upwards [hcX] with ω hω
  by_cases hp : ⊥ < τ n ω
  · simp only [stoppedProcess_indicator_comm', Set.indicator_apply, mem_ofPred_eq,
      hp, ite_true]
    cases ht : τ n ω using WithTop.recTopCoe with
    | top =>
      simpa only [stoppedProcess, ht, min_eq_left le_top,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using hω
    | coe u =>
      simpa only [stoppedProcess, ht, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe,
        Function.comp_def, id_eq] using hω.comp (continuous_id.min (continuous_const (y := u)))
  · simpa only [stoppedProcess_indicator_comm', Set.indicator_apply, mem_ofPred_eq,
      hp, ite_false] using (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : E)))

end ProbabilityTheory.Locally
