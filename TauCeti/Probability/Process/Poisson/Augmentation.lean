/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Poisson.Filtered
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.HasLaw
import TauCeti.Probability.Independence.Completion
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Process.Filtration.Natural

/-!
# Augmentation and right-continuity for filtered Poisson processes

For any homogeneous Poisson process `N` of rate `α` relative to a filtration `ℱ`, the probability
that `N` changes across `[s, u]` is `1 - exp (-α * (u - s)) ≤ α * (u - s)`. Along any sequence
`u n ≥ s` with summable gaps `u n - s`, Borel–Cantelli shows that `N (u n) = N s` eventually almost
surely, without any pathwise regularity assumption on the given version `N`.

Consequently:
* `N` remains a filtered Poisson process on `ℱ.rightCont`, on `ℱ.nullAugment P` (under
  `P.completion`), and hence on `(ℱ.ambientNullAugmentation P).rightCont` and
  `(ℱ.nullAugment P).rightCont`, with no path-continuity hypothesis;
* for any filtration `ℱ`, the entire future increment process `(N (s + v) - N s)_v` is independent
  of `ℱ.rightCont s` (`indep_comap_shift_rightCont`);
* both `(Filtration.natural N hmeas).ambientNullAugmentation P` and
  `(Filtration.natural N hmeas).nullAugment P` are already right-continuous.

See also the analogous Brownian results in `TauCeti.Probability.BrownianMotion.UsualFiltration`
(`TauCeti.Probability.IsFilteredPreBrownianReal.rightCont`, `nullAugment`) and
`TauCeti.Probability.BrownianMotion.RightContinuity`
(`ProbabilityTheory.IsBrownianReal.indep_shift_rightCont_natural`,
`rightCont_natural_le_nullAugment`, `isRightContinuous_nullAugment_natural`).

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3, and §4, Theorem 31.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition, Springer,
  1991, §2.7.A.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {α : ℝ≥0} {N : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- Along any sequence of times `u n ≥ s` with summable gaps `u n - s`, a filtered Poisson process
eventually equals `N s` almost surely. No path regularity is assumed. -/
theorem ae_eventually_eval_eq_of_tsum_sub_ne_top (h : IsFilteredPoissonProcess ℱ α N P)
    {s : ℝ≥0} {u : ℕ → ℝ≥0} (hsu : ∀ n, s ≤ u n)
    (hsum : (∑' n, ((u n - s : ℝ≥0) : ℝ≥0∞)) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, N (u n) ω = N s ω := by
  have hle : (∑' n, P {ω | N (u n) ω ≠ N s ω}) ≤
      (α : ℝ≥0∞) * ∑' n, ((u n - s : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun n ↦ h.measure_eval_ne_le (hsu n)
  have hfin : (∑' n, P {ω | N (u n) ω ≠ N s ω}) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hsum) hle
  filter_upwards [MeasureTheory.ae_eventually_notMem hfin] with ω hω
  exact hω.mono fun _ hn ↦ not_ne_iff.mp hn

/-- Along any sequence of times `u n ≥ s` with geometric gaps `u n - s ≤ 2⁻ⁿ`, a filtered Poisson
process eventually equals `N s` almost surely. -/
theorem ae_eventually_eval_eq_of_sub_le_two_inv_pow (h : IsFilteredPoissonProcess ℱ α N P)
    {s : ℝ≥0} {u : ℕ → ℝ≥0} (hsu : ∀ n, s ≤ u n)
    (hle : ∀ n, u n - s ≤ (2⁻¹ : ℝ≥0) ^ n) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, N (u n) ω = N s ω := by
  refine h.ae_eventually_eval_eq_of_tsum_sub_ne_top hsu
    (ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ?_)
  rw [← ENNReal.tsum_geometric_two]
  refine tsum_le_tsum fun n ↦ (ENNReal.coe_le_coe.mpr (hle n)).trans_eq ?_
  rw [ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]

/-- At every fixed time `s`, `N (s + 2⁻ⁿ)` eventually equals `N s` almost surely. -/
theorem ae_eventually_eval_add_two_inv_pow_eq (h : IsFilteredPoissonProcess ℱ α N P) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, N (s + (2⁻¹ : ℝ≥0) ^ n) ω = N s ω :=
  h.ae_eventually_eval_eq_of_sub_le_two_inv_pow (fun _ ↦ le_self_add)
    fun _ ↦ (add_tsub_cancel_left _ _).le

/-- Every filtered Poisson process remains a filtered Poisson process on the right-continuation of
its filtration. No pathwise right-continuity hypothesis is needed. -/
theorem rightCont (h : IsFilteredPoissonProcess ℱ α N P) :
    IsFilteredPoissonProcess ℱ.rightCont α N P where
  stronglyAdapted t := (h.stronglyAdapted t).mono (ℱ.le_rightCont t)
  eval_zero_ae_eq_zero := h.eval_zero_ae_eq_zero
  hasLaw_sub := h.hasLaw_sub
  indep_sub s t hst := by
    have := h.isProbabilityMeasure
    refine h.adapted.indep_comap_sub_rightCont h.indep_sub hst
      ⟨fun n ↦ s + (2⁻¹ : ℝ≥0) ^ n, fun _ ↦ lt_add_of_pos_right s (by positivity), ?_, ?_⟩
    · have hpow : Tendsto (fun n : ℕ ↦ (2⁻¹ : ℝ≥0) ^ n) atTop (𝓝 0) :=
        NNReal.tendsto_coe.mp <| by
          simpa using tendsto_pow_atTop_nhds_zero_of_lt_one
            (by positivity : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹ : ℝ) < 1)
      simpa using tendsto_const_nhds.add hpow
    · filter_upwards [h.ae_eventually_eval_add_two_inv_pow_eq s] with ω hω
      exact tendsto_const_nhds.congr' (hω.mono fun _ hn ↦ hn.symm)

/-- Completing the ambient probability space and adjoining all ambient null events to the
filtration preserves the filtered Poisson property. -/
theorem nullAugment (h : IsFilteredPoissonProcess ℱ α N P) :
    IsFilteredPoissonProcess (ℱ.nullAugment P) α
      (fun t (ω : NullMeasurableSpace Ω P) ↦ N t ω) P.completion where
  -- The carrier tag `NullMeasurableSpace Ω P` changes only the ambient measurable-space instance,
  -- not `N t`; `StronglyMeasurable` names its σ-algebra explicitly, so `mono` transports it along
  -- `le_nullAugment` directly.
  stronglyAdapted t := (h.stronglyAdapted t).mono (ℱ.le_nullAugment P t)
  eval_zero_ae_eq_zero := P.ae_completion.symm ▸ h.eval_zero_ae_eq_zero
  hasLaw_sub _ _ hst := (h.hasLaw_sub hst).completion
  indep_sub _ _ hst := (h.indep_sub hst).nullAugment_right

/-- The entire future increment process `(N (s + v) - N s)_v` of a filtered Poisson process is
independent of the right-continuous past `ℱ.rightCont s`. -/
theorem indep_comap_shift_rightCont (h : IsFilteredPoissonProcess ℱ α N P) (s : ℝ≥0) :
    Indep (.comap (fun ω v ↦ N (s + v) ω - N s ω) inferInstance) (ℱ.rightCont s) P :=
  h.rightCont.indep_comap_shift s

/-- Every event of the raw right-continuous natural filtration of a Poisson process agrees almost
everywhere with an event of the natural filtration at the same time. -/
theorem rightCont_natural_le_nullAugment (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) (s : ℝ≥0) :
    (Filtration.natural N hmeas).rightCont s ≤ (Filtration.natural N hmeas).nullAugment P s := by
  have := h.isProbabilityMeasure
  exact Filtration.rightCont_natural_le_nullAugment_of_indep_shift hmeas
    ((h.natural hmeas).indep_comap_shift_rightCont s)

/-- The raw right-continuous natural filtration of a Poisson process is contained in its
original-space null augmentation. -/
theorem rightCont_natural_le_ambientNullAugmentation (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) :
    (Filtration.natural N hmeas).rightCont ≤
      (Filtration.natural N hmeas).ambientNullAugmentation P :=
  Filtration.rightCont_le_ambientNullAugmentation_of_rightCont_le_nullAugment
    (h.rightCont_natural_le_nullAugment hmeas)

/-- The original-space null augmentation of the natural filtration of a Poisson process is
right-continuous. -/
theorem isRightContinuous_ambientNullAugmentation_natural (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) :
    ((Filtration.natural N hmeas).ambientNullAugmentation P).IsRightContinuous :=
  Filtration.isRightContinuous_ambientNullAugmentation_of_rightCont_le_nullAugment
    (h.rightCont_natural_le_nullAugment hmeas)

/-- The completed null augmentation of the natural filtration of a Poisson process is
right-continuous, without assuming completeness of the original probability space. -/
theorem isRightContinuous_nullAugment_natural (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) :
    ((Filtration.natural N hmeas).nullAugment P).IsRightContinuous :=
  Filtration.isRightContinuous_nullAugment_of_rightCont_le_nullAugment
    (h.rightCont_natural_le_nullAugment hmeas)

end TauCeti.Probability.IsFilteredPoissonProcess
