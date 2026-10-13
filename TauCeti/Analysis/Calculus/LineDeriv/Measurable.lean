/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Measurability of almost-everywhere line derivatives

Let `u : E → F` be a.e.-strongly measurable on an open set `s`, and suppose that at almost every
`x ∈ s` it has a line derivative `u' x` in a fixed direction `v`. Then `u'` is a.e.-strongly
measurable on `s` (`TauCeti.aestronglyMeasurable_of_ae_hasLineDerivAt`), being the
almost-everywhere limit of the difference quotients `t⁻¹ • (u (x + t • v) - u x)`. If `u` is
moreover locally Lipschitz on `s`, then `u'` is essentially locally bounded there (near each point
it is bounded almost everywhere by `C * ‖v‖` for a local Lipschitz constant `C`), hence locally
integrable (`LocallyLipschitzOn.locallyIntegrableOn_of_ae_hasLineDerivAt`).

Mathlib's `aestronglyMeasurable_lineDeriv` covers `lineDeriv` of a globally continuous function.
The results here only ask for measurability on `s` and for a line derivative almost everywhere, with
an arbitrary candidate `u'`; this is the form in which a.e. derivatives of locally Lipschitz
functions (Rademacher's theorem) enter the theory of weak derivatives.
-/

public section

open MeasureTheory Metric Set Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure E} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {v : E} {u u' : E → F}

namespace TauCeti

/-- An almost-everywhere line derivative of a function a.e.-strongly measurable on an open set `s`
is a.e.-strongly measurable on `s`: it is the almost-everywhere limit of difference quotients. -/
theorem aestronglyMeasurable_of_ae_hasLineDerivAt
    [SecondCountableTopologyEither E F] [μ.IsAddRightInvariant]
    (hu : AEStronglyMeasurable u (μ.restrict s)) (hs : IsOpen s)
    (h : ∀ᵐ x ∂μ, x ∈ s → HasLineDerivAt ℝ u (u' x) x v) :
    AEStronglyMeasurable u' (μ.restrict s) := by
  have hsm := hs.measurableSet
  -- Extending `u` by zero off `s` makes the difference quotients measurable on all of `E`.
  have hw : AEStronglyMeasurable (s.indicator u) μ :=
    (aestronglyMeasurable_indicator_iff hsm).2 hu
  let t : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa [t, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · simp only [mem_compl_iff, mem_singleton_iff, t, inv_eq_zero]
      positivity
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => (t n)⁻¹ • (s.indicator u (x + t n • v) - s.indicator u x)) (fun n => ?_) ?_
  · exact (((hw.comp_quasiMeasurePreserving
      (measurePreserving_add_right μ (t n • v)).quasiMeasurePreserving).sub hw).const_smul
        _).restrict
  · filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hsm] with x hx hxs
    have hev : ∀ᶠ n in atTop, x + t n • v ∈ s := by
      have hlim : Tendsto (fun n => x + t n • v) atTop (𝓝 x) := by
        have h0 : Tendsto (fun n => t n • v) atTop (𝓝 ((0 : ℝ) • v)) :=
          (ht.mono_right nhdsWithin_le_nhds).smul_const v
        simpa using tendsto_const_nhds.add h0
      exact hlim.eventually (hs.mem_nhds hxs)
    refine ((hx hxs).tendsto_slope_zero.comp ht).congr' ?_
    filter_upwards [hev] with n hn
    simp [indicator_of_mem hn, indicator_of_mem hxs]

end TauCeti

/-- An almost-everywhere line derivative of a function locally Lipschitz on an open set `s` is
locally integrable on `s`: it is measurable, and near each point it is bounded almost everywhere by
`C * ‖v‖` for a local Lipschitz constant `C`. -/
theorem LocallyLipschitzOn.locallyIntegrableOn_of_ae_hasLineDerivAt
    [SecondCountableTopologyEither E F] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ]
    (hu : LocallyLipschitzOn s u) (hs : IsOpen s)
    (h : ∀ᵐ x ∂μ, x ∈ s → HasLineDerivAt ℝ u (u' x) x v) :
    LocallyIntegrableOn u' s μ := by
  have hm := TauCeti.aestronglyMeasurable_of_ae_hasLineDerivAt
    (hu.continuousOn.aestronglyMeasurable hs.measurableSet) hs h
  intro x hx
  obtain ⟨C, l, hl, hC⟩ := hu hx
  rw [hs.nhdsWithin_eq hx] at hl
  obtain ⟨m, hm', hμm⟩ := μ.finiteAt_nhds x
  obtain ⟨r, hr, hrl⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem hl hm') (hs.mem_nhds hx))
  refine ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),
    hm.mono_set fun y hy => (hrl hy).2, .restrict_of_bounded (C := C * ‖v‖)
      ((measure_mono fun y hy => (hrl hy).1.2).trans_lt hμm) ?_⟩
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_ball] with y hy hyB
  exact (hy (hrl hyB).2).le_of_lipschitzOn (isOpen_ball.mem_nhds hyB)
    (hC.mono fun z hz => (hrl hz).1.1)
