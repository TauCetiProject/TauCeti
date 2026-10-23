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

Let `μ` be a translation-invariant measure on a module `E` over a nontrivially normed field `𝕜`,
with continuous translations and scalar multiplication, measurable translations, and measurable
open sets. Let `u : E → F` be a.e.-strongly measurable on an open set `s`, and suppose that at
almost every `x ∈ s` it has a line derivative `u' x` in a fixed direction `v`. Then `u'` is
a.e.-strongly measurable on `s` (`MeasureTheory.AEStronglyMeasurable.of_ae_hasLineDerivAt`),
being the almost-everywhere limit of the difference quotients `t⁻¹ • (u (x + t • v) - u x)`.
If `u` is moreover locally Lipschitz on `s` and `E` is seminormed, then `u'` is essentially
locally bounded there (near each point it is bounded almost everywhere by `C * ‖v‖` for a local
Lipschitz constant `C`), hence locally integrable provided `μ` is locally finite and
`SecondCountableTopologyEither E F` holds
(`LocallyLipschitzOn.locallyIntegrableOn_of_ae_hasLineDerivAt`).

Mathlib's `aestronglyMeasurable_lineDeriv` covers `lineDeriv` of a globally continuous function.
The results here only ask for measurability on `s` and for a line derivative almost everywhere, with
an arbitrary candidate `u'`; this is the form in which a.e. derivatives of locally Lipschitz
functions (Rademacher's theorem) enter the theory of weak derivatives.
-/

public section

open MeasureTheory Metric Set Filter
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace E] {μ : Measure E}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set E} {v : E} {u u' : E → F}

variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstVAdd E E]
  [ContinuousSMul 𝕜 E] [OpensMeasurableSpace E] [MeasurableAdd E] in
/-- For a translation-invariant measure `μ`, an almost-everywhere line derivative of a function
a.e.-strongly measurable on an open set `s` is a.e.-strongly measurable on `s`: it is the
almost-everywhere limit of difference quotients. -/
theorem MeasureTheory.AEStronglyMeasurable.of_ae_hasLineDerivAt [μ.IsAddRightInvariant]
    (hu : AEStronglyMeasurable u (μ.restrict s)) (hs : IsOpen s)
    (h : ∀ᵐ x ∂μ, x ∈ s → HasLineDerivAt 𝕜 u (u' x) x v) :
    AEStronglyMeasurable u' (μ.restrict s) := by
  have hsm := hs.measurableSet
  -- Extending `u` by zero off `s` makes the difference quotients measurable on all of `E`.
  have hw : AEStronglyMeasurable (s.indicator u) μ :=
    (aestronglyMeasurable_indicator_iff hsm).2 hu
  refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : 𝕜))
    (f := fun t x => t⁻¹ • (s.indicator u (x + t • v) - s.indicator u x)) (fun t => ?_) ?_
  · exact (((hw.comp_quasiMeasurePreserving
      (measurePreserving_add_right μ (t • v)).quasiMeasurePreserving).sub hw).const_smul
        _).restrict
  · filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hsm] with x hx hxs
    have hev : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), x + t • v ∈ s := by
      have hlim : Tendsto (fun t : 𝕜 => x + t • v) (𝓝 0) (𝓝 x) :=
        ((continuous_id.smul continuous_const).const_vadd x).tendsto' 0 x (by simp)
      exact nhdsWithin_le_nhds (hlim.eventually (hs.mem_nhds hxs))
    refine (hx hxs).tendsto_slope_zero.congr' ?_
    filter_upwards [hev] with t ht
    simp [indicator_of_mem ht, indicator_of_mem hxs]

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [OpensMeasurableSpace E] [MeasurableAdd E] in
/-- For a locally finite, translation-invariant measure `μ`, assuming
`SecondCountableTopologyEither E F`, an almost-everywhere line derivative of a function locally
Lipschitz on an open set `s` is locally integrable on `s`: it is measurable, and near each point it
is bounded almost everywhere by `C * ‖v‖` for a local Lipschitz constant `C`. -/
theorem LocallyLipschitzOn.locallyIntegrableOn_of_ae_hasLineDerivAt
    [SecondCountableTopologyEither E F] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ]
    (hu : LocallyLipschitzOn s u) (hs : IsOpen s)
    (h : ∀ᵐ x ∂μ, x ∈ s → HasLineDerivAt 𝕜 u (u' x) x v) :
    LocallyIntegrableOn u' s μ := by
  have hm := (hu.continuousOn.aestronglyMeasurable hs.measurableSet).of_ae_hasLineDerivAt hs h
  intro x hx
  obtain ⟨C, l, hl, hC⟩ := hu hx
  rw [hs.nhdsWithin_eq hx] at hl
  obtain ⟨m, hm', hμm⟩ := μ.finiteAt_nhds x
  obtain ⟨r, hr, hrl⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem hl hm') (hs.mem_nhds hx))
  refine ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),
    hm.mono_set fun y hy => (hrl hy).2, .restrict_of_bounded (C := C * ‖v‖)
      ((measure_mono fun y hy => (hrl hy).1.2).trans_lt hμm) ?_⟩
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_ball] with y hy hyB
  -- Estimate the derivative along the line directly, allowing a seminormed domain.
  have hd := hy (hrl hyB).2
  rw [HasLineDerivAt] at hd
  apply hd.le_of_lip' (by positivity)
  have hlim : Tendsto (fun t : 𝕜 => y + t • v) (𝓝 0) (𝓝 y) :=
    (by fun_prop : Continuous fun t : 𝕜 => y + t • v).tendsto' 0 y (by simp)
  filter_upwards [hlim.eventually (isOpen_ball.mem_nhds hyB)] with t ht
  have hb := hC.norm_sub_le (hrl ht).1.1 (hrl hyB).1.1
  simpa [norm_smul, mul_assoc, mul_comm, mul_left_comm] using hb
