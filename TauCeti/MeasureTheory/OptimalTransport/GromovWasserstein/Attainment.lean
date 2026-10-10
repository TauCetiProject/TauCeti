/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lusin
public import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
public import TauCeti.MeasureTheory.OptimalTransport.Compactness
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Optimal Gromov–Wasserstein couplings

The Gromov–Wasserstein distance `TauCeti.gromovWassersteinEDist p μ ωX ν ωY` is an infimum of
distortions over the couplings of `μ` and `ν`. This file proves that the infimum is attained when
`X` and `Y` are Polish and `μ` and `ν` are Borel probability measures: some coupling has distortion
equal to the distance. The kernels `ωX` and `ωY` are only assumed almost-everywhere strongly
measurable, with values in an arbitrary pseudo-extended-metric space `Z`; no continuity, no lower
semicontinuity, and no separability or completeness of `Z` is needed, and every exponent
`p : ℝ≥0∞` is allowed, including `p = ∞`. No integrability is assumed either: the optimal value may
be `∞`.

The proof is the direct method. The couplings form a nonempty weakly compact set
(`TauCeti.isCompact_setOfPred_isCoupling`), so it suffices that the distortion is
weakly lower semicontinuous on it (`TauCeti.lowerSemicontinuousOn_gromovWassersteinDistortion`).
The distortion integrates the discrepancy `edist (ωX (x, x')) (ωY (y, y'))` against the square
`π ⊗ π`, and this integrand is not lower semicontinuous when the kernels are merely measurable. It
is continuous, however, on a closed set carrying all but an arbitrarily small part of the mass of
`π ⊗ π`, *uniformly in the coupling `π`*: by Lusin's theorem `ωX` is continuous on a closed set
`K ⊆ X × X` with `(μ ⊗ μ) Kᶜ` small, `ωY` on a closed `L ⊆ Y × Y` with `(ν ⊗ ν) Lᶜ` small, and the
image of `π ⊗ π` on `X × X` is `μ ⊗ μ` and on `Y × Y` is `ν ⊗ ν` whatever `π` is. That uniformity is
exactly the hypothesis of `TauCeti.lowerSemicontinuousOn_lintegral_comp`. For `p = ∞` the same
argument is applied to the indicator of `{edist > c}`, whose integral is positive exactly when the
essential supremum exceeds `c`.

## Main statements

* `TauCeti.lowerSemicontinuousOn_gromovWassersteinDistortion` — the distortion is weakly lower
  semicontinuous on the couplings of two fixed finite measures, on second-countable
  pseudometrizable carriers;
* `TauCeti.exists_isCoupling_gromovWassersteinDistortion_eq` — **existence of an optimal
  Gromov–Wasserstein coupling** on Polish carriers, the specialization of
  `TauCeti.exists_isCoupling_gromovWassersteinDistortion_eq_of_isTightMeasureSet` for tight
  marginals on second-countable metrizable carriers;
* `TauCeti.exists_isCoupling_gromovWassersteinDistortion_dist_eq` — its specialization to
  metric-measure spaces, whose kernels are the distance functions.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*, J. Mach.
  Learn. Res. 26 (2025), Theorem 26, the existence of optimal couplings for measurable kernels with
  values in a metric space.
* F. Mémoli, *Gromov–Wasserstein distances and the metric approach to object matching*, Found.
  Comput. Math. 11 (2011), where optimal couplings are shown to exist for compact metric-measure
  spaces.
-/

public section

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] [PseudoEMetricSpace Z]
  {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} [IsFiniteMeasure ν]
  {ωX : X × X → Z} {ωY : Y × Y → Z}

/-- **The uniform Lusin property of the kernel pair.** For every `ε > 0` there is a closed set of
pairs of points of `X × Y` on which both kernels are continuous and whose complement has mass at
most `ε` for the square of every coupling of `μ` and `ν`. -/
private theorem exists_isClosed_continuousOn_kernels
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C : Set ((X × Y) × (X × Y)), IsClosed C ∧
      ContinuousOn (fun q : (X × Y) × (X × Y) ↦ (ωX (q.1.1, q.2.1), ωY (q.1.2, q.2.2))) C ∧
      ∀ π : Measure (X × Y), IsCoupling π μ ν → π.prod π Cᶜ ≤ ε := by
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨K, -, hK, hKμ, hωK⟩ :=
    hωX.exists_isClosed_measure_sdiff_lt_continuousOn MeasurableSet.univ (measure_ne_top _ _) hε2
  obtain ⟨L, -, hL, hLν, hωL⟩ :=
    hωY.exists_isClosed_measure_sdiff_lt_continuousOn MeasurableSet.univ (measure_ne_top _ _) hε2
  rw [← compl_eq_univ_sdiff] at hKμ hLν
  have hfst : Continuous (Prod.map Prod.fst Prod.fst : (X × Y) × (X × Y) → X × X) := by fun_prop
  have hsnd : Continuous (Prod.map Prod.snd Prod.snd : (X × Y) × (X × Y) → Y × Y) := by fun_prop
  refine ⟨Prod.map Prod.fst Prod.fst ⁻¹' K ∩ Prod.map Prod.snd Prod.snd ⁻¹' L,
    (hK.preimage hfst).inter (hL.preimage hsnd), ?_, fun π hπ ↦ ?_⟩
  · exact (hωK.comp hfst.continuousOn fun _ hq ↦ hq.1).prodMk
      (hωL.comp hsnd.continuousOn fun _ hq ↦ hq.2)
  · have : IsFiniteMeasure π := hπ.isFiniteMeasure
    rw [compl_inter, ← preimage_compl, ← preimage_compl]
    calc π.prod π (Prod.map Prod.fst Prod.fst ⁻¹' Kᶜ ∪ Prod.map Prod.snd Prod.snd ⁻¹' Lᶜ)
        ≤ π.prod π (Prod.map Prod.fst Prod.fst ⁻¹' Kᶜ) +
            π.prod π (Prod.map Prod.snd Prod.snd ⁻¹' Lᶜ) := measure_union_le _ _
      _ = μ.prod μ Kᶜ + ν.prod ν Lᶜ := by
        rw [(hπ.measurePreserving_fst.prod hπ.measurePreserving_fst).measure_preimage
            hK.isOpen_compl.measurableSet.nullMeasurableSet,
          (hπ.measurePreserving_snd.prod hπ.measurePreserving_snd).measure_preimage
            hL.isOpen_compl.measurableSet.nullMeasurableSet]
      _ ≤ ε / 2 + ε / 2 := add_le_add hKμ.le hLν.le
      _ = ε := ENNReal.add_halves ε

/-- For a lower semicontinuous measurable `g`, the integral of `g` of the kernel discrepancy
against the square of a coupling is weakly lower semicontinuous on the couplings. -/
private theorem lowerSemicontinuousOn_lintegral_comp_edist {g : ℝ≥0∞ → ℝ≥0∞}
    (hg : LowerSemicontinuous g) (hgm : Measurable g)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν)) :
    LowerSemicontinuousOn
      (fun π : ProbabilityMeasure (X × Y) ↦ ∫⁻ q, g (edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
        ∂((π : Measure (X × Y)).prod (π : Measure (X × Y))))
      {π | IsCoupling (π : Measure (X × Y)) μ ν} := by
  -- `TauCeti.lowerSemicontinuousOn_lintegral_comp` runs on a pseudometric, which metrizability of
  -- the two factors supplies on the space of pairs of points of `X × Y`.
  let : PseudoMetricSpace ((X × Y) × (X × Y)) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  set K := {π : ProbabilityMeasure (X × Y) | IsCoupling (π : Measure (X × Y)) μ ν}
  have hsq : Continuous fun π : ProbabilityMeasure (X × Y) ↦ π.prod π :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  refine LowerSemicontinuousOn.comp (g := fun π : ProbabilityMeasure (X × Y) ↦ π.prod π)
    (lowerSemicontinuousOn_lintegral_comp (S := (fun π ↦ π.prod π) '' K)
      (Φ := fun q : (X × Y) × (X × Y) ↦ (ωX (q.1.1, q.2.1), ωY (q.1.2, q.2.2)))
      (hg.comp continuous_edist) (fun ε hε ↦ ?_) ?_) hsq.continuousOn (mapsTo_image _ _)
  · obtain ⟨C, hC, hΦC, hCπ⟩ := exists_isClosed_continuousOn_kernels hωX hωY hε
    refine ⟨C, hC, hΦC, ?_⟩
    rintro _ ⟨π, hπ, rfl⟩
    exact hCπ π hπ
  · rintro _ ⟨π, hπ, rfl⟩
    exact hgm.comp_aemeasurable (hπ.aestronglyMeasurable_edist hωX hωY).aemeasurable

/-- **Lower semicontinuity of the distortion.** On second-countable pseudometrizable carriers, the
`p`-distortion of a coupling of two fixed finite measures is weakly lower semicontinuous in the
coupling, for almost-everywhere strongly measurable kernels and every exponent `p`. -/
theorem lowerSemicontinuousOn_gromovWassersteinDistortion
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (p : ℝ≥0∞) :
    LowerSemicontinuousOn
      (fun π : ProbabilityMeasure (X × Y) ↦ gromovWassersteinDistortion p ωX ωY π)
      {π | IsCoupling (π : Measure (X × Y)) μ ν} := by
  rcases eq_or_ne p 0 with rfl | hp0
  · refine fun π hπ ↦ LowerSemicontinuousWithinAt.congr_of_eventuallyEq
      (lowerSemicontinuousOn_const (z := (0 : ℝ≥0∞)) π hπ) hπ
      (eventually_nhdsWithin_of_forall fun σ hσ ↦ ?_)
    beta_reduce
    rw [gromovWassersteinDistortion_def, eLpNorm_exponent_zero
      (IsCoupling.aestronglyMeasurable_edist hσ hωX hωY)]
  rcases eq_or_ne p ∞ with rfl | hptop
  · -- The essential supremum exceeds `c` exactly when the indicator of `{edist > c}` has positive
    -- integral, and that integral is lower semicontinuous.
    intro π₀ hπ₀
    refine lowerSemicontinuousWithinAt_iff.mpr fun c hc ↦ ?_
    have key : ∀ π : ProbabilityMeasure (X × Y), IsCoupling (π : Measure (X × Y)) μ ν →
        (gromovWassersteinDistortion ∞ ωX ωY π ≤ c ↔
          ∫⁻ q, (Ioi c).indicator (fun _ ↦ (1 : ℝ≥0∞))
            (edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
            ∂((π : Measure (X × Y)).prod (π : Measure (X × Y))) = 0) := by
      intro π hπ
      have hmeas := hπ.aestronglyMeasurable_edist hωX hωY
      have hind : AEMeasurable (fun q : (X × Y) × (X × Y) ↦ (Ioi c).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) (edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2))))
          ((π : Measure (X × Y)).prod (π : Measure (X × Y))) :=
        (measurable_const.indicator measurableSet_Ioi).comp_aemeasurable hmeas.aemeasurable
      rw [gromovWassersteinDistortion_def, eLpNorm_exponent_top hmeas, lintegral_eq_zero_iff' hind]
      refine ⟨fun h ↦ ?_, fun h ↦ eLpNormEssSup_le_of_ae_enorm_bound ?_⟩
      · filter_upwards [ae_le_eLpNormEssSup (f := fun q : (X × Y) × (X × Y) ↦
          edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))] with q hq
        simpa using (hq.trans h).not_gt
      · filter_upwards [h] with q hq
        simpa using hq
    have h₀ : 0 < ∫⁻ q, (Ioi c).indicator (fun _ ↦ (1 : ℝ≥0∞))
        (edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
          ∂((π₀ : Measure (X × Y)).prod (π₀ : Measure (X × Y))) :=
      pos_iff_ne_zero.mpr fun h ↦ (not_le_of_gt hc) ((key π₀ hπ₀).mpr h)
    filter_upwards [lowerSemicontinuousOn_lintegral_comp_edist
      (isOpen_Ioi.lowerSemicontinuous_indicator zero_le_one)
      (measurable_const.indicator measurableSet_Ioi) hωX hωY π₀ hπ₀ 0 h₀,
      self_mem_nhdsWithin] with π hπ hπK
    exact lt_of_not_ge fun h ↦ hπ.ne' ((key π hπK).mp h)
  · -- For `0 < p < ∞` the distortion is an increasing continuous function of the integral of the
    -- `p`-th power of the discrepancy.
    have hint := lowerSemicontinuousOn_lintegral_comp_edist (μ := μ) (ν := ν)
      (ENNReal.continuous_rpow_const (y := p.toReal)).lowerSemicontinuous
      (ENNReal.continuous_rpow_const.measurable) hωX hωY
    have hcomp := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).comp_lowerSemicontinuousOn
      hint (ENNReal.monotone_rpow_of_nonneg (by positivity))
    refine fun π hπ ↦ LowerSemicontinuousWithinAt.congr_of_eventuallyEq (hcomp π hπ) hπ
      (eventually_nhdsWithin_of_forall fun σ hσ ↦ ?_)
    beta_reduce
    rw [Function.comp_apply, gromovWassersteinDistortion_def,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop
        (IsCoupling.aestronglyMeasurable_edist hσ hωX hωY)]
    simp only [enorm_eq_self]

/-- **Existence of an optimal Gromov–Wasserstein coupling for tight marginals.** For tight Borel
probability measures `μ` and `ν` on second-countable metrizable spaces and almost-everywhere
strongly measurable kernels `ωX` and `ωY` with values in any pseudo-extended-metric space, some
coupling of `μ` and `ν` has distortion equal to the `p`-Gromov–Wasserstein distance, for every
exponent `p`. The common value may be `∞`. -/
theorem exists_isCoupling_gromovWassersteinDistortion_eq_of_isTightMeasureSet {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X}
    [IsProbabilityMeasure μ] {ν : Measure Y} [IsProbabilityMeasure ν] (hμ : IsTightMeasureSet {μ})
    (hν : IsTightMeasureSet {ν}) {ωX : X × X → Z} {ωY : Y × Y → Z}
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (p : ℝ≥0∞) :
    ∃ π, IsCoupling π μ ν ∧
      gromovWassersteinDistortion p ωX ωY π = gromovWassersteinEDist p μ ωX ν ωY := by
  have hKne : {π : ProbabilityMeasure (X × Y) | IsCoupling (π : Measure (X × Y)) μ ν}.Nonempty :=
    ⟨(Coupling.prod ⟨μ, ‹_›⟩ ⟨ν, ‹_›⟩).1, (Coupling.prod ⟨μ, ‹_›⟩ ⟨ν, ‹_›⟩).2⟩
  obtain ⟨π, hπ, hπmin⟩ :=
    (lowerSemicontinuousOn_gromovWassersteinDistortion hωX hωY p).exists_isMinOn hKne
      (isCompact_setOfPred_isCoupling (μ := ⟨μ, ‹_›⟩) (ν := ⟨ν, ‹_›⟩) hμ hν)
  refine ⟨π, hπ, le_antisymm (le_gromovWassersteinEDist fun σ hσ ↦ ?_)
    (gromovWassersteinEDist_le hπ p ωX ωY)⟩
  have : IsProbabilityMeasure σ := hσ.isProbabilityMeasure
  exact isMinOn_iff.mp hπmin ⟨σ, ‹_›⟩ hσ

/-- **Existence of an optimal Gromov–Wasserstein coupling.** For Borel probability measures `μ` and
`ν` on Polish spaces and almost-everywhere strongly measurable kernels `ωX` and `ωY` with values in
any pseudo-extended-metric space, some coupling of `μ` and `ν` has distortion equal to the
`p`-Gromov–Wasserstein distance, for every exponent `p`. The common value may be `∞`. -/
theorem exists_isCoupling_gromovWassersteinDistortion_eq {X Y : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y)
    [IsProbabilityMeasure ν] {ωX : X × X → Z} {ωY : Y × Y → Z}
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (p : ℝ≥0∞) :
    ∃ π, IsCoupling π μ ν ∧
      gromovWassersteinDistortion p ωX ωY π = gromovWassersteinEDist p μ ωX ν ωY :=
  exists_isCoupling_gromovWassersteinDistortion_eq_of_isTightMeasureSet
    isTightMeasureSet_singleton isTightMeasureSet_singleton hωX hωY p

/-- **Optimal Gromov–Wasserstein couplings of metric-measure spaces.** For Borel probability
measures on complete separable metric spaces, with the distance functions as kernels, the
`p`-Gromov–Wasserstein distance is attained by some coupling. -/
theorem exists_isCoupling_gromovWassersteinDistortion_dist_eq {X Y : Type*} [MetricSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [BorelSpace Y] (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y)
    [IsProbabilityMeasure ν] (p : ℝ≥0∞) :
    ∃ π, IsCoupling π μ ν ∧
      gromovWassersteinDistortion p (fun x : X × X ↦ dist x.1 x.2)
          (fun y : Y × Y ↦ dist y.1 y.2) π =
        gromovWassersteinEDist p μ (fun x : X × X ↦ dist x.1 x.2) ν
          (fun y : Y × Y ↦ dist y.1 y.2) :=
  exists_isCoupling_gromovWassersteinDistortion_eq μ ν continuous_dist.aestronglyMeasurable
    continuous_dist.aestronglyMeasurable p

end TauCeti
