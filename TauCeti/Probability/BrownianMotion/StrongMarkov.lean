/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Order.Cadlag
public import TauCeti.Probability.BrownianMotion.UsualFiltration
import TauCeti.Probability.HasLaw
import TauCeti.Probability.Independence.Stopping
import TauCeti.Probability.Process.StoppedValue

/-!
# The strong Markov property of Brownian motion

Let `B` be a pre-Brownian motion relative to a filtration `ℱ` under `P`. At a stopping time `τ`,
the restarted increment process
`B^{(τ)}_t(ω) := stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω`
measures increments elapsed after `τ`, vanishing identically on `{τ = ⊤}`.

When `B` has almost surely right-continuous paths, restricting `P` to `A ∩ {τ ≠ ⊤}` for any event
`A` in the stopping σ-algebra gives `B^{(τ)}` the path-space law `P (A ∩ {τ ≠ ⊤}) • P.map B`.
Conditioning on `A ∩ {τ ≠ ⊤}` when that event has positive probability yields a pre-Brownian (and,
under almost-sure path continuity, Brownian) motion. When `τ` is almost surely finite, `B^{(τ)}` is
pre-Brownian under right continuity and a Brownian motion under almost-sure path continuity; under
right continuity its entire sample path is independent of `hτ.measurableSpace`.

Because upward dyadic ceiling approximations remain stopping times on raw filtrations, every result
holds directly for stopping times of `ℱ`, and passes immediately to stopping times of the
right-continuous hull `ℱ.rightCont` (including open-set hitting times) via
`IsFilteredPreBrownianReal.rightCont`.

## Main declarations

* `IsFilteredPreBrownianReal.hasLaw_restrict_stoppedValue_shift_of_countable_range`,
  `IsFilteredPreBrownianReal.isPreBrownianReal_stoppedValue_shift_of_countable_range`, and
  `IsFilteredPreBrownianReal.indep_stoppedValue_shift_of_countable_range`: restart at
  countable-range stopping times without path regularity.
* `IsFilteredPreBrownianReal.hasLaw_restrict_stoppedValue_shift` and
  `IsFilteredPreBrownianReal.hasLaw_restrict_stoppedValue_shift_rightCont`: restricted full-path
  laws on `A ∩ {τ ≠ ⊤}` for `ℱ`- and `ℱ.rightCont`-stopping times.
* `IsFilteredPreBrownianReal.isPreBrownianReal_cond_stoppedValue_shift`,
  `IsFilteredPreBrownianReal.isBrownianReal_cond_stoppedValue_shift`,
  `IsFilteredPreBrownianReal.isPreBrownianReal_cond_stoppedValue_shift_rightCont`, and
  `IsFilteredPreBrownianReal.isBrownianReal_cond_stoppedValue_shift_rightCont`: conditional
  pre-Brownian and Brownian motion on positive-probability events `A ∩ {τ ≠ ⊤}`.
* `IsFilteredPreBrownianReal.isPreBrownianReal_stoppedValue_shift`,
  `IsFilteredPreBrownianReal.isBrownianReal_stoppedValue_shift`,
  `IsFilteredPreBrownianReal.indep_stoppedValue_shift`,
  `IsFilteredPreBrownianReal.isPreBrownianReal_stoppedValue_shift_rightCont`,
  `IsFilteredPreBrownianReal.isBrownianReal_stoppedValue_shift_rightCont`, and
  `IsFilteredPreBrownianReal.indep_stoppedValue_shift_rightCont`: the strong Markov restart laws
  and independence on `ℱ` and on `ℱ.rightCont`.
* `ProbabilityTheory.IsBrownianReal.stoppedValue_shift_natural`,
  `ProbabilityTheory.IsBrownianReal.indep_stoppedValue_shift_natural`,
  `ProbabilityTheory.IsBrownianReal.stoppedValue_shift_rightCont_natural`, and
  `ProbabilityTheory.IsBrownianReal.indep_stoppedValue_shift_rightCont_natural`: specializations to
  the natural filtration of a Brownian motion and its right-continuous hull.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.6, Theorem 2.6.16.
* S. P. Lalley, *Brownian Motion*, University of Chicago lecture notes, Theorem 5.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

private lemma hasLaw_finset_restrict_of_hasLaw_smul_map {μ : Measure Ω}
    {Y : ℝ≥0 → Ω → ℝ} {c : ℝ≥0∞} (hB : IsFilteredPreBrownianReal ℱ B P)
    (h : HasLaw (fun ω t ↦ Y t ω) (c • P.map (fun ω t ↦ B t ω)) μ) (I : Finset ℝ≥0) :
    HasLaw (fun ω ↦ I.restrict (Y · ω)) (c • BrownianReal.projectiveFamily I) μ := by
  have hcomp := (hasLaw_map I.measurable_restrict.aemeasurable).comp h
  have hB_meas : Measurable (fun ω t ↦ B t ω) := measurable_pi_iff.2 fun _ ↦ hB.adapted.measurable
  rwa [Measure.map_smul _ I.measurable_restrict.aemeasurable,
    Measure.map_map I.measurable_restrict hB_meas, Function.comp_def, Function.comp_def,
    (hB.hasLaw I).map_eq] at hcomp

/-! ### Countable-range stopping times -/

/-- At a countable-range stopping time `τ`, on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace`,
the entire restarted increment path has law `P (A ∩ {τ ≠ ⊤}) • P.map B`. -/
theorem hasLaw_restrict_stoppedValue_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω))
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) :=
  hτ.hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue_of_countable_range hc hB.hasLaw_shift
    hB.indep_shift hA

/-- At a countable-range stopping time `τ`, on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace`,
each finite-dimensional marginal of the restarted increment process has the Brownian projective
law scaled by `P (A ∩ {τ ≠ ⊤})`. No path continuity is required. -/
theorem hasLaw_restrict_finset_restrict_stoppedValue_shift_of_countable_range
    (hB : IsFilteredPreBrownianReal ℱ B P) (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (I : Finset ℝ≥0) :
    HasLaw
      (fun ω ↦ I.restrict (fun t ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω))
      (P (A ∩ {ω | τ ω ≠ ⊤}) • BrownianReal.projectiveFamily I)
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) :=
  hasLaw_finset_restrict_of_hasLaw_smul_map hB
    (hB.hasLaw_restrict_stoppedValue_shift_of_countable_range hτ hc hA) I

/-- At an almost-surely finite stopping time with countable range, the restarted increment
process of a filtered pre-Brownian motion is pre-Brownian. -/
theorem isPreBrownianReal_stoppedValue_shift_of_countable_range
    (hB : IsFilteredPreBrownianReal ℱ B P) (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨fun I ↦ ?_⟩
  have hrest :
      HasLaw
        (fun ω ↦ I.restrict (fun t ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω))
        (P {ω | τ ω ≠ ⊤} • BrownianReal.projectiveFamily I)
        (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using
      hB.hasLaw_restrict_finset_restrict_stoppedValue_shift_of_countable_range hτ hc .univ I
  exact hrest.of_restrict_of_ae_mem hfin

/-- At an almost-surely finite stopping time with countable range, the entire restarted increment
path of a filtered pre-Brownian motion is independent of `hτ.measurableSpace`. -/
theorem indep_stoppedValue_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact hτ.indep_stoppedValue_add_const_sub_stoppedValue_of_countable_range hc hfin hB.hasLaw_shift
    hB.indep_shift

/-! ### General stopping times on an arbitrary filtration -/

/-- **Restricted path-space strong Markov law.** At an arbitrary stopping time `τ` of `ℱ`, if `B`
has almost surely right-continuous paths, then on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace`
the restarted increment path has law `P (A ∩ {τ ≠ ⊤}) • P.map B`. -/
theorem hasLaw_restrict_stoppedValue_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω))
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact hτ.hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue hrc hB.hasLaw_shift
    hB.indep_shift hA

/-- At an arbitrary stopping time `τ` of `ℱ`, if `B` has almost surely right-continuous paths,
then on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace` each finite-dimensional marginal of the
restarted increment process has the Brownian projective law scaled by `P (A ∩ {τ ≠ ⊤})`. -/
theorem hasLaw_restrict_finset_restrict_stoppedValue_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (I : Finset ℝ≥0) :
    HasLaw
      (fun ω ↦ I.restrict (fun t ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω))
      (P (A ∩ {ω | τ ω ≠ ⊤}) • BrownianReal.projectiveFamily I)
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) :=
  hasLaw_finset_restrict_of_hasLaw_smul_map hB (hB.hasLaw_restrict_stoppedValue_shift hrc hτ hA) I

/-- Joint event factorization at a possibly infinite stopping time `τ` of `ℱ` when `B` has almost
surely right-continuous paths: for `A ∈ hτ.measurableSpace` and any measurable path event `S`, the
probability of `A ∩ {τ ≠ ⊤}` and the restarted path lying in `S` factors as
`P (A ∩ {τ ≠ ⊤}) * P (B ∈ S)`. -/
theorem measure_inter_preimage_stoppedValue_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) :
    P (A ∩ {ω | τ ω ≠ ⊤} ∩
        (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) ⁻¹' S) =
      P (A ∩ {ω | τ ω ≠ ⊤}) * P ((fun ω t ↦ B t ω) ⁻¹' S) := by
  have hlaw := hB.hasLaw_restrict_stoppedValue_shift hrc hτ hA
  have hA'_meas : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter hτ.measurableSet_eq_top.compl
  have hB_meas : Measurable (fun ω t ↦ B t ω) := measurable_pi_iff.2 fun _ ↦ hB.adapted.measurable
  rw [inter_comm, ← Measure.restrict_apply' hA'_meas,
    ← Measure.map_apply_of_aemeasurable hlaw.aemeasurable hS, hlaw.map_eq, smul_apply, smul_eq_mul,
    Measure.map_apply hB_meas hS]

/-- When `B` has almost surely right-continuous paths, conditioning on any positive-probability
event `A ∩ {τ ≠ ⊤}` with `A ∈ hτ.measurableSpace` makes the restarted increment process
pre-Brownian. -/
theorem isPreBrownianReal_cond_stoppedValue_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hpos : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (ProbabilityTheory.cond P (A ∩ {ω | τ ω ≠ ⊤})) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact ⟨fun I ↦
    (hB.hasLaw_restrict_finset_restrict_stoppedValue_shift hrc hτ hA I).cond_of_restrict hpos
      (measure_ne_top P _)⟩

/-- **Conditional strong Markov restart.** When `B` has almost surely continuous paths, conditioning
on any positive-probability event `A ∩ {τ ≠ ⊤}` with `A ∈ hτ.measurableSpace` makes the restarted
increment process a Brownian motion. -/
theorem isBrownianReal_cond_stoppedValue_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hpos : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (ProbabilityTheory.cond P (A ∩ {ω | τ ω ≠ ⊤})) where
  toIsPreBrownianReal :=
    hB.isPreBrownianReal_cond_stoppedValue_shift (hcont.mono fun _ hω ↦ hω.isRightContinuous) hτ hA
      hpos
  cont :=
    (hcont.mono fun _ hω ↦ continuous_stoppedValue_add_const_sub_stoppedValue τ hω).filter_mono
      cond_absolutelyContinuous.ae_le

/-- At an almost-surely finite stopping time of `ℱ`, the restarted increment process of an
almost-surely right-continuous filtered pre-Brownian motion is pre-Brownian. -/
theorem isPreBrownianReal_stoppedValue_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨fun I ↦ ?_⟩
  have hrest :
      HasLaw
        (fun ω ↦ I.restrict (fun t ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω))
        (P {ω | τ ω ≠ ⊤} • BrownianReal.projectiveFamily I)
        (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using hB.hasLaw_restrict_finset_restrict_stoppedValue_shift hrc hτ .univ I
  exact hrest.of_restrict_of_ae_mem hfin

/-- **Strong Markov property (independence).** At an almost-surely finite stopping time `τ` of `ℱ`,
the entire restarted increment path of an almost-surely right-continuous filtered pre-Brownian
motion is independent of `hτ.measurableSpace`. See
`IsFilteredPreBrownianReal.isBrownianReal_stoppedValue_shift` for the Brownian law. -/
theorem indep_stoppedValue_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact hτ.indep_stoppedValue_add_const_sub_stoppedValue hfin hrc hB.hasLaw_shift hB.indep_shift

/-- For an almost-surely right-continuous filtered pre-Brownian motion `B` and an almost-surely
finite stopping time `τ` of `ℱ`, any random variable measurable with respect to
`hτ.measurableSpace` is independent of the entire restarted increment path. -/
theorem indepFun_stoppedValue_shift {E : Type*} [MeasurableSpace E]
    (hB : IsFilteredPreBrownianReal ℱ B P) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω))
    (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {Y : Ω → E}
    (hY : Measurable[hτ.measurableSpace] Y) :
    IndepFun
      (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) Y P :=
  (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_right (hB.indep_stoppedValue_shift hrc hτ hfin) hY.comap_le)

/-- **Strong Markov property (Brownian law).** At an almost-surely finite stopping time `τ` of `ℱ`,
the restarted increment process of an almost-surely continuous filtered pre-Brownian motion is a
Brownian motion. See `IsFilteredPreBrownianReal.indep_stoppedValue_shift` for independence from
`hτ.measurableSpace`. -/
theorem isBrownianReal_stoppedValue_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P where
  toIsPreBrownianReal :=
    hB.isPreBrownianReal_stoppedValue_shift (hcont.mono fun _ hω ↦ hω.isRightContinuous) hτ hfin
  cont := hcont.mono fun _ hω ↦ continuous_stoppedValue_add_const_sub_stoppedValue τ hω

/-! ### Stopping times of the right-continuous filtration `ℱ.rightCont` -/

/-- Restricted path-space strong Markov law at a stopping time `τ` of the right-continuous
filtration `ℱ.rightCont` when `B` has almost surely right-continuous paths. -/
theorem hasLaw_restrict_stoppedValue_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω))
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).hasLaw_restrict_stoppedValue_shift hrc hτ hA

/-- Joint event factorization at a stopping time `τ` of `ℱ.rightCont` when `B` has almost surely
right-continuous paths. -/
theorem measure_inter_preimage_stoppedValue_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) :
    P (A ∩ {ω | τ ω ≠ ⊤} ∩
        (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) ⁻¹' S) =
      P (A ∩ {ω | τ ω ≠ ⊤}) * P ((fun ω t ↦ B t ω) ⁻¹' S) :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).measure_inter_preimage_stoppedValue_shift hrc hτ
    hA hS

/-- When `B` has almost surely right-continuous paths, conditioning on any positive-probability
event `A ∩ {τ ≠ ⊤}` with `A ∈ hτ.measurableSpace` for an `ℱ.rightCont`-stopping time `τ` makes the
restarted increment process pre-Brownian. -/
theorem isPreBrownianReal_cond_stoppedValue_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hpos : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (ProbabilityTheory.cond P (A ∩ {ω | τ ω ≠ ⊤})) :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).isPreBrownianReal_cond_stoppedValue_shift hrc hτ
    hA hpos

/-- When `B` has almost surely continuous paths, conditioning on any positive-probability event
`A ∩ {τ ≠ ⊤}` with `A ∈ hτ.measurableSpace` for an `ℱ.rightCont`-stopping time `τ` makes the
restarted increment process a Brownian motion. -/
theorem isBrownianReal_cond_stoppedValue_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hpos : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (ProbabilityTheory.cond P (A ∩ {ω | τ ω ≠ ⊤})) :=
  (hB.rightCont fun _ ↦
    hcont.mono fun _ hω ↦ hω.continuousWithinAt).isBrownianReal_cond_stoppedValue_shift hcont hτ hA
    hpos

/-- At an almost-surely finite stopping time of `ℱ.rightCont`, the restarted increment process of
an almost-surely right-continuous filtered pre-Brownian motion is pre-Brownian. -/
theorem isPreBrownianReal_stoppedValue_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).isPreBrownianReal_stoppedValue_shift hrc hτ hfin

/-- **Strong Markov property on `ℱ.rightCont` (independence).** At an almost-surely finite stopping
time of `ℱ.rightCont`, the entire restarted increment path of an almost-surely right-continuous
filtered pre-Brownian motion is independent of `hτ.measurableSpace`. See
`IsFilteredPreBrownianReal.isBrownianReal_stoppedValue_shift_rightCont` for the Brownian law. -/
theorem indep_stoppedValue_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).indep_stoppedValue_shift hrc hτ hfin

/-- For an almost-surely right-continuous filtered pre-Brownian motion `B` and an almost-surely
finite stopping time `τ` of `ℱ.rightCont`, any random variable measurable with respect to
`hτ.measurableSpace` is independent of the entire restarted increment path. -/
theorem indepFun_stoppedValue_shift_rightCont {E : Type*} [MeasurableSpace E]
    (hB : IsFilteredPreBrownianReal ℱ B P) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω))
    (hτ : IsStoppingTime ℱ.rightCont τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {Y : Ω → E}
    (hY : Measurable[hτ.measurableSpace] Y) :
    IndepFun
      (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) Y P :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).indepFun_stoppedValue_shift hrc hτ hfin hY

/-- **Strong Markov property on `ℱ.rightCont` (Brownian law).** At an almost-surely finite stopping
time of `ℱ.rightCont`, the restarted increment process of an almost-surely continuous filtered
pre-Brownian motion is a Brownian motion. See
`IsFilteredPreBrownianReal.indep_stoppedValue_shift_rightCont` for independence from
`hτ.measurableSpace`. -/
theorem isBrownianReal_stoppedValue_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P :=
  (hB.rightCont fun _ ↦
    hcont.mono fun _ hω ↦ hω.continuousWithinAt).isBrownianReal_stoppedValue_shift hcont hτ hfin

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {τ : Ω → WithTop ℝ≥0}

/-- **Strong Markov property on the natural filtration (Brownian law).** For a Brownian motion `B`
with strongly measurable coordinates and an almost-surely finite stopping time `τ` of its natural
filtration, the restarted increment process is a Brownian motion. See
`IsBrownianReal.indep_stoppedValue_shift_natural` for independence from `hτ.measurableSpace`. -/
theorem stoppedValue_shift_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas) τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P :=
  (hB.isFilteredPreBrownianReal_natural hmeas).isBrownianReal_stoppedValue_shift hB.cont hτ hfin

/-- **Strong Markov property on the natural filtration (independence).** For a Brownian motion `B`
with strongly measurable coordinates and an almost-surely finite stopping time `τ` of its natural
filtration, the entire restarted increment path is independent of `hτ.measurableSpace`. See
`IsBrownianReal.stoppedValue_shift_natural` for the Brownian law. -/
theorem indep_stoppedValue_shift_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas) τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P :=
  (hB.isFilteredPreBrownianReal_natural hmeas).indep_stoppedValue_shift
    (hB.cont.mono fun _ hω ↦ hω.isRightContinuous) hτ hfin

/-- **Strong Markov property on the right-continuous natural filtration (Brownian law).** For a
Brownian motion `B` with strongly measurable coordinates and an almost-surely finite stopping time
`τ` of `(Filtration.natural B hmeas).rightCont`, the restarted increment process is a Brownian
motion. See `IsBrownianReal.indep_stoppedValue_shift_rightCont_natural` for independence from
`hτ.measurableSpace`. -/
theorem stoppedValue_shift_rightCont_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas).rightCont τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P :=
  (hB.isFilteredPreBrownianReal_natural hmeas).isBrownianReal_stoppedValue_shift_rightCont hB.cont
    hτ hfin

/-- **Strong Markov property on the right-continuous natural filtration (independence).** For a
Brownian motion `B` with strongly measurable coordinates and an almost-surely finite stopping time
`τ` of `(Filtration.natural B hmeas).rightCont`, the entire restarted increment path is independent
of `hτ.measurableSpace`. See `IsBrownianReal.stoppedValue_shift_rightCont_natural` for the Brownian
law. -/
theorem indep_stoppedValue_shift_rightCont_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas).rightCont τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P :=
  (hB.isFilteredPreBrownianReal_natural hmeas).indep_stoppedValue_shift_rightCont
    (hB.cont.mono fun _ hω ↦ hω.isRightContinuous) hτ hfin

end ProbabilityTheory.IsBrownianReal
