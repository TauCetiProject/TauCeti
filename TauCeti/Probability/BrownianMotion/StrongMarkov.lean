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
public import TauCeti.Probability.Process.Filtration.Comp
import TauCeti.Probability.HasLaw
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Independence.Stopping
import TauCeti.Probability.Process.StoppedValue
import TauCeti.Probability.Process.StoppingApproximation

/-!
# The strong Markov property of Brownian motion

Let `B` be a pre-Brownian motion relative to a filtration `ℱ` under `P`. At a stopping time `τ`,
the restarted increment process
`B^{(τ)}_t(ω) := stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω`
measures increments elapsed after `τ`, vanishing identically on `{τ = ⊤}`.

When `B` has almost surely right-continuous paths, restricting `P` to `A ∩ {τ ≠ ⊤}` for any event
`A` in the stopping σ-algebra gives `B^{(τ)}` the path-space law `P (A ∩ {τ ≠ ⊤}) • P.map B`.
Conditioning on `A ∩ {τ ≠ ⊤}` when that event has positive probability yields a pre-Brownian (and,
under path continuity, Brownian) motion. When `τ` is almost surely finite, `B^{(τ)}` is a
Brownian motion under `P` whose entire sample path is independent of `hτ.measurableSpace`.

Because upward dyadic ceiling approximations remain stopping times on raw filtrations, every result
holds directly for stopping times of `ℱ`, and passes immediately to stopping times of the
right-continuous hull `ℱ.rightCont` (including open-set hitting times) via
`IsFilteredPreBrownianReal.rightCont`.

## Main declarations

* `TauCeti.Probability.IsFilteredPreBrownianReal.indep_shift` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.shift`: deterministic time shifts are independent
  of `ℱ s` and remain filtered pre-Brownian on `ℱ.comp (monotone_id.const_add s)`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.hasLaw_restrict_shift_of_countable_range`,
  `TauCeti.Probability.IsFilteredPreBrownianReal.isPreBrownianReal_shift_of_countable_range`, and
  `TauCeti.Probability.IsFilteredPreBrownianReal.indep_shift_of_countable_range`: restart at
  countable-range stopping times without path regularity.
* `TauCeti.Probability.IsFilteredPreBrownianReal.hasLaw_restrict_shift` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.hasLaw_restrict_shift_rightCont`: restricted
  full-path laws on `A ∩ {τ ≠ ⊤}` for `ℱ`- and `ℱ.rightCont`-stopping times.
* `TauCeti.Probability.IsFilteredPreBrownianReal.isBrownianReal_cond_shift` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.isBrownianReal_cond_shift_rightCont`: conditional
  Brownian motion on positive-probability events `A ∩ {τ ≠ ⊤}`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.isBrownianReal_shift_stoppingTime`,
  `TauCeti.Probability.IsFilteredPreBrownianReal.indep_shift_stoppingTime`,
  `TauCeti.Probability.IsFilteredPreBrownianReal.isBrownianReal_shift_stoppingTime_rightCont`, and
  `TauCeti.Probability.IsFilteredPreBrownianReal.indep_shift_stoppingTime_rightCont`: the strong
  Markov restart law and independence on `ℱ` and on `ℱ.rightCont`.
* `ProbabilityTheory.IsBrownianReal.shift_stoppingTime_natural`,
  `ProbabilityTheory.IsBrownianReal.indep_shift_stoppingTime_natural`,
  `ProbabilityTheory.IsBrownianReal.shift_stoppingTime_rightCont_natural`, and
  `ProbabilityTheory.IsBrownianReal.indep_shift_stoppingTime_rightCont_natural`: specializations to
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

/-! ### Deterministic time shifts -/

/-- At a deterministic time `s`, the entire shifted increment process `t ↦ B (s + t) - B s`
is independent of `ℱ s`. -/
theorem indep_shift (hB : IsFilteredPreBrownianReal ℱ B P) (s : ℝ≥0) :
    Indep (.comap (fun ω t ↦ B (s + t) ω - B s ω) inferInstance) (ℱ s) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact hB.adapted.indep_comap_shift_sub hB.indep_sub s

/-- Shifting time by `s` and recentering at `B s` produces a filtered pre-Brownian motion
relative to the shifted filtration `ℱ.comp (monotone_id.const_add s)`. -/
theorem shift (hB : IsFilteredPreBrownianReal ℱ B P) (s : ℝ≥0) :
    IsFilteredPreBrownianReal (ℱ.comp (monotone_id.const_add s))
      (fun t ω ↦ B (s + t) ω - B s ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.shift s
  adapted t := by
    rw [Filtration.measurable_comp_iff]
    exact (hB.adapted (s + t)).sub ((hB.adapted s).mono (ℱ.mono le_self_add) le_rfl)
  indep_sub u v huv := by
    rw [Filtration.comp_apply]
    dsimp only [id_eq]
    have heq : ((fun ω ↦ B (s + v) ω - B s ω) - fun ω ↦ B (s + u) ω - B s ω) =
        B (s + v) - B (s + u) := funext fun ω ↦ sub_sub_sub_cancel_right _ _ _
    rw [heq]
    exact hB.indep_sub (add_le_add_right huv s)

/-- If paths are almost surely right-continuous at each fixed time, the entire shifted increment
process `t ↦ B (s + t) - B s` is independent of the right-continuous slice `ℱ.rightCont s`. -/
theorem indep_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ t, ∀ᵐ ω ∂P, ContinuousWithinAt (B · ω) (Ioi t) t) (s : ℝ≥0) :
    Indep (.comap (fun ω t ↦ B (s + t) ω - B s ω) inferInstance) (ℱ.rightCont s) P :=
  (hB.rightCont hrc).indep_shift s

/-! ### Countable-range stopping times -/

/-- At a countable-range stopping time `τ`, on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace`,
each finite-dimensional marginal of the restarted increment process has the Brownian projective
law scaled by `P (A ∩ {τ ≠ ⊤})`. No path continuity is required. -/
theorem hasLaw_restrict_finset_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (I : Finset ℝ≥0) :
    HasLaw
      (fun ω ↦ I.restrict (fun t ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω))
      (P (A ∩ {ω | τ ω ≠ ⊤}) • BrownianReal.projectiveFamily I)
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  let U : ℝ≥0 → Ω → (I → ℝ) := fun s ω i ↦ B (s + i.val) ω - B s ω
  have hm (s : ℝ≥0) : Measurable (U s) :=
    Measurable.of_eval fun i ↦
      (hB.adapted.measurable (i := s + i.val)).sub (hB.adapted.measurable (i := s))
  have hlaw (s : ℝ≥0) : HasLaw (U s) (BrownianReal.projectiveFamily I) P :=
    (hB.toIsPreBrownianReal.shift s).hasLaw I
  have hind (s : ℝ≥0) : Indep (.comap (U s) inferInstance) (ℱ s) P := by
    refine indep_of_indep_of_le_left (hB.indep_shift s) ?_
    have hcomp : U s = I.restrict ∘ fun ω t ↦ B (s + t) ω - B s ω := rfl
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono I.measurable_restrict.comap_le
  have hA'_meas : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter hτ.measurableSet_eq_top.compl
  refine (hτ.hasLaw_restrict_stoppedValue_of_countable_range hc hm hlaw hind hA).congr ?_
  filter_upwards [ae_restrict_of_forall_mem hA'_meas fun _ hω ↦ hω.2] with ω hω
  ext i
  dsimp only [Finset.restrict_def, U]
  exact stoppedValue_add_const_sub_stoppedValue (u := B) (τ := τ) i.val hω

/-- At a countable-range stopping time `τ`, on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace`,
the entire restarted increment path has law `P (A ∩ {τ ≠ ⊤}) • P.map B`. -/
theorem hasLaw_restrict_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω))
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hA'_meas : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter hτ.measurableSet_eq_top.compl
  have hstop_meas :
      Measurable (stoppedValue (fun s ω (t : ℝ≥0) ↦ B (s + t) ω - B s ω) τ) :=
    hτ.measurable_stoppedValue_of_countable_range hc fun s ↦
      measurable_pi_iff.2 fun t ↦
        (hB.adapted.measurable (i := s + t)).sub (hB.adapted.measurable (i := s))
  have hX_ae :
      AEMeasurable (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
    refine hstop_meas.aemeasurable.congr ?_
    filter_upwards [ae_restrict_of_forall_mem hA'_meas fun _ hω ↦ hω.2] with ω hω
    funext t
    exact (stoppedValue_add_const_sub_stoppedValue (u := B) (τ := τ) t hω).symm
  have hB_ae : AEMeasurable (fun ω t ↦ B t ω) P :=
    (measurable_pi_iff.2 fun _ ↦ hB.adapted.measurable).aemeasurable
  exact HasLaw.smul_map_of_forall_finset_restrict hX_ae hB_ae
    (hB.hasLaw_restrict_finset_shift_of_countable_range hτ hc hA) hB.hasLaw

/-- At an almost-surely finite stopping time with countable range, the restarted increment
process of a filtered pre-Brownian motion is pre-Brownian. -/
theorem isPreBrownianReal_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨fun I ↦ ?_⟩
  have hrest :
      HasLaw
        (fun ω ↦ I.restrict (fun t ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω))
        (P {ω | τ ω ≠ ⊤} • BrownianReal.projectiveFamily I)
        (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using hB.hasLaw_restrict_finset_shift_of_countable_range hτ hc .univ I
  exact hrest.of_restrict_of_ae_mem hfin

/-- At an almost-surely finite stopping time with countable range, the entire restarted increment
path of a filtered pre-Brownian motion is independent of `hτ.measurableSpace`. -/
theorem indep_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact indep_comap_of_forall_hasLaw_restrict_inter (F := {ω | τ ω ≠ ⊤}) hτ.measurableSpace_le hfin
    fun _ hA ↦ hB.hasLaw_restrict_shift_of_countable_range hτ hc hA

/-! ### General stopping times on an arbitrary filtration -/

/-- At an arbitrary stopping time `τ` of `ℱ`, if `B` has almost surely right-continuous paths,
then on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace` each finite-dimensional marginal of the
restarted increment process has the Brownian projective law scaled by `P (A ∩ {τ ≠ ⊤})`. -/
theorem hasLaw_restrict_finset_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (I : Finset ℝ≥0) :
    HasLaw
      (fun ω ↦ I.restrict (fun t ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω))
      (P (A ∩ {ω | τ ω ≠ ⊤}) • BrownianReal.projectiveFamily I)
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  let U : ℝ≥0 → Ω → (I → ℝ) := fun s ω i ↦ B (s + i.val) ω - B s ω
  have hm (s : ℝ≥0) : Measurable (U s) :=
    Measurable.of_eval fun i ↦
      (hB.adapted.measurable (i := s + i.val)).sub (hB.adapted.measurable (i := s))
  have hU_rc : ∀ᵐ ω ∂P, IsRightContinuous (fun s ↦ U s ω) := by
    filter_upwards [hrc] with ω hω s
    refine continuousWithinAt_pi.2 fun i ↦ ?_
    have hshift : ContinuousWithinAt (fun u : ℝ≥0 ↦ B (u + i.val) ω) (Ioi s) s :=
      (hω (s + i.val)).comp (f := fun u : ℝ≥0 ↦ u + i.val) (by fun_prop)
        (fun u (hu : s < u) ↦ add_lt_add_of_lt_of_le hu le_rfl)
    exact hshift.sub (hω s)
  have hlaw (s : ℝ≥0) : HasLaw (U s) (BrownianReal.projectiveFamily I) P :=
    (hB.toIsPreBrownianReal.shift s).hasLaw I
  have hind (s : ℝ≥0) : Indep (.comap (U s) inferInstance) (ℱ s) P := by
    refine indep_of_indep_of_le_left (hB.indep_shift s) ?_
    have hcomp : U s = I.restrict ∘ fun ω t ↦ B (s + t) ω - B s ω := rfl
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono I.measurable_restrict.comap_le
  have hA'_meas : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter hτ.measurableSet_eq_top.compl
  refine (hτ.hasLaw_restrict_stoppedValue hm hU_rc hlaw hind hA).congr ?_
  filter_upwards [ae_restrict_of_forall_mem hA'_meas fun _ hω ↦ hω.2] with ω hω
  ext i
  dsimp only [Finset.restrict_def, U]
  exact stoppedValue_add_const_sub_stoppedValue (u := B) (τ := τ) i.val hω

/-- **Restricted path-space strong Markov law.** At an arbitrary stopping time `τ` of `ℱ`, if `B`
has almost surely right-continuous paths, then on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace`
the restarted increment path has law `P (A ∩ {τ ≠ ⊤}) • P.map B`. -/
theorem hasLaw_restrict_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω))
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact HasLaw.smul_map_of_forall_finset_restrict
    (hτ.aemeasurable_stoppedValue_add_const_sub (fun _ ↦ hB.adapted.measurable) hrc).restrict
    (measurable_pi_iff.2 fun _ ↦ hB.adapted.measurable).aemeasurable
    (hB.hasLaw_restrict_finset_shift hrc hτ hA) hB.hasLaw

/-- Joint event factorization at a possibly infinite stopping time `τ` of `ℱ`: for
`A ∈ hτ.measurableSpace` and any measurable path event `S`, the probability of `A ∩ {τ ≠ ⊤}` and
the restarted path lying in `S` factors as `P (A ∩ {τ ≠ ⊤}) * P (B ∈ S)`. -/
theorem measure_inter_preimage_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) :
    P (A ∩ {ω | τ ω ≠ ⊤} ∩
        (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) ⁻¹' S) =
      P (A ∩ {ω | τ ω ≠ ⊤}) * P ((fun ω t ↦ B t ω) ⁻¹' S) := by
  have hlaw := hB.hasLaw_restrict_shift hrc hτ hA
  have hA'_meas : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter hτ.measurableSet_eq_top.compl
  have hB_meas : Measurable (fun ω t ↦ B t ω) := measurable_pi_iff.2 fun _ ↦ hB.adapted.measurable
  rw [inter_comm, ← Measure.restrict_apply' hA'_meas,
    ← Measure.map_apply_of_aemeasurable hlaw.aemeasurable hS, hlaw.map_eq, smul_apply, smul_eq_mul,
    Measure.map_apply hB_meas hS]

/-- Conditioning on any positive-probability event `A ∩ {τ ≠ ⊤}` with `A ∈ hτ.measurableSpace`
makes the restarted increment process pre-Brownian. -/
theorem isPreBrownianReal_cond_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hpos : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (ProbabilityTheory.cond P (A ∩ {ω | τ ω ≠ ⊤})) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact ⟨fun I ↦
    (hB.hasLaw_restrict_finset_shift hrc hτ hA I).cond_of_restrict hpos (measure_ne_top P _)⟩

/-- **Conditional strong Markov restart.** Conditioning on any positive-probability event
`A ∩ {τ ≠ ⊤}` with `A ∈ hτ.measurableSpace` makes the restarted increment process a Brownian
motion. -/
theorem isBrownianReal_cond_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hpos : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (ProbabilityTheory.cond P (A ∩ {ω | τ ω ≠ ⊤})) where
  toIsPreBrownianReal :=
    hB.isPreBrownianReal_cond_shift (hcont.mono fun _ hω ↦ hω.isRightContinuous) hτ hA hpos
  cont :=
    (hcont.mono fun _ hω ↦ continuous_stoppedValue_add_const_sub_stoppedValue τ hω).filter_mono
      cond_absolutelyContinuous.ae_le

/-- At an almost-surely finite stopping time of `ℱ`, the restarted increment process of an
almost-surely right-continuous filtered pre-Brownian motion is pre-Brownian. -/
theorem isPreBrownianReal_shift_stoppingTime (hB : IsFilteredPreBrownianReal ℱ B P)
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
    simpa using hB.hasLaw_restrict_finset_shift hrc hτ .univ I
  exact hrest.of_restrict_of_ae_mem hfin

/-- **Strong Markov property (independence).** At an almost-surely finite stopping time `τ` of `ℱ`,
the entire restarted increment path of an almost-surely right-continuous filtered pre-Brownian
motion is independent of `hτ.measurableSpace`. See
`IsFilteredPreBrownianReal.isBrownianReal_shift_stoppingTime` for the Brownian law. -/
theorem indep_shift_stoppingTime (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact indep_comap_of_forall_hasLaw_restrict_inter (F := {ω | τ ω ≠ ⊤}) hτ.measurableSpace_le hfin
    fun _ hA ↦ hB.hasLaw_restrict_shift hrc hτ hA

/-- At an almost-surely finite stopping time `τ` of `ℱ`, any random variable measurable with
respect to `hτ.measurableSpace` is independent of the entire restarted increment path. -/
theorem indepFun_shift_stoppingTime {E : Type*} [MeasurableSpace E]
    (hB : IsFilteredPreBrownianReal ℱ B P) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω))
    (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {Y : Ω → E}
    (hY : Measurable[hτ.measurableSpace] Y) :
    IndepFun
      (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) Y P :=
  (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_right (hB.indep_shift_stoppingTime hrc hτ hfin) hY.comap_le)

/-- **Strong Markov property (Brownian law).** At an almost-surely finite stopping time `τ` of `ℱ`,
the restarted increment process of an almost-surely continuous filtered pre-Brownian motion is a
Brownian motion. See `IsFilteredPreBrownianReal.indep_shift_stoppingTime` for independence from
`hτ.measurableSpace`. -/
theorem isBrownianReal_shift_stoppingTime (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P where
  toIsPreBrownianReal :=
    hB.isPreBrownianReal_shift_stoppingTime (hcont.mono fun _ hω ↦ hω.isRightContinuous) hτ hfin
  cont := hcont.mono fun _ hω ↦ continuous_stoppedValue_add_const_sub_stoppedValue τ hω

/-! ### Stopping times of the right-continuous filtration `ℱ.rightCont` -/

/-- Restricted path-space strong Markov law at a stopping time `τ` of the right-continuous
filtration `ℱ.rightCont`. -/
theorem hasLaw_restrict_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω))
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).hasLaw_restrict_shift hrc hτ hA

/-- Joint event factorization at a stopping time `τ` of `ℱ.rightCont`. -/
theorem measure_inter_preimage_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) :
    P (A ∩ {ω | τ ω ≠ ⊤} ∩
        (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) ⁻¹' S) =
      P (A ∩ {ω | τ ω ≠ ⊤}) * P ((fun ω t ↦ B t ω) ⁻¹' S) :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).measure_inter_preimage_shift hrc hτ hA hS

/-- Conditioning on any positive-probability event `A ∩ {τ ≠ ⊤}` with `A ∈ hτ.measurableSpace` for
an `ℱ.rightCont`-stopping time `τ` makes the restarted increment process pre-Brownian. -/
theorem isPreBrownianReal_cond_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hpos : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (ProbabilityTheory.cond P (A ∩ {ω | τ ω ≠ ⊤})) :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).isPreBrownianReal_cond_shift hrc hτ hA hpos

/-- Conditioning on any positive-probability event `A ∩ {τ ≠ ⊤}` with `A ∈ hτ.measurableSpace` for
an `ℱ.rightCont`-stopping time `τ` makes the restarted increment process a Brownian motion. -/
theorem isBrownianReal_cond_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hpos : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
      (ProbabilityTheory.cond P (A ∩ {ω | τ ω ≠ ⊤})) :=
  (hB.rightCont fun _ ↦ hcont.mono fun _ hω ↦ hω.continuousWithinAt).isBrownianReal_cond_shift
    hcont hτ hA hpos

/-- At an almost-surely finite stopping time of `ℱ.rightCont`, the restarted increment process of
an almost-surely right-continuous filtered pre-Brownian motion is pre-Brownian. -/
theorem isPreBrownianReal_shift_stoppingTime_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsPreBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).isPreBrownianReal_shift_stoppingTime hrc hτ hfin

/-- **Strong Markov property on `ℱ.rightCont` (independence).** At an almost-surely finite stopping
time of `ℱ.rightCont`, the entire restarted increment path is independent of `hτ.measurableSpace`.
See `IsFilteredPreBrownianReal.isBrownianReal_shift_stoppingTime_rightCont` for the Brownian law. -/
theorem indep_shift_stoppingTime_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).indep_shift_stoppingTime hrc hτ hfin

/-- At an almost-surely finite stopping time `τ` of `ℱ.rightCont`, any random variable measurable
with respect to `hτ.measurableSpace` is independent of the entire restarted increment path. -/
theorem indepFun_shift_stoppingTime_rightCont {E : Type*} [MeasurableSpace E]
    (hB : IsFilteredPreBrownianReal ℱ B P) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω))
    (hτ : IsStoppingTime ℱ.rightCont τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {Y : Ω → E}
    (hY : Measurable[hτ.measurableSpace] Y) :
    IndepFun
      (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) Y P :=
  (hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s).indepFun_shift_stoppingTime hrc hτ hfin hY

/-- **Strong Markov property on `ℱ.rightCont` (Brownian law).** At an almost-surely finite stopping
time of `ℱ.rightCont`, the restarted increment process of an almost-surely continuous filtered
pre-Brownian motion is a Brownian motion. See
`IsFilteredPreBrownianReal.indep_shift_stoppingTime_rightCont` for independence from
`hτ.measurableSpace`. -/
theorem isBrownianReal_shift_stoppingTime_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P :=
  (hB.rightCont fun _ ↦
    hcont.mono fun _ hω ↦ hω.continuousWithinAt).isBrownianReal_shift_stoppingTime hcont hτ hfin

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {τ : Ω → WithTop ℝ≥0}

/-- **Strong Markov property on the natural filtration (Brownian law).** For a Brownian motion `B`
with strongly measurable coordinates and an almost-surely finite stopping time `τ` of its natural
filtration, the restarted increment process is a Brownian motion. See
`IsBrownianReal.indep_shift_stoppingTime_natural` for independence from `hτ.measurableSpace`. -/
theorem shift_stoppingTime_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas) τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P :=
  (hB.isFilteredPreBrownianReal_natural hmeas).isBrownianReal_shift_stoppingTime hB.cont hτ hfin

/-- **Strong Markov property on the natural filtration (independence).** For a Brownian motion `B`
with strongly measurable coordinates and an almost-surely finite stopping time `τ` of its natural
filtration, the entire restarted increment path is independent of `hτ.measurableSpace`. See
`IsBrownianReal.shift_stoppingTime_natural` for the Brownian law. -/
theorem indep_shift_stoppingTime_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas) τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P :=
  (hB.isFilteredPreBrownianReal_natural hmeas).indep_shift_stoppingTime
    (hB.cont.mono fun _ hω ↦ hω.isRightContinuous) hτ hfin

/-- **Strong Markov property on the right-continuous natural filtration (Brownian law).** For a
Brownian motion `B` with strongly measurable coordinates and an almost-surely finite stopping time
`τ` of `(Filtration.natural B hmeas).rightCont`, the restarted increment process is a Brownian
motion. See `IsBrownianReal.indep_shift_stoppingTime_rightCont_natural` for independence from
`hτ.measurableSpace`. -/
theorem shift_stoppingTime_rightCont_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas).rightCont τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω) P :=
  (hB.isFilteredPreBrownianReal_natural hmeas).isBrownianReal_shift_stoppingTime_rightCont hB.cont
    hτ hfin

/-- **Strong Markov property on the right-continuous natural filtration (independence).** For a
Brownian motion `B` with strongly measurable coordinates and an almost-surely finite stopping time
`τ` of `(Filtration.natural B hmeas).rightCont`, the entire restarted increment path is independent
of `hτ.measurableSpace`. See `IsBrownianReal.shift_stoppingTime_rightCont_natural` for the Brownian
law. -/
theorem indep_shift_stoppingTime_rightCont_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas).rightCont τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue B (fun ω' ↦ τ ω' + t) ω - stoppedValue B τ ω)
        inferInstance)
      hτ.measurableSpace P :=
  (hB.isFilteredPreBrownianReal_natural hmeas).indep_shift_stoppingTime_rightCont
    (hB.cont.mono fun _ hω ↦ hω.isRightContinuous) hτ hfin

end ProbabilityTheory.IsBrownianReal
