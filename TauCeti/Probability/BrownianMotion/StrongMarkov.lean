/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Topology.Order.Cadlag
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Order.WithBot
import TauCeti.MeasureTheory.Function.ConditionalLExpectation
import TauCeti.Probability.BrownianMotion.Predictable
import TauCeti.Probability.BrownianMotion.UsualFiltration
import TauCeti.Probability.Independence.CondExp
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Process.Filtration.Progressive
import TauCeti.Probability.Process.StoppedValue
import TauCeti.Probability.Process.StoppingApproximation

/-!
# The strong Markov property of Brownian motion

If `B` is a Brownian motion relative to a filtration `ℱ` and `τ` is an `ℱ.rightCont`-stopping time
(equivalently, `{τ < t} ∈ ℱ t` for every `t`), then on `{τ ≠ ⊤}` the restarted increment process
`t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω` is a standard Brownian motion independent of the
stopping sigma-algebra `hτ.measurableSpace` (`ℱ_{τ+}`).

No completeness or right continuity is assumed on the ambient filtration `ℱ`, nor is `B` assumed to
be literally progressive or everywhere continuous. Instead, the proof proceeds in four stages:

1. **Countable-range stopping times (`ℱ`):** decomposing `A ∩ {τ ≠ ⊤}` into the countable family of
   slices `A ∩ {τ = s} ∈ ℱ s` reduces the restricted path law directly to deterministic-time shift
   invariance and increment independence, without any path regularity.
2. **Dyadic ceiling approximation (`ℱ.rightCont`) for strongly progressive right-continuous paths:**
   `TauCeti.Probability.IsFilteredPreBrownianReal.rightCont` extends increment independence to
   `ℱ.rightCont`, where the upward dyadic approximations `TauCeti.dyadicCeilTime n ∘ τ` are
   countable-range stopping times with `{dyadicCeilTime n (τ ω) ≠ ⊤} = {τ ω ≠ ⊤}`. Dominated
   convergence of bounded continuous finite-dimensional cylinder integrals and projective-limit
   uniqueness pass the restricted pushforward identity to `τ`.
3. **Indistinguishable predictable modification:** for an arbitrary filtered pre-Brownian motion `B`
   with almost-surely continuous paths, `exists_isStronglyPredictable_isBrownianReal_indist` selects
   a predictable Brownian version `W ≡ᵐ[P] B` on the same raw filtration `ℱ`, giving literal joint
   and stopped-value measurability for `W` and transferring all distributional, independence, and
   conditional-expectation conclusions back to `B` outside one common null set.
4. **Transition-kernel and conditional-expectation formulas:** on `A ∩ {τ ≠ ⊤}`, the pair
   `(stoppedValue B τ, B_{τ + ·} - B_τ)` factors as the product of the restricted stopped-position
   law and Wiener law, yielding both full-path conditional-expectation freezing at a.s.-finite `τ`
   and the Gaussian heat-kernel formulas for `condLExp`, integrable `condExp`, and localized
   exhausting stopping events when `g (z + ·)` is Gaussian-integrable at each fixed start `z`.

## Main declarations

* `ProbabilityTheory.IsPreBrownianReal.identDistrib`,
  `ProbabilityTheory.IsPreBrownianReal.of_identDistrib`,
  `ProbabilityTheory.IsPreBrownianReal.identDistrib_shift`: projective-limit uniqueness of the
  pre-Brownian path law on `ℝ≥0 → ℝ`.
* Under `TauCeti.Probability.IsFilteredPreBrownianReal`:
  * `map_restrict_shift_eq_smul_of_countable_range`,
    `isFilteredPreBrownianReal_stoppedValue_sub_of_countable_range`: strong Markov restart at
    countable-range stopping times without path continuity.
  * `isFilteredPreBrownianReal_stoppedValue_sub_rightCont`,
    `isFilteredPreBrownianReal_stoppedValue_sub`: the restarted process
    `t ↦ stoppedValue B (τ + t) - stoppedValue B τ` is a filtered pre-Brownian motion on the
    post-stopping filtration `hτ.shiftFiltration`.
  * `map_restrict_shift_eq_smul_rightCont`, `isBrownianReal_shift_cond_rightCont`: restricted
    pushforward and conditional-probability Brownian restart on `A ∩ {τ ≠ ⊤}` for stopping times
    that may take the value `⊤` with positive probability.
  * `strongMarkov_rightCont`, `strongMarkov` (and `ProbabilityTheory.IsBrownianReal` counterparts
    `strongMarkov_rightCont_natural`, `strongMarkov_natural`): the strong Markov property at
    almost-surely finite stopping times.
  * `condLExp_stoppedValue_shift_rightCont`, `condExp_stoppedValue_shift_rightCont`,
    `condLExp_indicator_shift_eval_rightCont`, `condExp_indicator_shift_eval_rightCont`,
    `exists_measurableSet_condExp_indicator_shift_eval_rightCont`: full-path freezing and Gaussian
    transition-kernel conditional expectations at stopping times.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition, Springer,
  1991, §2.6, Theorem 2.6.16.
* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, Theorem 2.16.
* S. P. Lalley, *Brownian Motion*, University of Chicago lecture notes, Theorem 5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {Q : Measure Ω'} {B : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}

/-- Two pre-Brownian motions with almost-everywhere measurable path maps have the same full path
distribution on `ℝ≥0 → ℝ`. -/
theorem identDistrib (hB : IsPreBrownianReal B P) (hY : IsPreBrownianReal Y Q)
    (hBm : AEMeasurable (fun ω t ↦ B t ω) P) (hYm : AEMeasurable (fun ω t ↦ Y t ω) Q) :
    IdentDistrib (fun ω t ↦ B t ω) (fun ω t ↦ Y t ω) P Q where
  aemeasurable_fst := hBm
  aemeasurable_snd := hYm
  map_eq := IsProjectiveLimit.unique (P := BrownianReal.projectiveFamily)
    (fun I ↦ by
      rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hBm,
        Function.comp_def]
      exact (hB.hasLaw I).map_eq)
    (fun I ↦ by
      rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hYm,
        Function.comp_def]
      exact (hY.hasLaw I).map_eq)

/-- A process whose path map has the same distribution as a pre-Brownian motion is pre-Brownian. -/
theorem of_identDistrib (hB : IsPreBrownianReal B P)
    (hid : IdentDistrib (fun ω t ↦ Y t ω) (fun ω t ↦ B t ω) Q P) :
    IsPreBrownianReal Y Q where
  hasLaw I := by
    have hcomp := hid.comp (Finset.measurable_restrict I)
    exact ⟨hcomp.aemeasurable_fst, hcomp.map_eq.trans (hB.hasLaw I).map_eq⟩

/-- Deterministic-time shift invariance of the full path law of a pre-Brownian motion. -/
theorem identDistrib_shift (hB : IsPreBrownianReal B P)
    (hBm : AEMeasurable (fun ω t ↦ B t ω) P) (s : ℝ≥0) :
    IdentDistrib (fun ω t ↦ B (s + t) ω - B s ω) (fun ω t ↦ B t ω) P P :=
  (hB.shift s).identDistrib hB
    (by
      simpa only [Function.comp_def, Pi.sub_apply] using
        ((Measurable.of_eval fun t ↦ (measurable_pi_apply (s + t)).sub
          (measurable_pi_apply s)).comp_aemeasurable hBm))
    hBm

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-! ### Deterministic-time shift and shared reduction helpers -/

/-- For a filtered pre-Brownian motion, the entire shifted increment process after time `s` is
independent of `ℱ s`. -/
theorem indep_comap_shift (hB : IsFilteredPreBrownianReal ℱ B P) (s : ℝ≥0) :
    Indep (.comap (fun ω t ↦ B (s + t) ω - B s ω) inferInstance) (ℱ s) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact MeasureTheory.Adapted.indep_comap_shift hB.adapted hB.indep_sub s

/-- Restricted to any `ℱ s`-measurable event `A`, the shifted increment path after `s` has
pushforward measure `P A • P.map (fun ω t ↦ B t ω)`, including when `P A = 0`. -/
theorem map_restrict_shift_eq_smul_const (hB : IsFilteredPreBrownianReal ℱ B P) (s : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    (P.restrict A).map (fun ω t ↦ B (s + t) ω - B s ω) = P A • P.map (fun ω t ↦ B t ω) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hBm : Measurable fun ω t ↦ B t ω := Measurable.of_eval fun _ ↦ hB.adapted.measurable
  have hSm : Measurable fun ω t ↦ B (s + t) ω - B s ω :=
    Measurable.of_eval fun _ ↦ hB.adapted.measurable.sub hB.adapted.measurable
  have hid := hB.toIsPreBrownianReal.identDistrib_shift hBm.aemeasurable s
  ext U hU
  rw [Measure.map_apply hSm hU, Measure.restrict_apply' (ℱ.le s A hA), smul_apply,
    smul_eq_mul, ← hid.map_eq, Measure.map_apply hSm hU, mul_comm]
  exact (Indep_iff _ _ P).1 (hB.indep_comap_shift s) _ _ ⟨U, hU, rfl⟩ hA

private theorem restrict_eq_of_ae_ne_top {E : Set Ω} (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    P.restrict (E ∩ {ω | τ ω ≠ ⊤}) = P.restrict E ∧ P (E ∩ {ω | τ ω ≠ ⊤}) = P E := by
  have hae : (E ∩ {ω | τ ω ≠ ⊤} : Set Ω) =ᵐ[P] E :=
    hτ_ne_top.mono fun ω hω ↦ by simp [hω]
  exact ⟨Measure.restrict_congr_set hae, measure_congr hae⟩

private theorem identDistrib_and_indep_of_map_restrict_eq_smul [IsProbabilityMeasure P]
    {S : Ω → ℝ≥0 → ℝ} (hSm : Measurable S)
    (hBm : AEMeasurable (fun ω t ↦ B t ω) P) (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hmap : ∀ {A : Set Ω}, MeasurableSet[m] A →
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map S =
        P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω)) :
    IdentDistrib S (fun ω t ↦ B t ω) P P ∧ Indep (.comap S inferInstance) m P := by
  obtain ⟨hrestU, hmeasU⟩ := restrict_eq_of_ae_ne_top (E := univ) hτ_ne_top
  have hmapU := hmap MeasurableSet.univ
  rw [hrestU, Measure.restrict_univ, hmeasU, measure_univ, one_smul] at hmapU
  refine ⟨⟨hSm.aemeasurable, hBm, hmapU⟩, (Indep_iff _ _ P).2 ?_⟩
  rintro _ A ⟨U, hU, rfl⟩ hA
  obtain ⟨hrest, hmeas⟩ := restrict_eq_of_ae_ne_top (E := A) hτ_ne_top
  have h := congrArg (fun μ ↦ μ U) (hmap hA)
  rwa [hrest, hmeas, Measure.map_apply hSm hU, Measure.restrict_apply (hSm hU),
    smul_apply, smul_eq_mul, ← hmapU, Measure.map_apply hSm hU, mul_comm] at h

private theorem isFilteredPreBrownianReal_stoppedValue_sub_of_forall_shift
    {𝒢 : Filtration ℝ≥0 mΩ} (hτ : IsStoppingTime 𝒢 τ) (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hadapt : Adapted hτ.shiftFiltration
      (fun t ↦ stoppedValue B (fun ω ↦ τ ω + t) - stoppedValue B τ))
    (hshift : ∀ s : ℝ≥0,
      IsPreBrownianReal (fun u ω ↦ B ((τ ω + s).untopA + u) ω - B (τ ω + s).untopA ω) P ∧
        Indep (.comap (fun ω u ↦ B ((τ ω + s).untopA + u) ω - B (τ ω + s).untopA ω) inferInstance)
          (hτ.add_const_of_orderedSub s).measurableSpace P) :
    IsFilteredPreBrownianReal hτ.shiftFiltration
      (fun t ↦ stoppedValue B (fun ω ↦ τ ω + t) - stoppedValue B τ) P := by
  have h0 : ∀ᵐ ω ∂P, (stoppedValue B (fun ω' ↦ τ ω' + (0 : ℝ≥0)) - stoppedValue B τ) ω = 0 :=
    ae_of_all _ fun ω ↦ by simp [stoppedValue]
  have hae_inc {s t : ℝ≥0} (hst : s ≤ t) :
      (fun ω ↦ B ((τ ω + s).untopA + (t - s)) ω - B (τ ω + s).untopA ω) =ᵐ[P]
        (stoppedValue B (fun ω ↦ τ ω + t) - stoppedValue B τ) -
          (stoppedValue B (fun ω ↦ τ ω + s) - stoppedValue B τ) := by
    filter_upwards [hτ_ne_top] with ω hω
    cases hτ' : τ ω with
    | top => exact absurd hτ' hω
    | coe u =>
      simp only [Pi.sub_apply, stoppedValue, hτ', sub_sub_sub_cancel_right]
      change B (u + s + (t - s)) ω - B (u + s) ω = B (u + t) ω - B (u + s) ω
      rw [add_assoc, add_tsub_cancel_of_le hst]
  refine hadapt.isFilteredPreBrownianReal h0
    (fun s t hst ↦ ((hshift s).1.hasLaw_eval (t - s)).congr (hae_inc hst).symm)
    fun s t hst ↦ ?_
  have hind := indep_of_indep_of_le_left (hshift s).2
    (MeasurableSpace.comap_le_comap_pi
      (g := fun u ω ↦ B ((τ ω + s).untopA + u) ω - B (τ ω + s).untopA ω) (t - s))
  have hi : @IndepFun Ω ℝ Ω mΩ inferInstance (hτ.shiftFiltration s)
      (fun ω ↦ B ((τ ω + s).untopA + (t - s)) ω - B (τ ω + s).untopA ω) id P := by
    simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id, hτ.shiftFiltration_apply] using hind
  simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using
    hi.congr (hae_inc hst) Filter.EventuallyEq.rfl

/-! ### Countable-range stopping times -/

/-- At a countable-range stopping time, the shifted increment path of an adapted process is
jointly measurable in the product path space, with no path-continuity hypothesis. -/
theorem measurable_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) :
    Measurable fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω := by
  refine Measurable.of_eval fun t ↦ ?_
  have hct : (range fun ω ↦ τ ω + t).Countable :=
    Set.Countable.mono (by rintro _ ⟨ω, rfl⟩; exact ⟨τ ω, ⟨ω, rfl⟩, rfl⟩)
      (hc.image (· + (t : WithTop ℝ≥0)))
  have hm_add : Measurable (stoppedValue B fun ω ↦ τ ω + t) :=
    (hB.adapted.stronglyAdapted.stronglyMeasurable_stoppedValue_of_countable_range
      (hτ.add_const_of_orderedSub t) hct).measurable.mono
      (hτ.add_const_of_orderedSub t).measurableSpace_le le_rfl
  have hm_val : Measurable (stoppedValue B τ) :=
    (hB.adapted.stronglyAdapted.stronglyMeasurable_stoppedValue_of_countable_range
      hτ hc).measurable.mono hτ.measurableSpace_le le_rfl
  have hpiece : (fun ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) =
      {ω | τ ω = ⊤}.piecewise
        (fun ω ↦ B ((⊤ : WithTop ℝ≥0).untopA + t) ω - B (⊤ : WithTop ℝ≥0).untopA ω)
        (stoppedValue B (fun ω ↦ τ ω + t) - stoppedValue B τ) := by
    ext ω
    by_cases htop : τ ω = ⊤
    · simp [Set.piecewise, htop]
    · rw [Set.piecewise_eq_of_notMem {ω | τ ω = ⊤} _ _ htop, Pi.sub_apply,
        stoppedValue_add_const_of_ne_top B t htop, stoppedValue]
  rw [hpiece]
  exact Measurable.piecewise hτ.measurableSet_eq_top
    (hB.adapted.measurable.sub hB.adapted.measurable) (hm_add.sub hm_val)

/-- **Countable-range strong Markov restricted law.** For any countable-range `ℱ`-stopping time `τ`
and `A ∈ hτ.measurableSpace`, restricting to `A ∩ {τ ≠ ⊤}` pushes the shifted increment path
forward to `P (A ∩ {τ ≠ ⊤}) • P.map (fun ω t ↦ B t ω)`. Neither path continuity nor almost-sure
finiteness of `τ` is needed. -/
theorem map_restrict_shift_eq_smul_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) =
      P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω) := by
  let R : Set ℝ≥0 := {s | (s : WithTop ℝ≥0) ∈ range τ}
  have : Countable R := (hc.preimage WithTop.coe_injective).to_subtype
  let slice : R → Set Ω := fun s ↦ A ∩ {ω | τ ω = s.1}
  have hslice_F (s : R) : MeasurableSet[ℱ s.1] (slice s) :=
    (hτ.measurableSet_inter_eq_iff A s.1).1 (hA.inter (hτ.measurableSet_eq' s.1))
  have hslice_m (s : R) : MeasurableSet (slice s) := ℱ.le s.1 _ (hslice_F s)
  have hdisj : Pairwise (Function.onFun Disjoint slice) := fun i j hij ↦
    disjoint_left.2 fun ω (hi : ω ∈ slice i) (hj : ω ∈ slice j) ↦
      hij (Subtype.ext (WithTop.coe_injective (hi.2.symm.trans hj.2)))
  have hunion : A ∩ {ω | τ ω ≠ ⊤} = ⋃ s : R, slice s := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, slice]
    refine ⟨fun ⟨hAω, hne⟩ ↦ ?_, fun ⟨s, hAω, hs⟩ ↦ ⟨hAω, hs ▸ WithTop.coe_ne_top⟩⟩
    lift τ ω to ℝ≥0 using hne with s hs
    exact ⟨⟨s, ⟨ω, hs.symm⟩⟩, hAω, rfl⟩
  have hSm := hB.measurable_shift_of_countable_range hτ hc
  ext U hU
  rw [Measure.map_apply hSm hU, hunion, Measure.restrict_iUnion hdisj hslice_m,
    Measure.sum_apply _ (hSm hU), measure_iUnion hdisj hslice_m, smul_apply,
    smul_eq_mul, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun s ↦ ?_
  have hcongr : (P.restrict (slice s)).map (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) =
      (P.restrict (slice s)).map (fun ω t ↦ B (s.1 + t) ω - B s.1 ω) :=
    Measure.map_congr ((ae_restrict_mem (hslice_m s)).mono fun ω hω ↦
      funext fun t ↦ by dsimp only; rw [hω.2]; rfl)
  rw [← Measure.map_apply hSm hU, hcongr, hB.map_restrict_shift_eq_smul_const s.1 (hslice_F s),
    smul_apply, smul_eq_mul]

/-- At an almost-surely finite countable-range stopping time, the shifted increment path has the
same full path law as `B`. -/
theorem identDistrib_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IdentDistrib (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)
      (fun ω t ↦ B t ω) P P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (identDistrib_and_indep_of_map_restrict_eq_smul (m := hτ.measurableSpace)
    (hB.measurable_shift_of_countable_range hτ hc)
    (Measurable.of_eval fun _ ↦ hB.adapted.measurable).aemeasurable hτ_ne_top
    fun hA ↦ hB.map_restrict_shift_eq_smul_of_countable_range hτ hc hA).1

/-- At an almost-surely finite countable-range stopping time, the shifted increment process is
pre-Brownian. -/
theorem isPreBrownianReal_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsPreBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P :=
  hB.toIsPreBrownianReal.of_identDistrib
    (hB.identDistrib_shift_of_countable_range hτ hc hτ_ne_top)

/-- At an almost-surely finite countable-range stopping time, the shifted increment path is
independent of `hτ.measurableSpace`. -/
theorem indep_shift_of_countable_range (hB : IsFilteredPreBrownianReal ℱ B P)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep (.comap (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) inferInstance)
      hτ.measurableSpace P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (identDistrib_and_indep_of_map_restrict_eq_smul
    (hB.measurable_shift_of_countable_range hτ hc)
    (Measurable.of_eval fun _ ↦ hB.adapted.measurable).aemeasurable hτ_ne_top
    fun hA ↦ hB.map_restrict_shift_eq_smul_of_countable_range hτ hc hA).2

/-- At an almost-surely finite countable-range stopping time `τ`, the restarted process
`t ↦ stoppedValue B (τ + t) - stoppedValue B τ` is a filtered pre-Brownian motion relative to the
post-stopping filtration `hτ.shiftFiltration`. -/
theorem isFilteredPreBrownianReal_stoppedValue_sub_of_countable_range
    (hB : IsFilteredPreBrownianReal ℱ B P) (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsFilteredPreBrownianReal hτ.shiftFiltration
      (fun t ↦ stoppedValue B (fun ω ↦ τ ω + t) - stoppedValue B τ) P := by
  refine isFilteredPreBrownianReal_stoppedValue_sub_of_forall_shift hτ hτ_ne_top (fun t ↦ ?_)
    fun s ↦ ?_
  · rw [hτ.shiftFiltration_apply]
    have hct : (range fun ω ↦ τ ω + t).Countable :=
      Set.Countable.mono (by rintro _ ⟨ω, rfl⟩; exact ⟨τ ω, ⟨ω, rfl⟩, rfl⟩)
        (hc.image (· + (t : WithTop ℝ≥0)))
    exact ((hB.adapted.stronglyAdapted.stronglyMeasurable_stoppedValue_of_countable_range
      (hτ.add_const_of_orderedSub t) hct).sub
      ((hB.adapted.stronglyAdapted.stronglyMeasurable_stoppedValue_of_countable_range
        hτ hc).mono
        (hτ.measurableSpace_mono (hτ.add_const_of_orderedSub t) fun _ ↦ le_self_add))).measurable
  · have hcs : (range fun ω ↦ τ ω + s).Countable :=
      Set.Countable.mono (by rintro _ ⟨ω, rfl⟩; exact ⟨τ ω, ⟨ω, rfl⟩, rfl⟩)
        (hc.image (· + (s : WithTop ℝ≥0)))
    have hσ_ne : ∀ᵐ ω ∂P, τ ω + s ≠ ⊤ :=
      hτ_ne_top.mono fun ω hω ↦ WithTop.add_ne_top.2 ⟨hω, WithTop.coe_ne_top⟩
    exact ⟨hB.isPreBrownianReal_shift_of_countable_range (hτ.add_const_of_orderedSub s) hcs hσ_ne,
      hB.indep_shift_of_countable_range (hτ.add_const_of_orderedSub s) hcs hσ_ne⟩

/-! ### Strongly progressive right-continuous paths on `ℱ.rightCont` -/

/-- If `B` is strongly progressive on `ℱ` and `τ` is an `ℱ.rightCont`-stopping time, the shifted
increment path map is jointly measurable. -/
theorem measurable_shift_of_isStronglyProgressive (hprog : IsStronglyProgressive ℱ B)
    (hτ : IsStoppingTime ℱ.rightCont τ) :
    Measurable fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω := by
  have huncurry : Measurable (Function.uncurry B) := hprog.isProgressive.measurable
  have huntop : Measurable fun ω ↦ (τ ω).untopA := hτ.measurable'.untopA
  exact Measurable.of_eval fun t ↦
    (huncurry.comp ((huntop.add_const t).prodMk measurable_id)).sub
      (huncurry.comp (huntop.prodMk measurable_id))

private theorem tendsto_shift_dyadicCeilTime {ω : Ω} (hτ : τ ω ≠ ⊤)
    (hrc : IsRightContinuous (B · ω)) (t : ℝ≥0) :
    Tendsto (fun n ↦ B ((TauCeti.dyadicCeilTime n (τ ω)).untopA + t) ω -
        B (TauCeti.dyadicCeilTime n (τ ω)).untopA ω)
      atTop (𝓝 (B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)) := by
  have hd_lim := TauCeti.tendsto_dyadicCeilTime (τ ω)
  have huntop : Tendsto (fun n ↦ (TauCeti.dyadicCeilTime n (τ ω)).untopA)
      atTop (𝓝[≥] (τ ω).untopA) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(WithTop.tendsto_untopA hτ).comp hd_lim, ?_⟩
    filter_upwards [hd_lim.eventually (eventually_ne_nhds hτ)] with n hn
    exact WithTop.untopA_mono hn (TauCeti.le_dyadicCeilTime n (τ ω))
  have huntop_add : Tendsto (fun n ↦ (TauCeti.dyadicCeilTime n (τ ω)).untopA + t)
      atTop (𝓝[≥] ((τ ω).untopA + t)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_nhds_of_tendsto_nhdsWithin huntop).add_const t, ?_⟩
    filter_upwards [(tendsto_nhdsWithin_iff.1 huntop).2] with n (hn : (τ ω).untopA ≤ _)
    exact Set.mem_Ici.2 (by gcongr)
  exact ((continuousWithinAt_Ioi_iff_Ici.mp (hrc ((τ ω).untopA + t))).tendsto.comp huntop_add).sub
    ((continuousWithinAt_Ioi_iff_Ici.mp (hrc (τ ω).untopA)).tendsto.comp huntop)

/-- **Dyadic-approximation strong Markov restricted law.** For a strongly progressive `B` with
almost-surely right-continuous paths and any `ℱ.rightCont`-stopping time `τ`, restricting to
`A ∩ {τ ≠ ⊤}` pushes the shifted increment path forward to
`P (A ∩ {τ ≠ ⊤}) • P.map (fun ω t ↦ B t ω)`. -/
theorem map_restrict_shift_eq_smul_of_isStronglyProgressive_rightCont
    (hB : IsFilteredPreBrownianReal ℱ B P) (hprog : IsStronglyProgressive ℱ B)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) =
      P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  let E : Set Ω := A ∩ {ω | τ ω ≠ ⊤}
  have hEm : MeasurableSet E := (hτ.measurableSpace_le A hA).inter hτ.measurableSet_eq_top.compl
  have hB' : IsFilteredPreBrownianReal ℱ.rightCont B P :=
    hB.rightCont fun s ↦ hrc.mono fun _ hω ↦ hω s
  have hSm := measurable_shift_of_isStronglyProgressive hprog hτ
  let S_n (n : ℕ) : Ω → ℝ≥0 → ℝ := fun ω t ↦
    B ((TauCeti.dyadicCeilTime n (τ ω)).untopA + t) ω -
      B (TauCeti.dyadicCeilTime n (τ ω)).untopA ω
  have hSn_m (n : ℕ) : Measurable (S_n n) :=
    hB'.measurable_shift_of_countable_range (hτ.dyadicCeilTime n)
      (TauCeti.countable_range_dyadicCeilTime τ n)
  have hSn_law (n : ℕ) : (P.restrict E).map (S_n n) = P E • P.map (fun ω t ↦ B t ω) := by
    have hAn : MeasurableSet[(hτ.dyadicCeilTime n).measurableSpace] A :=
      hτ.measurableSpace_mono (hτ.dyadicCeilTime n)
        (fun ω ↦ TauCeti.le_dyadicCeilTime n (τ ω)) A hA
    simpa only [E, ne_eq, TauCeti.dyadicCeilTime_eq_top_iff] using
      hB'.map_restrict_shift_eq_smul_of_countable_range (hτ.dyadicCeilTime n)
        (TauCeti.countable_range_dyadicCeilTime τ n) hAn
  have : IsFiniteMeasure (P E • P.map (fun ω t ↦ B t ω)) :=
    Measure.smul_finite _ (measure_ne_top P E)
  refine IsProjectiveLimit.unique (P := fun I ↦ ((P.restrict E).map
      (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)).map I.restrict)
    (fun _ ↦ rfl) fun I ↦ (ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_).symm
  have hIm : Measurable (I.restrict (π := fun _ : ℝ≥0 ↦ ℝ)) := Finset.measurable_restrict I
  have hint_n (n : ℕ) : ∫ ω in E, f (I.restrict (S_n n ω)) ∂P =
      ∫ x, f x ∂((P E • P.map (fun ω t ↦ B t ω)).map I.restrict) := by
    rw [← hSn_law n, Measure.map_map hIm (hSn_m n),
      integral_map (hIm.comp (hSn_m n)).aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  dsimp only
  rw [Measure.map_map hIm hSm,
    integral_map (hIm.comp hSm).aemeasurable f.continuous.aestronglyMeasurable]
  refine tendsto_nhds_unique (tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖)
    (fun n ↦ (f.continuous.measurable.comp (hIm.comp (hSn_m n))).aestronglyMeasurable)
    (integrable_const ‖f‖) (fun n ↦ ae_of_all _ fun ω ↦ f.norm_coe_le_norm _) ?_)
    (tendsto_const_nhds.congr' (Eventually.of_forall fun n ↦ (hint_n n).symm))
  filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae hrc] with ω hωE hωrc
  exact f.continuous.tendsto _ |>.comp
    (tendsto_pi_nhds.mpr fun i ↦ tendsto_shift_dyadicCeilTime hωE.2 hωrc i.1)

/-- For a strongly progressive filtered pre-Brownian motion with almost-surely right-continuous
paths and an almost-surely finite `ℱ.rightCont`-stopping time `τ`, the restarted process
`t ↦ stoppedValue B (τ + t) - stoppedValue B τ` is a filtered pre-Brownian motion relative to
`hτ.shiftFiltration`. -/
theorem isFilteredPreBrownianReal_stoppedValue_sub_rightCont
    (hB : IsFilteredPreBrownianReal ℱ B P) (hprog : IsStronglyProgressive ℱ B)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsFilteredPreBrownianReal hτ.shiftFiltration
      (fun t ↦ stoppedValue B (fun ω ↦ τ ω + t) - stoppedValue B τ) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hprog' : IsStronglyProgressive ℱ.rightCont B :=
    fun t ↦ (hprog t).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont t))
  refine isFilteredPreBrownianReal_stoppedValue_sub_of_forall_shift hτ hτ_ne_top
    (fun t ↦ ?_) fun s ↦ ?_
  · rw [hτ.shiftFiltration_apply]
    exact (measurable_stoppedValue hprog' (hτ.add_const_of_orderedSub t)).sub
      ((measurable_stoppedValue hprog' hτ).mono
        (hτ.measurableSpace_mono (hτ.add_const_of_orderedSub t) fun _ ↦ le_self_add) le_rfl)
  · have hσ := hτ.add_const_of_orderedSub s
    have hσ_ne : ∀ᵐ ω ∂P, τ ω + s ≠ ⊤ :=
      hτ_ne_top.mono fun ω hω ↦ WithTop.add_ne_top.2 ⟨hω, WithTop.coe_ne_top⟩
    obtain ⟨hid, hind⟩ := identDistrib_and_indep_of_map_restrict_eq_smul
      (measurable_shift_of_isStronglyProgressive hprog hσ)
      (Measurable.of_eval fun _ ↦ hB.adapted.measurable).aemeasurable hσ_ne fun hA ↦
        map_restrict_shift_eq_smul_of_isStronglyProgressive_rightCont hB hprog hrc hσ hA
    exact ⟨hB.toIsPreBrownianReal.of_identDistrib hid, hind⟩

/-- Specialization of `isFilteredPreBrownianReal_stoppedValue_sub_rightCont` to an `ℱ`-stopping
time `τ`. -/
theorem isFilteredPreBrownianReal_stoppedValue_sub
    (hB : IsFilteredPreBrownianReal ℱ B P) (hprog : IsStronglyProgressive ℱ B)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsFilteredPreBrownianReal hτ.shiftFiltration
      (fun t ↦ stoppedValue B (fun ω ↦ τ ω + t) - stoppedValue B τ) P := by
  have hRC := hB.isFilteredPreBrownianReal_stoppedValue_sub_rightCont hprog hrc
    (hτ.mono_filtration ℱ.le_rightCont) hτ_ne_top
  refine ⟨hRC.toIsPreBrownianReal, fun t ↦ ?_, fun s t hst ↦ ?_⟩
  · rw [hτ.shiftFiltration_apply]
    exact (measurable_stoppedValue hprog (hτ.add_const_of_orderedSub t)).sub
      ((measurable_stoppedValue hprog hτ).mono
        (hτ.measurableSpace_mono (hτ.add_const_of_orderedSub t) fun _ ↦ le_self_add) le_rfl)
  · have hind := hRC.indep_sub hst
    rw [IsStoppingTime.shiftFiltration_apply] at hind ⊢
    exact indep_of_indep_of_le_right hind
      ((hτ.add_const_of_orderedSub s).measurableSpace_mono_filtration ℱ.le_rightCont)

/-! ### Strong Markov property on raw filtrations for almost-surely continuous paths -/

/-- At any `ℱ.rightCont`-stopping time `τ` (not necessarily finite), the shifted increment path of
a filtered pre-Brownian motion with almost-surely continuous paths is `P`-almost everywhere
measurable into `ℝ≥0 → ℝ`. -/
theorem aemeasurable_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) :
    AEMeasurable (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P := by
  obtain ⟨W, hWpred, -, -, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  exact (measurable_shift_of_isStronglyProgressive hWpred.isStronglyProgressive hτ).aemeasurable
    |>.congr (heq.mono fun ω hω ↦ funext fun t ↦ by simp [hω])

/-- Specialization of `aemeasurable_shift_rightCont` to an `ℱ`-stopping time `τ`. -/
theorem aemeasurable_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ) :
    AEMeasurable (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P :=
  hB.aemeasurable_shift_rightCont hc (hτ.mono_filtration ℱ.le_rightCont)

/-- **Restricted strong Markov law (`ℱ.rightCont`).** For a filtered pre-Brownian motion `B` with
almost-surely continuous paths, an arbitrary `ℱ.rightCont`-stopping time `τ`, and any event
`A ∈ hτ.measurableSpace`, restricting to `A ∩ {τ ≠ ⊤}` pushes the shifted increment path forward
to `P (A ∩ {τ ≠ ⊤}) • P.map (fun ω t ↦ B t ω)`, including when `P (A ∩ {τ ≠ ⊤}) = 0` or
`P {τ = ⊤} > 0`. -/
theorem map_restrict_shift_eq_smul_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) =
      P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω) := by
  obtain ⟨W, hWpred, hWB, hFW, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hrcW : ∀ᵐ ω ∂P, IsRightContinuous (W · ω) :=
    hWB.cont.mono fun _ hω _ ↦ hω.continuousAt.continuousWithinAt
  have hcongr_shift :
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) =
        (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map
          (fun ω t ↦ W ((τ ω).untopA + t) ω - W (τ ω).untopA ω) :=
    Measure.map_congr (ae_restrict_of_ae (heq.mono fun ω hω ↦ funext fun t ↦ by simp [hω]))
  have hcongr_path : P.map (fun ω t ↦ W t ω) = P.map (fun ω t ↦ B t ω) :=
    Measure.map_congr (heq.mono fun ω hω ↦ funext fun t ↦ hω t)
  rw [hcongr_shift, map_restrict_shift_eq_smul_of_isStronglyProgressive_rightCont hFW
    hWpred.isStronglyProgressive hrcW hτ hA, hcongr_path]

/-- **Restricted strong Markov law (`ℱ`).** Specialization of
`map_restrict_shift_eq_smul_rightCont` to an `ℱ`-stopping time `τ`. -/
theorem map_restrict_shift_eq_smul (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) =
      P (A ∩ {ω | τ ω ≠ ⊤}) • P.map (fun ω t ↦ B t ω) :=
  hB.map_restrict_shift_eq_smul_rightCont hc (hτ.mono_filtration ℱ.le_rightCont)
    (hτ.measurableSpace_mono_filtration ℱ.le_rightCont A hA)

/-- **Conditional strong Markov restart (`ℱ.rightCont`).** For any `ℱ.rightCont`-stopping time `τ`
(possibly infinite with positive probability) and any `A ∈ hτ.measurableSpace` with
`P (A ∩ {τ ≠ ⊤}) ≠ 0`, under the conditional probability `P[|A ∩ {τ ≠ ⊤}]` the restarted increment
process `t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω` is a standard Brownian motion. -/
theorem isBrownianReal_shift_cond_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hcA : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)
      (P[|A ∩ {ω | τ ω ≠ ⊤}]) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  let E : Set Ω := A ∩ {ω | τ ω ≠ ⊤}
  have hSaem : AEMeasurable (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P :=
    hB.aemeasurable_shift_rightCont hc hτ
  have hmap : (P[|E]).map (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) =
      P.map (fun ω t ↦ B t ω) := by
    rw [ProbabilityTheory.cond, Measure.map_smul _ hSaem.restrict,
      hB.map_restrict_shift_eq_smul_rightCont hc hτ hA, smul_smul,
      ENNReal.inv_mul_cancel hcA (measure_ne_top P E), one_smul]
  refine ⟨hB.toIsPreBrownianReal.of_identDistrib
    ⟨hSaem.mono_ac cond_absolutelyContinuous,
      (Measurable.of_eval fun _ ↦ hB.adapted.measurable).aemeasurable, hmap⟩, ?_⟩
  exact cond_absolutelyContinuous.ae_le (hc.mono fun ω hω ↦ by fun_prop)

/-- **Conditional strong Markov restart (`ℱ`).** Specialization of
`isBrownianReal_shift_cond_rightCont` to an `ℱ`-stopping time `τ`. -/
theorem isBrownianReal_shift_cond (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hcA : P (A ∩ {ω | τ ω ≠ ⊤}) ≠ 0) :
    IsBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)
      (P[|A ∩ {ω | τ ω ≠ ⊤}]) :=
  hB.isBrownianReal_shift_cond_rightCont hc (hτ.mono_filtration ℱ.le_rightCont)
    (hτ.measurableSpace_mono_filtration ℱ.le_rightCont A hA) hcA

/-- At an almost-surely finite `ℱ.rightCont`-stopping time `τ`, the restarted increment path has
the same distribution on `ℝ≥0 → ℝ` as `B`. -/
theorem identDistrib_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IdentDistrib (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)
      (fun ω t ↦ B t ω) P P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨hrest, hmeas⟩ := restrict_eq_of_ae_ne_top (E := univ) hτ_ne_top
  have hmap := hB.map_restrict_shift_eq_smul_rightCont hc hτ MeasurableSet.univ
  rw [hrest, Measure.restrict_univ, hmeas, measure_univ, one_smul] at hmap
  exact ⟨hB.aemeasurable_shift_rightCont hc hτ,
    (Measurable.of_eval fun _ ↦ hB.adapted.measurable).aemeasurable, hmap⟩

/-- At an almost-surely finite `ℱ.rightCont`-stopping time `τ`, the restarted increment process
is a standard Brownian motion. -/
theorem isBrownianReal_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.of_identDistrib
    (hB.identDistrib_shift_rightCont hc hτ hτ_ne_top)
  cont := hc.mono fun ω hω ↦ by fun_prop

/-- At an almost-surely finite `ℱ.rightCont`-stopping time `τ`, the entire restarted increment
path is independent of `hτ.measurableSpace` (`ℱ_{τ+}`). -/
theorem indep_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep (.comap (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) inferInstance)
      hτ.measurableSpace P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWpred, hWB, hFW, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hrcW : ∀ᵐ ω ∂P, IsRightContinuous (W · ω) :=
    hWB.cont.mono fun _ hω _ ↦ hω.continuousAt.continuousWithinAt
  have hindW := (identDistrib_and_indep_of_map_restrict_eq_smul
    (measurable_shift_of_isStronglyProgressive hWpred.isStronglyProgressive hτ)
    (Measurable.of_eval fun _ ↦ hFW.adapted.measurable).aemeasurable hτ_ne_top fun hA ↦
      map_restrict_shift_eq_smul_of_isStronglyProgressive_rightCont hFW
        hWpred.isStronglyProgressive hrcW hτ hA).2
  have hae : (fun ω t ↦ W ((τ ω).untopA + t) ω - W (τ ω).untopA ω) =ᵐ[P]
      fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω :=
    heq.mono fun ω hω ↦ funext fun t ↦ by simp [hω]
  have hi : @IndepFun Ω (ℝ≥0 → ℝ) Ω mΩ inferInstance hτ.measurableSpace
      (fun ω t ↦ W ((τ ω).untopA + t) ω - W (τ ω).untopA ω) id P := by
    simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hindW
  simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using
    hi.congr hae Filter.EventuallyEq.rfl

/-- **Strong Markov property (`ℱ.rightCont`).** At an almost-surely finite `ℱ.rightCont`-stopping
time `τ`, the restarted increment process `t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω` is a
Brownian motion independent of `hτ.measurableSpace`. -/
theorem strongMarkov_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P ∧
      Indep (.comap (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) inferInstance)
        hτ.measurableSpace P :=
  ⟨hB.isBrownianReal_shift_rightCont hc hτ hτ_ne_top,
    hB.indep_shift_rightCont hc hτ hτ_ne_top⟩

/-- At an almost-surely finite `ℱ`-stopping time `τ`, the restarted increment path has the same
distribution on `ℝ≥0 → ℝ` as `B`. -/
theorem identDistrib_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IdentDistrib (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)
      (fun ω t ↦ B t ω) P P :=
  hB.identDistrib_shift_rightCont hc (hτ.mono_filtration ℱ.le_rightCont) hτ_ne_top

/-- At an almost-surely finite `ℱ`-stopping time `τ`, the restarted increment process is a
standard Brownian motion. -/
theorem isBrownianReal_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P :=
  hB.isBrownianReal_shift_rightCont hc (hτ.mono_filtration ℱ.le_rightCont) hτ_ne_top

/-- At an almost-surely finite `ℱ`-stopping time `τ`, the entire restarted increment path is
independent of `hτ.measurableSpace`. -/
theorem indep_shift (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep (.comap (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) inferInstance)
      hτ.measurableSpace P :=
  indep_of_indep_of_le_right
    (hB.indep_shift_rightCont hc (hτ.mono_filtration ℱ.le_rightCont) hτ_ne_top)
    (hτ.measurableSpace_mono_filtration ℱ.le_rightCont)

/-- **Strong Markov property (`ℱ`).** At an almost-surely finite `ℱ`-stopping time `τ` on an
arbitrary raw filtration `ℱ`, the restarted increment process is a Brownian motion independent of
`hτ.measurableSpace`. -/
theorem strongMarkov (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P ∧
      Indep (.comap (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) inferInstance)
        hτ.measurableSpace P :=
  ⟨hB.isBrownianReal_shift hc hτ hτ_ne_top, hB.indep_shift hc hτ hτ_ne_top⟩

/-! ### Joint stopped-position/increment laws and transition-kernel expectations -/

/-- For a strongly progressive `B` with almost-surely right-continuous paths, restricted to
`A ∩ {τ ≠ ⊤}` for `A ∈ hτ.measurableSpace`, the joint law of `stoppedValue B τ` and the restarted
increment path factors as the product of `(P.restrict (A ∩ {τ ≠ ⊤})).map (stoppedValue B τ)` and
`P.map (fun ω t ↦ B t ω)`. -/
theorem map_restrict_stoppedValue_prodMk_shift_eq_prod_of_isStronglyProgressive_rightCont
    (hB : IsFilteredPreBrownianReal ℱ B P) (hprog : IsStronglyProgressive ℱ B)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map
        (fun ω ↦ (stoppedValue B τ ω, fun t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)) =
      ((P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue B τ)).prod
        (P.map (fun ω t ↦ B t ω)) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hprog' : IsStronglyProgressive ℱ.rightCont B :=
    fun t ↦ (hprog t).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont t))
  have hX_m : Measurable[hτ.measurableSpace] (stoppedValue B τ) := measurable_stoppedValue hprog' hτ
  have hX_m' : Measurable (stoppedValue B τ) := hX_m.mono hτ.measurableSpace_le le_rfl
  have hS_m := measurable_shift_of_isStronglyProgressive hprog hτ
  let E : Set Ω := A ∩ {ω | τ ω ≠ ⊤}
  have hEm : MeasurableSet E := (hτ.measurableSpace_le A hA).inter hτ.measurableSet_eq_top.compl
  refine (Measure.prod_eq fun U V hU hV ↦ ?_).symm
  have hAU : MeasurableSet[hτ.measurableSpace] (A ∩ stoppedValue B τ ⁻¹' U) := hA.inter (hX_m hU)
  have hstep := congrArg (fun μ ↦ μ V)
    (map_restrict_shift_eq_smul_of_isStronglyProgressive_rightCont hB hprog hrc hτ hAU)
  have hAU_ne : MeasurableSet ((A ∩ stoppedValue B τ ⁻¹' U) ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hAU).inter hτ.measurableSet_eq_top.compl
  rw [Measure.map_apply hS_m hV, Measure.restrict_apply' hAU_ne, smul_apply, smul_eq_mul] at hstep
  rw [Measure.map_apply (hX_m'.prodMk hS_m) (hU.prod hV), Measure.map_apply hX_m' hU,
    Measure.restrict_apply' hEm, Measure.restrict_apply' hEm, mk_preimage_prod]
  have hset1 : (stoppedValue B τ ⁻¹' U ∩
      (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) ⁻¹' V) ∩ E =
      (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) ⁻¹' V ∩
        ((A ∩ stoppedValue B τ ⁻¹' U) ∩ {ω | τ ω ≠ ⊤}) := by ext ω; simp [E]; tauto
  have hset2 : stoppedValue B τ ⁻¹' U ∩ E = (A ∩ stoppedValue B τ ⁻¹' U) ∩ {ω | τ ω ≠ ⊤} := by
    ext ω; simp [E]; tauto
  rw [hset1, hset2, hstep]

/-- Restricted to `A ∩ {τ ≠ ⊤}` for `A ∈ hτ.measurableSpace`, the joint law of `stoppedValue B τ`
and the restarted increment path is the product of
`(P.restrict (A ∩ {τ ≠ ⊤})).map (stoppedValue B τ)` and the path law `P.map (fun ω t ↦ B t ω)`,
without assuming `τ` is almost surely finite. -/
theorem map_restrict_stoppedValue_prodMk_shift_eq_prod_rightCont
    (hB : IsFilteredPreBrownianReal ℱ B P) (hc : ∀ᵐ ω ∂P, Continuous (B · ω))
    (hτ : IsStoppingTime ℱ.rightCont τ) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map
        (fun ω ↦ (stoppedValue B τ ω, fun t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)) =
      ((P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue B τ)).prod
        (P.map (fun ω t ↦ B t ω)) := by
  obtain ⟨W, hWpred, hWB, hFW, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hrcW : ∀ᵐ ω ∂P, IsRightContinuous (W · ω) :=
    hWB.cont.mono fun _ hω _ ↦ hω.continuousAt.continuousWithinAt
  let E : Set Ω := A ∩ {ω | τ ω ≠ ⊤}
  have hcongr_pair : (P.restrict E).map
      (fun ω ↦ (stoppedValue B τ ω, fun t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)) =
      (P.restrict E).map
        (fun ω ↦ (stoppedValue W τ ω, fun t ↦ W ((τ ω).untopA + t) ω - W (τ ω).untopA ω)) :=
    Measure.map_congr (ae_restrict_of_ae (heq.mono fun ω hω ↦
      Prod.ext (by simp [stoppedValue, hω]) (funext fun t ↦ by simp [hω])))
  have hcongr_X : (P.restrict E).map (stoppedValue B τ) = (P.restrict E).map (stoppedValue W τ) :=
    Measure.map_congr (ae_restrict_of_ae (heq.mono fun ω hω ↦ by simp [stoppedValue, hω]))
  have hcongr_path : P.map (fun ω t ↦ W t ω) = P.map (fun ω t ↦ B t ω) :=
    Measure.map_congr (heq.mono fun ω hω ↦ funext fun t ↦ hω t)
  rw [hcongr_pair,
    map_restrict_stoppedValue_prodMk_shift_eq_prod_of_isStronglyProgressive_rightCont hFW
      hWpred.isStronglyProgressive hrcW hτ hA, hcongr_X, hcongr_path]

/-- Restricted to `A ∩ {τ ≠ ⊤}` for `A ∈ hτ.measurableSpace`, the joint law of `stoppedValue B τ`
and a single increment `B ((τ ω).untopA + t) ω - B (τ ω).untopA ω` is the product of
`(P.restrict (A ∩ {τ ≠ ⊤})).map (stoppedValue B τ)` and `gaussianReal 0 t`. -/
theorem map_restrict_stoppedValue_prodMk_shift_eval_eq_prod_rightCont
    (hB : IsFilteredPreBrownianReal ℱ B P) (hc : ∀ᵐ ω ∂P, Continuous (B · ω))
    (hτ : IsStoppingTime ℱ.rightCont τ) (t : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map
        (fun ω ↦ (stoppedValue B τ ω, B ((τ ω).untopA + t) ω - B (τ ω).untopA ω)) =
      ((P.restrict (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedValue B τ)).prod (gaussianReal 0 t) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hXB_aem : AEMeasurable (stoppedValue B τ) P := by
    obtain ⟨W, hWpred, -, -, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
    have hprog' : IsStronglyProgressive ℱ.rightCont W := fun u ↦
      (hWpred.isStronglyProgressive u).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont u))
    exact ((measurable_stoppedValue hprog' hτ).mono hτ.measurableSpace_le le_rfl).aemeasurable.congr
      (heq.mono fun ω hω ↦ by simp [stoppedValue, hω])
  have hSB_aem := hB.aemeasurable_shift_rightCont hc hτ
  have hBm : Measurable fun ω u ↦ B u ω := Measurable.of_eval fun _ ↦ hB.adapted.measurable
  have hmap := congrArg (fun μ ↦ μ.map (Prod.map id (Function.eval t)))
    (hB.map_restrict_stoppedValue_prodMk_shift_eq_prod_rightCont hc hτ hA)
  rw [AEMeasurable.map_map_of_aemeasurable
    (measurable_id.prodMap (measurable_pi_apply t)).aemeasurable
    (hXB_aem.restrict.prodMk hSB_aem.restrict),
    ← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply t), Measure.map_id,
    Measure.map_map (measurable_pi_apply t) hBm] at hmap
  simpa only [Prod.map_apply, id_eq, Function.comp_def, (hB.hasLaw_eval t).map_eq] using hmap

private theorem exists_stoppedValue_shift_indep_indist_rightCont
    (hB : IsFilteredPreBrownianReal ℱ B P) (hc : ∀ᵐ ω ∂P, Continuous (B · ω))
    (hτ : IsStoppingTime ℱ.rightCont τ) (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∃ (X : Ω → ℝ) (S : Ω → ℝ≥0 → ℝ),
      Measurable[hτ.measurableSpace] X ∧ Measurable S ∧
      Indep (.comap S inferInstance) hτ.measurableSpace P ∧
      P.map S = P.map (fun ω' u ↦ B u ω') ∧
      (∀ᵐ ω ∂P, stoppedValue B τ ω = X ω ∧
        (fun u ↦ B ((τ ω).untopA + u) ω - B (τ ω).untopA ω) = S ω) := by
  obtain ⟨W, hWpred, hWB, hFW, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hprog' : IsStronglyProgressive ℱ.rightCont W := fun u ↦
    (hWpred.isStronglyProgressive u).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont u))
  refine ⟨stoppedValue W τ, fun ω u ↦ W ((τ ω).untopA + u) ω - W (τ ω).untopA ω,
    measurable_stoppedValue hprog' hτ,
    measurable_shift_of_isStronglyProgressive hWpred.isStronglyProgressive hτ,
    hFW.indep_shift_rightCont hWB.cont hτ hτ_ne_top,
    (hFW.identDistrib_shift_rightCont hWB.cont hτ hτ_ne_top).map_eq.trans
      (Measure.map_congr (heq.mono fun ω hω ↦ funext fun u ↦ hω u)),
    heq.mono fun ω hω ↦ ⟨by simp [stoppedValue, hω], funext fun u ↦ by simp [hω]⟩⟩

/-- **Full-path nonnegative conditional-expectation freezing (`ℱ.rightCont`).** At an
almost-surely finite `ℱ.rightCont`-stopping time `τ`, the nonnegative conditional expectation of
any measurable functional
`f (stoppedValue B τ ω, fun u ↦ B ((τ ω).untopA + u) ω - B (τ ω).untopA ω)` given
`hτ.measurableSpace` freezes `stoppedValue B τ` and integrates over the Wiener path law. -/
theorem condLExp_stoppedValue_shift_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {f : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    P⁻[fun ω ↦ f (stoppedValue B τ ω, fun u ↦ B ((τ ω).untopA + u) ω - B (τ ω).untopA ω) |
        hτ.measurableSpace] =ᵐ[P]
      fun ω ↦ ∫⁻ w, f (stoppedValue B τ ω, w) ∂(P.map fun ω' u ↦ B u ω') := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨X, S, hXm, hSm, hind, hmap, hae⟩ :=
    hB.exists_stoppedValue_shift_indep_indist_rightCont hc hτ hτ_ne_top
  have hae_in : (fun ω ↦ f (stoppedValue B τ ω,
      fun u ↦ B ((τ ω).untopA + u) ω - B (τ ω).untopA ω)) =ᵐ[P] fun ω ↦ f (X ω, S ω) :=
    hae.mono fun ω ⟨hX, hS⟩ ↦ congrArg f (Prod.ext hX hS)
  refine (condLExp_congr_ae hae_in).trans
    ((TauCeti.Probability.condLExp_comp_prodMk_ae_eq_lintegral_of_indep
      hτ.measurableSpace_le hXm hSm hind hf).trans ?_)
  filter_upwards [hae] with ω ⟨hX, _⟩
  rw [hmap, hX]

/-- **Full-path Bochner conditional-expectation freezing (`ℱ.rightCont`).** At an almost-surely
finite `ℱ.rightCont`-stopping time `τ`, the conditional expectation of an integrable Banach-valued
functional `f (stoppedValue B τ ω, fun u ↦ B ((τ ω).untopA + u) ω - B (τ ω).untopA ω)` given
`hτ.measurableSpace` freezes `stoppedValue B τ` and integrates against the Wiener path law. -/
theorem condExp_stoppedValue_shift_rightCont {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {f : ℝ × (ℝ≥0 → ℝ) → E} (hf : StronglyMeasurable f)
    (hint : Integrable (fun ω ↦ f (stoppedValue B τ ω,
      fun u ↦ B ((τ ω).untopA + u) ω - B (τ ω).untopA ω)) P) :
    P[fun ω ↦ f (stoppedValue B τ ω, fun u ↦ B ((τ ω).untopA + u) ω - B (τ ω).untopA ω) |
        hτ.measurableSpace] =ᵐ[P]
      fun ω ↦ ∫ w, f (stoppedValue B τ ω, w) ∂(P.map fun ω' u ↦ B u ω') := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨X, S, hXm, hSm, hind, hmap, hae⟩ :=
    hB.exists_stoppedValue_shift_indep_indist_rightCont hc hτ hτ_ne_top
  have hae_in : (fun ω ↦ f (stoppedValue B τ ω,
      fun u ↦ B ((τ ω).untopA + u) ω - B (τ ω).untopA ω)) =ᵐ[P] fun ω ↦ f (X ω, S ω) :=
    hae.mono fun ω ⟨hX, hS⟩ ↦ congrArg f (Prod.ext hX hS)
  refine (condExp_congr_ae hae_in).trans
    ((TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep
      hτ.measurableSpace_le hXm hSm hind hf (hint.congr hae_in)).trans ?_)
  filter_upwards [hae] with ω ⟨hX, _⟩
  rw [hmap, hX]

/-- **Restricted Tonelli transition-kernel formula on `A ∩ {τ ≠ ⊤}`.** For any measurable
`g : ℝ → ℝ≥0∞` and any `ℱ.rightCont`-stopping time `τ` (not necessarily a.s. finite), integrating
`g (B ((τ ω).untopA + t) ω)` over `A ∩ {τ ≠ ⊤}` equals integrating its Gaussian heat-kernel
evaluation at `stoppedValue B τ ω`. -/
theorem setLIntegral_shift_eval_eq_lintegral_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) (t : ℝ≥0)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, g (B ((τ ω).untopA + t) ω) ∂P =
      ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, ∫⁻ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t ∂P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWpred, hWB, hFW, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hprog' : IsStronglyProgressive ℱ.rightCont W := fun u ↦
    (hWpred.isStronglyProgressive u).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont u))
  have hXW : Measurable (stoppedValue W τ) :=
    (measurable_stoppedValue hprog' hτ).mono hτ.measurableSpace_le le_rfl
  have hYW : Measurable fun ω ↦ W ((τ ω).untopA + t) ω - W (τ ω).untopA ω :=
    (measurable_pi_apply t).comp (measurable_shift_of_isStronglyProgressive
      hWpred.isStronglyProgressive hτ)
  let E : Set Ω := A ∩ {ω | τ ω ≠ ⊤}
  have hEm : MeasurableSet E := (hτ.measurableSpace_le A hA).inter hτ.measurableSet_eq_top.compl
  have hprod := hFW.map_restrict_stoppedValue_prodMk_shift_eval_eq_prod_rightCont hWB.cont hτ t hA
  have hcongrL : ∫⁻ ω in E, g (B ((τ ω).untopA + t) ω) ∂P =
      ∫⁻ ω in E, g (stoppedValue W τ ω + (W ((τ ω).untopA + t) ω - W (τ ω).untopA ω)) ∂P :=
    setLIntegral_congr_fun_ae hEm
      (heq.mono fun ω hω _ ↦ by simp [stoppedValue, hω, add_sub_cancel])
  have hcongrR : ∫⁻ ω in E, ∫⁻ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t ∂P =
      ∫⁻ ω in E, ∫⁻ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t ∂P :=
    setLIntegral_congr_fun_ae hEm (heq.mono fun ω hω _ ↦ by simp [stoppedValue, hω])
  exact hcongrL.trans
    ((TauCeti.Probability.setLIntegral_comp_prodMk_eq_setLIntegral_lintegral_of_map_restrict_eq_prod
      hXW hYW hprod (hg.comp measurable_add)).trans hcongrR)

/-- **Nonnegative Gaussian transition-kernel identity (`ℱ.rightCont`).** For any
`ℱ.rightCont`-stopping time `τ` (possibly infinite with positive probability) and measurable
`g : ℝ → ℝ≥0∞`, the nonnegative conditional expectation of
`{τ ≠ ⊤}.indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω))` given `hτ.measurableSpace` is almost
everywhere `{τ ≠ ⊤}.indicator (fun ω ↦ ∫⁻ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t)`. -/
theorem condLExp_indicator_shift_eval_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) (t : ℝ≥0)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    P⁻[{ω | τ ω ≠ ⊤}.indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω)) | hτ.measurableSpace] =ᵐ[P]
      {ω | τ ω ≠ ⊤}.indicator
        (fun ω ↦ ∫⁻ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWpred, -, -, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hprog' : IsStronglyProgressive ℱ.rightCont W := fun u ↦
    (hWpred.isStronglyProgressive u).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont u))
  have hne_τ : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    ((measurableSet_singleton ⊤).preimage hτ.measurable).compl
  have hne_m : MeasurableSet {ω | τ ω ≠ ⊤} := hτ.measurableSpace_le _ hne_τ
  have hker_m : Measurable[hτ.measurableSpace] ({ω | τ ω ≠ ⊤}.indicator
      fun ω ↦ ∫⁻ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t) :=
    (((hg.comp measurable_add).lintegral_prod_right').comp
      (measurable_stoppedValue hprog' hτ)).indicator hne_τ
  refine (ae_eq_condLExp hτ.measurableSpace_le P _ hker_m fun A hA ↦ ?_).symm.trans ?_
  · rw [setLIntegral_indicator hne_m, setLIntegral_indicator hne_m, inter_comm {ω | τ ω ≠ ⊤} A,
      hB.setLIntegral_shift_eval_eq_lintegral_rightCont hc hτ t hg hA]
    exact setLIntegral_congr_fun_ae ((hτ.measurableSpace_le A hA).inter hne_m)
      (heq.mono fun ω hω _ ↦ by simp [stoppedValue, hω])
  · filter_upwards [heq] with ω hω
    by_cases h : τ ω ≠ ⊤ <;> simp [h, stoppedValue, hω]

/-- Specialization of `condLExp_indicator_shift_eval_rightCont` to an almost-surely finite
`ℱ.rightCont`-stopping time `τ`. -/
theorem condLExp_shift_eval_rightCont (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (t : ℝ≥0) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    P⁻[fun ω ↦ g (B ((τ ω).untopA + t) ω) | hτ.measurableSpace] =ᵐ[P]
      fun ω ↦ ∫⁻ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t := by
  have haeL : (fun ω ↦ g (B ((τ ω).untopA + t) ω)) =ᵐ[P]
      {ω | τ ω ≠ ⊤}.indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω)) :=
    hτ_ne_top.mono fun ω hω ↦ by simp [hω]
  have haeR : ({ω | τ ω ≠ ⊤}.indicator
      fun ω ↦ ∫⁻ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t) =ᵐ[P]
      fun ω ↦ ∫⁻ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t :=
    hτ_ne_top.mono fun ω hω ↦ by simp [hω]
  exact (condLExp_congr_ae haeL).trans
    ((hB.condLExp_indicator_shift_eval_rightCont hc hτ t hg).trans haeR)

/-- Specialization of `condLExp_shift_eval_rightCont` to an almost-surely finite `ℱ`-stopping
time `τ`. -/
theorem condLExp_shift_eval (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (t : ℝ≥0) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    P⁻[fun ω ↦ g (B ((τ ω).untopA + t) ω) | hτ.measurableSpace] =ᵐ[P]
      fun ω ↦ ∫⁻ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  let hτ' := hτ.mono_filtration ℱ.le_rightCont
  obtain ⟨W, hWpred, -, -, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hker_m : Measurable[hτ.measurableSpace]
      (fun ω ↦ ∫⁻ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t) :=
    ((hg.comp measurable_add).lintegral_prod_right').comp
      (measurable_stoppedValue hWpred.isStronglyProgressive hτ)
  have htower := TauCeti.MeasureTheory.condLExp_condLExp_of_le (P := P)
    (X := fun ω ↦ g (B ((τ ω).untopA + t) ω))
    (hτ.measurableSpace_mono_filtration ℱ.le_rightCont) hτ'.measurableSpace_le
  have hrc : P⁻[fun ω ↦ g (B ((τ ω).untopA + t) ω) | hτ'.measurableSpace] =ᵐ[P]
      fun ω ↦ ∫⁻ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t :=
    (hB.condLExp_shift_eval_rightCont hc hτ' hτ_ne_top t hg).trans
      (heq.mono fun ω hω ↦ by simp [stoppedValue, ← hω])
  refine htower.symm.trans ((condLExp_congr_ae hrc).trans ?_)
  exact (ae_eq_condLExp hτ.measurableSpace_le P _ hker_m fun _ _ ↦ rfl).symm.trans
    (heq.mono fun ω hω ↦ by simp [stoppedValue, hω])

/-- **Restricted Fubini transition-kernel formula on `A ∩ {τ ≠ ⊤}`.** Whenever `g : ℝ → E` is
strongly measurable and `ω ↦ g (B ((τ ω).untopA + t) ω)` is integrable on `A ∩ {τ ≠ ⊤}` for
`A ∈ hτ.measurableSpace`, the Gaussian heat-kernel evaluation
`ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t` is also integrable on `A ∩ {τ ≠ ⊤}` with
the same set integral. -/
theorem setIntegral_shift_eval_eq_setIntegral_integral_rightCont {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) (t : ℝ≥0)
    {g : ℝ → E} (hg : StronglyMeasurable g) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hint : IntegrableOn (fun ω ↦ g (B ((τ ω).untopA + t) ω)) (A ∩ {ω | τ ω ≠ ⊤}) P) :
    IntegrableOn (fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t)
        (A ∩ {ω | τ ω ≠ ⊤}) P ∧
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t ∂P =
        ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (B ((τ ω).untopA + t) ω) ∂P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWpred, hWB, hFW, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hprog' : IsStronglyProgressive ℱ.rightCont W := fun u ↦
    (hWpred.isStronglyProgressive u).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont u))
  have hXW : Measurable (stoppedValue W τ) :=
    (measurable_stoppedValue hprog' hτ).mono hτ.measurableSpace_le le_rfl
  have hYW : Measurable fun ω ↦ W ((τ ω).untopA + t) ω - W (τ ω).untopA ω :=
    (measurable_pi_apply t).comp (measurable_shift_of_isStronglyProgressive
      hWpred.isStronglyProgressive hτ)
  let E₀ : Set Ω := A ∩ {ω | τ ω ≠ ⊤}
  have hEm : MeasurableSet E₀ := (hτ.measurableSpace_le A hA).inter hτ.measurableSet_eq_top.compl
  have hae_in : (fun ω ↦ g (B ((τ ω).untopA + t) ω)) =ᵐ[P.restrict E₀]
      fun ω ↦ g (stoppedValue W τ ω + (W ((τ ω).untopA + t) ω - W (τ ω).untopA ω)) :=
    (ae_restrict_of_ae heq).mono fun ω hω ↦ by simp [stoppedValue, hω, add_sub_cancel]
  have hae_ker : (fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t) =ᵐ[P.restrict E₀]
      fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t :=
    (ae_restrict_of_ae heq).mono fun ω hω ↦ by simp [stoppedValue, hω]
  obtain ⟨hint_ker, hset_eq⟩ :=
    TauCeti.Probability.setIntegral_comp_prodMk_eq_setIntegral_integral_of_map_restrict_eq_prod
      hXW hYW (hFW.map_restrict_stoppedValue_prodMk_shift_eval_eq_prod_rightCont hWB.cont hτ t hA)
      (hg.comp_measurable measurable_add) (hint.congr_fun_ae hae_in)
  refine ⟨hint_ker.congr_fun_ae hae_ker, ?_⟩
  exact (setIntegral_congr_ae hEm (heq.mono fun ω hω _ ↦ by simp [stoppedValue, ← hω])).trans
    (hset_eq.trans (setIntegral_congr_ae hEm
      (heq.mono fun ω hω _ ↦ by simp [stoppedValue, hω, add_sub_cancel])))

/-- **Localized Bochner Gaussian transition-kernel identity (`ℱ.rightCont`).** On any stopping
event `D ∈ hτ.measurableSpace` such that
`(D ∩ {τ ≠ ⊤}).indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω))` is integrable, its conditional
expectation given `hτ.measurableSpace` is given on `D ∩ {τ ≠ ⊤}` by integrating
`g (stoppedValue B τ ω + ·)` against `gaussianReal 0 t`. -/
theorem condExp_inter_ne_top_indicator_shift_eval_rightCont {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) (t : ℝ≥0)
    {g : ℝ → E} (hg : StronglyMeasurable g) {D : Set Ω} (hD : MeasurableSet[hτ.measurableSpace] D)
    (hint : Integrable ((D ∩ {ω | τ ω ≠ ⊤}).indicator fun ω ↦ g (B ((τ ω).untopA + t) ω)) P) :
    P[(D ∩ {ω | τ ω ≠ ⊤}).indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω)) |
        hτ.measurableSpace] =ᵐ[P]
      (D ∩ {ω | τ ω ≠ ⊤}).indicator
        (fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWpred, -, -, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hprog' : IsStronglyProgressive ℱ.rightCont W := fun u ↦
    (hWpred.isStronglyProgressive u).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont u))
  let E₀ : Set Ω := D ∩ {ω | τ ω ≠ ⊤}
  have hE₀_τ : MeasurableSet[hτ.measurableSpace] E₀ :=
    hD.inter ((measurableSet_singleton ⊤).preimage hτ.measurable).compl
  have hE₀_m : MeasurableSet E₀ := hτ.measurableSpace_le _ hE₀_τ
  have hker_sm : StronglyMeasurable[hτ.measurableSpace]
      (E₀.indicator fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t) :=
    (((hg.comp_measurable measurable_add).integral_prod_right').comp_measurable
      (measurable_stoppedValue hprog' hτ)).indicator hE₀_τ
  have hcell (C : Set Ω) (hC : MeasurableSet[hτ.measurableSpace] C) :
      IntegrableOn (E₀.indicator fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t) C P ∧
        ∫ ω in C, E₀.indicator (fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t) ω ∂P =
          ∫ ω in C, E₀.indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω)) ω ∂P := by
    have hint_B : IntegrableOn (fun ω ↦ g (B ((τ ω).untopA + t) ω))
        ((C ∩ D) ∩ {ω | τ ω ≠ ⊤}) P := by
      have h := hint.integrableOn (s := C)
      rwa [integrableOn_indicator_iff hE₀_m.nullMeasurableSet, inter_comm, ← inter_assoc] at h
    obtain ⟨hint_ker, hset_eq⟩ :=
      hB.setIntegral_shift_eval_eq_setIntegral_integral_rightCont hc hτ t hg (hC.inter hD) hint_B
    have hae_W : (fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t) =ᵐ[P.restrict (C ∩ E₀)]
        fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t :=
      (ae_restrict_of_ae heq).mono fun ω hω ↦ by simp [stoppedValue, hω]
    have hint_kerW : IntegrableOn (fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t)
        (E₀ ∩ C) P := by
      rw [inter_comm]; exact (inter_assoc C D {ω | τ ω ≠ ⊤} ▸ hint_ker).congr_fun_ae hae_W
    refine ⟨(integrableOn_indicator_iff hE₀_m.nullMeasurableSet).2 hint_kerW, ?_⟩
    rw [setIntegral_indicator hE₀_m, setIntegral_indicator hE₀_m, ← inter_assoc, ← hset_eq]
    exact setIntegral_congr_ae ((hτ.measurableSpace_le (C ∩ D) (hC.inter hD)).inter
      hτ.measurableSet_eq_top.compl) (heq.mono fun ω hω _ ↦ by simp [stoppedValue, ← hω])
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hint
    (fun C hC _ ↦ (hcell C hC).1) (fun C hC _ ↦ (hcell C hC).2)
    hker_sm.aestronglyMeasurable).symm.trans ?_
  filter_upwards [heq] with ω hω
  by_cases h : ω ∈ E₀ <;> simp [E₀, h, stoppedValue, hω]

/-- Specialization of `condExp_inter_ne_top_indicator_shift_eval_rightCont` to `{τ ≠ ⊤}`: when
`{τ ≠ ⊤}.indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω))` is integrable, its conditional expectation
given `hτ.measurableSpace` is `{τ ≠ ⊤}.indicator` of the Gaussian heat-kernel integral at
`stoppedValue B τ`. -/
theorem condExp_indicator_shift_eval_rightCont {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) (t : ℝ≥0)
    {g : ℝ → E} (hg : StronglyMeasurable g)
    (hint : Integrable ({ω | τ ω ≠ ⊤}.indicator fun ω ↦ g (B ((τ ω).untopA + t) ω)) P) :
    P[{ω | τ ω ≠ ⊤}.indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω)) | hτ.measurableSpace] =ᵐ[P]
      {ω | τ ω ≠ ⊤}.indicator (fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t) := by
  simpa only [univ_inter] using
    hB.condExp_inter_ne_top_indicator_shift_eval_rightCont hc hτ t hg MeasurableSet.univ
      (by simpa only [univ_inter] using hint)

/-- At an almost-surely finite `ℱ.rightCont`-stopping time `τ`, the conditional expectation of an
integrable observable `g (B ((τ ω).untopA + t) ω)` given `hτ.measurableSpace` is given almost
everywhere by integrating `g (stoppedValue B τ ω + ·)` against `gaussianReal 0 t`. -/
theorem condExp_shift_eval_rightCont {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (t : ℝ≥0) {g : ℝ → E} (hg : StronglyMeasurable g)
    (hint : Integrable (fun ω ↦ g (B ((τ ω).untopA + t) ω)) P) :
    P[fun ω ↦ g (B ((τ ω).untopA + t) ω) | hτ.measurableSpace] =ᵐ[P]
      fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t := by
  have haeL : (fun ω ↦ g (B ((τ ω).untopA + t) ω)) =ᵐ[P]
      {ω | τ ω ≠ ⊤}.indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω)) :=
    hτ_ne_top.mono fun ω hω ↦ by simp [hω]
  have haeR : ({ω | τ ω ≠ ⊤}.indicator
      fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t) =ᵐ[P]
      fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t :=
    hτ_ne_top.mono fun ω hω ↦ by simp [hω]
  exact (condExp_congr_ae haeL).trans
    ((hB.condExp_indicator_shift_eval_rightCont hc hτ t hg (hint.congr haeL)).trans haeR)

/-- Specialization of `condExp_shift_eval_rightCont` to an almost-surely finite `ℱ`-stopping time
`τ` on an arbitrary raw filtration `ℱ`. -/
theorem condExp_shift_eval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (t : ℝ≥0) {g : ℝ → E} (hg : StronglyMeasurable g)
    (hint : Integrable (fun ω ↦ g (B ((τ ω).untopA + t) ω)) P) :
    P[fun ω ↦ g (B ((τ ω).untopA + t) ω) | hτ.measurableSpace] =ᵐ[P]
      fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  let hτ' := hτ.mono_filtration ℱ.le_rightCont
  obtain ⟨W, hWpred, -, -, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hker_sm : StronglyMeasurable[hτ.measurableSpace]
      (fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t) :=
    ((hg.comp_measurable measurable_add).integral_prod_right').comp_measurable
      (measurable_stoppedValue hWpred.isStronglyProgressive hτ)
  have hrc : P[fun ω ↦ g (B ((τ ω).untopA + t) ω) | hτ'.measurableSpace] =ᵐ[P]
      fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t :=
    (hB.condExp_shift_eval_rightCont hc hτ' hτ_ne_top t hg hint).trans
      (heq.mono fun ω hω ↦ by simp [stoppedValue, ← hω])
  have hint_ker : Integrable (fun ω ↦ ∫ y, g (stoppedValue W τ ω + y) ∂gaussianReal 0 t) P :=
    integrable_condExp.congr hrc
  refine (condExp_condExp_of_le (hτ.measurableSpace_mono_filtration ℱ.le_rightCont)
    hτ'.measurableSpace_le).symm.trans ((condExp_congr_ae hrc).trans ?_)
  rw [condExp_of_stronglyMeasurable hτ.measurableSpace_le hker_sm hint_ker]
  exact heq.mono fun ω hω ↦ by simp [stoppedValue, hω]

private theorem integrable_inter_ne_top_indicator_shift_eval_of_lintegral_le_rightCont
    {E : Type*} [NormedAddCommGroup E] (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (B · ω)) (hτ : IsStoppingTime ℱ.rightCont τ) (t : ℝ≥0)
    {g : ℝ → E} (hg : StronglyMeasurable g) {D : Set Ω} (hD : MeasurableSet[hτ.measurableSpace] D)
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hle : ∀ᵐ ω ∂P, ω ∈ D ∩ {ω | τ ω ≠ ⊤} →
      ∫⁻ y, ‖g (stoppedValue B τ ω + y)‖ₑ ∂gaussianReal 0 t ≤ K) :
    Integrable ((D ∩ {ω | τ ω ≠ ⊤}).indicator fun ω ↦ g (B ((τ ω).untopA + t) ω)) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWpred, -, -, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hEm : MeasurableSet (D ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hD).inter
      (show MeasurableSet {ω | τ ω ≠ ⊤} from hτ.measurableSet_eq_top.compl)
  have huncurry : Measurable (Function.uncurry W) :=
    hWpred.isStronglyProgressive.isProgressive.measurable
  have haesm : AEStronglyMeasurable
      ((D ∩ {ω | τ ω ≠ ⊤}).indicator fun ω ↦ g (B ((τ ω).untopA + t) ω)) P :=
    ((hg.comp_measurable (huncurry.comp ((hτ.measurable'.untopA.add_const t).prodMk
      measurable_id))).indicator hEm).aestronglyMeasurable.congr
      (heq.mono fun ω hω ↦ by by_cases h : ω ∈ D ∩ {ω | τ ω ≠ ⊤} <;> simp [h, hω])
  refine ⟨haesm, hasFiniteIntegral_iff_eNorm.2 ?_⟩
  have hind_eq : ∫⁻ ω, ‖(D ∩ {ω | τ ω ≠ ⊤}).indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω)) ω‖ₑ ∂P =
      ∫⁻ ω in D ∩ {ω | τ ω ≠ ⊤}, ‖g (B ((τ ω).untopA + t) ω)‖ₑ ∂P := by
    rw [← lintegral_indicator hEm (fun ω ↦ ‖g (B ((τ ω).untopA + t) ω)‖ₑ)]
    exact lintegral_congr fun ω ↦ by by_cases h : ω ∈ D ∩ {ω | τ ω ≠ ⊤} <;> simp [h]
  rw [hind_eq, hB.setLIntegral_shift_eval_eq_lintegral_rightCont hc hτ t hg.eNorm hD]
  exact (setLIntegral_mono_ae measurable_const.aemeasurable hle).trans_lt
    (by rw [setLIntegral_const]; exact ENNReal.mul_lt_top hK.lt_top (measure_lt_top P _))

/-- **Exhausting localized transition-kernel identity (`ℱ.rightCont`).** Whenever `g : ℝ → E` is
strongly measurable and `y ↦ g (z + y)` is integrable under `gaussianReal 0 t` at every fixed
starting point `z : ℝ` (without requiring `g (B ((τ ω).untopA + t) ω)` to be globally
`P`-integrable), there is an increasing sequence of `hτ.measurableSpace`-measurable events `A n`
covering `Ω` on each of which `(A n ∩ {τ ≠ ⊤}).indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω))` is
`P`-integrable and has conditional expectation given by the Gaussian heat kernel at
`stoppedValue B τ`. -/
theorem exists_measurableSet_condExp_indicator_shift_eval_rightCont {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hB : IsFilteredPreBrownianReal ℱ B P) (hc : ∀ᵐ ω ∂P, Continuous (B · ω))
    (hτ : IsStoppingTime ℱ.rightCont τ) (t : ℝ≥0) {g : ℝ → E} (hg : StronglyMeasurable g)
    (hg_int : ∀ z : ℝ, Integrable (fun y ↦ g (z + y)) (gaussianReal 0 t)) :
    ∃ A : ℕ → Set Ω, (∀ n, MeasurableSet[hτ.measurableSpace] (A n)) ∧ Monotone A ∧
      (⋃ n, A n) = univ ∧
      ∀ n, Integrable ((A n ∩ {ω | τ ω ≠ ⊤}).indicator fun ω ↦ g (B ((τ ω).untopA + t) ω)) P ∧
        P[(A n ∩ {ω | τ ω ≠ ⊤}).indicator (fun ω ↦ g (B ((τ ω).untopA + t) ω)) |
            hτ.measurableSpace] =ᵐ[P]
          (A n ∩ {ω | τ ω ≠ ⊤}).indicator
            (fun ω ↦ ∫ y, g (stoppedValue B τ ω + y) ∂gaussianReal 0 t) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWpred, -, -, heq⟩ := hB.exists_isStronglyPredictable_isBrownianReal_indist hc
  have hprog' : IsStronglyProgressive ℱ.rightCont W := fun u ↦
    (hWpred.isStronglyProgressive u).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le_rightCont u))
  let q : ℝ → ℝ≥0∞ := fun z ↦ ∫⁻ y, ‖g (z + y)‖ₑ ∂gaussianReal 0 t
  have hqm : Measurable q := (hg.comp_measurable measurable_add).eNorm.lintegral_prod_right'
  have hXW_τ : Measurable[hτ.measurableSpace] (stoppedValue W τ) :=
    measurable_stoppedValue hprog' hτ
  let A : ℕ → Set Ω := fun n ↦ {ω | τ ω = ⊤} ∪ {ω | q (stoppedValue W τ ω) ≤ n}
  have hAm (n : ℕ) : MeasurableSet[hτ.measurableSpace] (A n) :=
    ((measurableSet_singleton ⊤).preimage hτ.measurable).union
      (measurableSet_Iic.preimage (hqm.comp hXW_τ))
  have hmono : Monotone A := fun m n hmn ω hω ↦
    hω.imp id fun (h : q (stoppedValue W τ ω) ≤ m) ↦ h.trans (Nat.cast_le.2 hmn)
  have hcover : (⋃ n, A n) = univ := eq_univ_of_forall fun ω ↦ by
    obtain ⟨n, hn⟩ := exists_nat_ge (q (stoppedValue W τ ω)).toReal
    have hqn : q (stoppedValue W τ ω) ≤ n :=
      ((ENNReal.le_ofReal_iff_toReal_le (hg_int _).2.ne
        (Nat.cast_nonneg n)).2 hn).trans_eq (ENNReal.ofReal_natCast n)
    exact mem_iUnion.2 ⟨n, Or.inr hqn⟩
  refine ⟨A, hAm, hmono, hcover, fun n ↦ ?_⟩
  have hint_n := hB.integrable_inter_ne_top_indicator_shift_eval_of_lintegral_le_rightCont
    hc hτ t hg (hAm n) (ENNReal.natCast_ne_top n)
    (heq.mono fun ω hω ⟨hωA, hωne⟩ ↦ by
      rcases hωA with htop | (hq : q (stoppedValue W τ ω) ≤ n)
      · exact absurd htop hωne
      · simpa only [q, stoppedValue, hω] using hq)
  exact ⟨hint_n, hB.condExp_inter_ne_top_indicator_shift_eval_rightCont hc hτ t hg (hAm n) hint_n⟩

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {τ : Ω → WithTop ℝ≥0}

/-- At an almost-surely finite stopping time `τ` of `(Filtration.natural B hmeas).rightCont`, the
restarted increment process of a standard Brownian motion `B` is again a Brownian motion
independent of `hτ.measurableSpace`. -/
theorem strongMarkov_rightCont_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas).rightCont τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P ∧
      Indep (.comap (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) inferInstance)
        hτ.measurableSpace P :=
  (hB.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hmeas).strongMarkov_rightCont
    hB.cont hτ hτ_ne_top

/-- At an almost-surely finite stopping time `τ` of the raw natural filtration
`Filtration.natural B hmeas`, the restarted increment process of `B` is a Brownian motion
independent of `hτ.measurableSpace`. -/
theorem strongMarkov_natural (hB : IsBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t))
    (hτ : IsStoppingTime (Filtration.natural B hmeas) τ)
    (hτ_ne_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsBrownianReal (fun t ω ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) P ∧
      Indep (.comap (fun ω t ↦ B ((τ ω).untopA + t) ω - B (τ ω).untopA ω) inferInstance)
        hτ.measurableSpace P :=
  (hB.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hmeas).strongMarkov
    hB.cont hτ hτ_ne_top

end ProbabilityTheory.IsBrownianReal
