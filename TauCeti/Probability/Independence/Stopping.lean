/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Order.Cadlag
import TauCeti.Probability.HasLaw
import TauCeti.Probability.Independence.Basic
import TauCeti.Probability.Process.StoppedValue
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Law and independence of processes sampled at a stopping time

Suppose a family of random variables `(U s)_{s}` shares a common law `ν` and each `U s` is
independent of the filtration slice `ℱ s`. Sampling `U` at a stopping time `τ` preserves both
properties without requiring ambient measurability beyond the almost-everywhere measurability
carried by `HasLaw`: on every event `A ∈ hτ.measurableSpace`, the restriction to `A ∩ {τ ≠ ⊤}`
pushes `stoppedValue U τ` forward to `P (A ∩ {τ ≠ ⊤}) • ν`. When `τ` is almost surely finite,
`stoppedValue U τ` has law `ν` under a probability measure and is independent of
`hτ.measurableSpace` under any zero or probability measure.

The countable-range case decomposes `A ∩ {τ ≠ ⊤}` along the countably many level sets `{τ = s}`,
requiring neither a topology on time nor any regularity of `U`. For nonnegative real times,
upward dyadic approximations pass the restricted law to right-continuous families taking values
in a pseudo-metrizable Borel space, on arbitrary raw filtrations. Specializing `U s` to the
shifted increment path `t ↦ X (s + t) ω - X s ω` gives the full path-space law and independence of
the restarted increment process `t ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω`.

## Main declarations

* `IsStoppingTime.hasLaw_restrict_stoppedValue_of_countable_range`,
  `IsStoppingTime.hasLaw_stoppedValue_of_countable_range`, and
  `IsStoppingTime.indep_stoppedValue_of_countable_range`: law and independence at countable-range
  stopping times over a partial order.
* `IsStoppingTime.hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue_of_countable_range`,
  `IsStoppingTime.hasLaw_stoppedValue_add_const_sub_stoppedValue_of_countable_range`, and
  `IsStoppingTime.indep_stoppedValue_add_const_sub_stoppedValue_of_countable_range`: restarted
  increment path laws and independence at countable-range stopping times.
* `IsStoppingTime.hasLaw_restrict_stoppedValue`,
  `IsStoppingTime.hasLaw_stoppedValue`, and
  `IsStoppingTime.indep_stoppedValue`: law and independence for right-continuous families indexed
  by `ℝ≥0` at arbitrary stopping times.
* `IsStoppingTime.hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue`,
  `IsStoppingTime.hasLaw_stoppedValue_add_const_sub_stoppedValue`, and
  `IsStoppingTime.indep_stoppedValue_add_const_sub_stoppedValue`: restarted increment path laws and
  independence for right-continuous group-valued processes indexed by `ℝ≥0`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.6.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.IsStoppingTime

open ProbabilityTheory

section CountableRange

variable {ι Ω β : Type*} [PartialOrder ι] [Nonempty ι] {mΩ : MeasurableSpace Ω}
  [MeasurableSpace β] {ℱ : Filtration ι mΩ} {P : Measure Ω} {ν : Measure β}
  {U : ι → Ω → β} {τ : Ω → WithTop ι}

private lemma hasLaw_restrict_stoppedValue_of_countable_range_of_measurable
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) (hm : ∀ s, Measurable (U s))
    (hlaw : ∀ s, HasLaw (U s) ν P) (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (stoppedValue U τ) (P (A ∩ {ω | τ ω ≠ ⊤}) • ν)
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  let R : Set ι := {s | (s : WithTop ι) ∈ range τ}
  have hR : R.Countable := hc.preimage WithTop.coe_injective
  have hslice (s : ι) : MeasurableSet[ℱ s] (A ∩ {ω | τ ω = s}) := by
    have hs : MeasurableSet[hτ.measurableSpace] {ω | τ ω = s} := by
      rw [← univ_inter {ω | τ ω = s}, hτ.measurableSet_inter_eq_iff, univ_inter]
      exact hτ.measurableSet_eq_of_countable_range hc s
    exact (hτ.measurableSet_inter_eq_iff A s).1 (hA.inter hs)
  have hslice_meas (s : ι) : MeasurableSet (A ∩ {ω | τ ω = s}) := ℱ.le s _ (hslice s)
  have hdecomp : A ∩ {ω | τ ω ≠ ⊤} = ⋃ s ∈ R, A ∩ {ω | τ ω = s} := by
    ext ω
    cases h : τ ω with
    | top => simp [h]
    | coe s => simpa [h, R] using fun _ ↦ (⟨ω, h⟩ : ∃ y, τ y = (s : WithTop ι))
  have hdisj : R.PairwiseDisjoint (fun s ↦ A ∩ {ω | τ ω = s}) :=
    fun s _ t _ hst ↦ disjoint_left.2 fun ω hs ht ↦
      hst (WithTop.coe_injective (hs.2.symm.trans ht.2))
  have hZ : Measurable (stoppedValue U τ) := hτ.measurable_stoppedValue_of_countable_range hc hm
  refine ⟨hZ.aemeasurable, Measure.ext fun C hC ↦ ?_⟩
  rw [Measure.map_apply hZ hC, Measure.restrict_apply (hZ hC)]
  have hpre : stoppedValue U τ ⁻¹' C ∩ (A ∩ {ω | τ ω ≠ ⊤}) =
      ⋃ s ∈ R, U s ⁻¹' C ∩ (A ∩ {ω | τ ω = s}) := by
    ext ω
    cases h : τ ω with
    | top => simp [h]
    | coe s =>
      simp only [stoppedValue_of_eq h, h, mem_inter_iff, mem_preimage, mem_ofPred_eq, ne_eq,
        WithTop.coe_ne_top, not_false_eq_true, and_true, mem_iUnion, WithTop.coe_inj, exists_prop,
        R, mem_range]
      exact ⟨fun ⟨hCω, hAω⟩ ↦ ⟨s, ⟨ω, h⟩, hCω, hAω, rfl⟩,
        fun ⟨t, _, hCω, hAω, hst⟩ ↦ ⟨by simpa [hst] using hCω, hAω⟩⟩
  have hdisj_pre : R.PairwiseDisjoint (fun s ↦ U s ⁻¹' C ∩ (A ∩ {ω | τ ω = s})) :=
    fun s hs t ht hst ↦ (hdisj hs ht hst).mono inter_subset_right inter_subset_right
  have hfactor (s : ι) : P (U s ⁻¹' C ∩ (A ∩ {ω | τ ω = s})) = ν C * P (A ∩ {ω | τ ω = s}) := by
    rw [(Indep_iff _ _ _).1 (hind s) _ _ ⟨C, hC, rfl⟩ (hslice s),
      ← Measure.map_apply (hm s) hC, (hlaw s).map_eq]
  rw [hpre, measure_biUnion hR hdisj_pre fun s _ ↦ (hm s hC).inter (hslice_meas s)]
  simp only [hfactor, ENNReal.tsum_mul_left]
  rw [← measure_biUnion hR hdisj fun s _ ↦ hslice_meas s, ← hdecomp, smul_apply, smul_eq_mul,
    mul_comm]

/-- At a countable-range stopping time `τ`, if each `U s` has law `ν` and is independent of `ℱ s`,
then on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace` the stopped value `stoppedValue U τ` has
law `P (A ∩ {τ ≠ ⊤}) • ν`. -/
theorem hasLaw_restrict_stoppedValue_of_countable_range (hτ : IsStoppingTime ℱ τ)
    (hc : (range τ).Countable) (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (stoppedValue U τ) (P (A ∩ {ω | τ ω ≠ ⊤}) • ν)
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  let U' (s : ι) : Ω → β := (hlaw s).aemeasurable.mk (U s)
  have hm' (s : ι) : Measurable (U' s) := (hlaw s).aemeasurable.measurable_mk
  have hlaw' (s : ι) : HasLaw (U' s) ν P := (hlaw s).congr (hlaw s).aemeasurable.ae_eq_mk.symm
  have hind' (s : ι) : Indep (.comap (U' s) inferInstance) (ℱ s) P := by
    rw [Indep_iff]
    rintro _ B ⟨C, hC, rfl⟩ hB
    have hpre : (U' s ⁻¹' C : Set Ω) =ᵐ[P] U s ⁻¹' C :=
      (hlaw s).aemeasurable.ae_eq_mk.mono fun ω hω ↦ by simp [U', hω]
    rw [measure_congr (hpre.inter .rfl), measure_congr hpre]
    exact (Indep_iff _ _ _).1 (hind s) _ B ⟨C, hC, rfl⟩ hB
  refine (hτ.hasLaw_restrict_stoppedValue_of_countable_range_of_measurable hc hm' hlaw' hind'
    hA).congr ?_
  have hR : {s : ι | (s : WithTop ι) ∈ range τ}.Countable := hc.preimage WithTop.coe_injective
  have hA'_meas : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    hτ.measurableSpace_le _ (hA.inter (hτ.measurableSet_eq_top_of_countable_range hc).compl)
  filter_upwards [ae_restrict_of_ae ((ae_ball_iff hR).2 fun s _ ↦ (hlaw s).aemeasurable.ae_eq_mk),
    ae_restrict_of_forall_mem hA'_meas fun _ hω ↦ hω.2] with ω hω hfin
  cases h : τ ω with
  | top => exact absurd h hfin
  | coe s =>
    rw [stoppedValue_of_eq h, stoppedValue_of_eq h]
    exact hω s ⟨ω, h⟩

/-- At an almost-surely finite stopping time with countable range, a family sharing a law `ν` with
each slice independent of `ℱ s` retains the law `ν`. -/
theorem hasLaw_stoppedValue_of_countable_range [IsProbabilityMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hc : (range τ).Countable) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) :
    HasLaw (stoppedValue U τ) ν P := by
  have hrest : HasLaw (stoppedValue U τ) (P {ω | τ ω ≠ ⊤} • ν) (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using hτ.hasLaw_restrict_stoppedValue_of_countable_range hc hlaw hind .univ
  exact hrest.of_restrict_of_ae_mem hfin

/-- Under a zero or probability measure, at an almost-surely finite stopping time with countable
range, a family sharing a law `ν` with each slice independent of `ℱ s` has stopped value
independent of `hτ.measurableSpace`. -/
theorem indep_stoppedValue_of_countable_range [IsZeroOrProbabilityMeasure P]
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) :
    Indep (.comap (stoppedValue U τ) inferInstance) hτ.measurableSpace P :=
  indep_comap_of_forall_hasLaw_restrict_inter hτ.measurableSpace_le hfin fun _ hA ↦
    hτ.hasLaw_restrict_stoppedValue_of_countable_range hc hlaw hind hA

/-- At a countable-range stopping time `τ`, if every deterministic shifted increment path
`t ↦ X (s + t) ω - X s ω` shares a path-space law `ν` and is independent of `ℱ s`, then on
`A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace` the restarted increment path has law
`P (A ∩ {τ ≠ ⊤}) • ν`. -/
theorem hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue_of_countable_range
    {E : Type*} [Add ι] [MeasurableSpace E] [Sub E] {ν : Measure (ι → E)} {X : ι → Ω → E}
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    (hlaw : ∀ s, HasLaw (fun ω t ↦ X (s + t) ω - X s ω) ν P)
    (hind : ∀ s, Indep (.comap (fun ω t ↦ X (s + t) ω - X s ω) inferInstance) (ℱ s) P)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (fun ω (t : ι) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω)
      (P (A ∩ {ω | τ ω ≠ ⊤}) • ν) (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  have hA'_meas : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    hτ.measurableSpace_le _ (hA.inter (hτ.measurableSet_eq_top_of_countable_range hc).compl)
  refine (hτ.hasLaw_restrict_stoppedValue_of_countable_range hc hlaw hind hA).congr ?_
  filter_upwards [ae_restrict_of_forall_mem hA'_meas fun _ hω ↦ hω.2] with ω hω
  funext t
  exact stoppedValue_add_const_sub_stoppedValue (u := X) (τ := τ) t hω

/-- At an almost-surely finite stopping time with countable range, if every deterministic shifted
increment path `t ↦ X (s + t) ω - X s ω` shares a path-space law `ν` and is independent of `ℱ s`,
then the restarted increment path retains the law `ν`. -/
theorem hasLaw_stoppedValue_add_const_sub_stoppedValue_of_countable_range
    {E : Type*} [Add ι] [MeasurableSpace E] [Sub E] [IsProbabilityMeasure P]
    {ν : Measure (ι → E)} {X : ι → Ω → E} (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hlaw : ∀ s, HasLaw (fun ω t ↦ X (s + t) ω - X s ω) ν P)
    (hind : ∀ s, Indep (.comap (fun ω t ↦ X (s + t) ω - X s ω) inferInstance) (ℱ s) P) :
    HasLaw (fun ω (t : ι) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω) ν P := by
  have hrest :
      HasLaw (fun ω (t : ι) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω)
        (P {ω | τ ω ≠ ⊤} • ν) (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using
      hτ.hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue_of_countable_range hc hlaw hind
        .univ
  exact hrest.of_restrict_of_ae_mem hfin

/-- Under a zero or probability measure, at an almost-surely finite stopping time with countable
range, if every deterministic shifted increment path `t ↦ X (s + t) ω - X s ω` shares a path-space
law `ν` and is independent of `ℱ s`, then the restarted increment path is independent of
`hτ.measurableSpace`. -/
theorem indep_stoppedValue_add_const_sub_stoppedValue_of_countable_range
    {E : Type*} [Add ι] [MeasurableSpace E] [Sub E] [IsZeroOrProbabilityMeasure P]
    {ν : Measure (ι → E)} {X : ι → Ω → E} (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hlaw : ∀ s, HasLaw (fun ω t ↦ X (s + t) ω - X s ω) ν P)
    (hind : ∀ s, Indep (.comap (fun ω t ↦ X (s + t) ω - X s ω) inferInstance) (ℱ s) P) :
    Indep
      (.comap (fun ω (t : ι) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω)
        inferInstance)
      hτ.measurableSpace P :=
  indep_comap_of_forall_hasLaw_restrict_inter hτ.measurableSpace_le hfin fun _ hA ↦
    hτ.hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue_of_countable_range hc hlaw hind hA

end CountableRange

section NNReal

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace β]
  [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
  {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} {ν : Measure β}
  {U : ℝ≥0 → Ω → β} {τ : Ω → WithTop ℝ≥0}

/-- At an arbitrary stopping time `τ` on a filtration indexed by `ℝ≥0`, an almost-surely
right-continuous family into a pseudo-metrizable Borel space with common law `ν` and slices
independent of `ℱ s` has restricted law `P (A ∩ {τ ≠ ⊤}) • ν` on `A ∩ {τ ≠ ⊤}` for every
`A ∈ hτ.measurableSpace`. -/
theorem hasLaw_restrict_stoppedValue [IsFiniteMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ U t ω)) (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (stoppedValue U τ) (P (A ∩ {ω | τ ω ≠ ⊤}) • ν)
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  let A' : Set Ω := A ∩ {ω | τ ω ≠ ⊤}
  have hA' : MeasurableSet[hτ.measurableSpace] A' :=
    hA.inter ((measurableSet_singleton ⊤).preimage hτ.measurable).compl
  have hstep (n : ℕ) :
      HasLaw (stoppedValue U (fun ω ↦ TauCeti.dyadicCeilTime n (τ ω)))
        (P A' • ν) (P.restrict A') := by
    have hσ := hτ.dyadicCeilTime n
    have hA'σ : MeasurableSet[hσ.measurableSpace] A' :=
      hτ.measurableSpace_mono hσ (fun ω ↦ TauCeti.le_dyadicCeilTime n (τ ω)) _ hA'
    have hinter : A' ∩ {ω | TauCeti.dyadicCeilTime n (τ ω) ≠ ⊤} = A' :=
      inter_eq_left.2 fun ω hω ↦ (TauCeti.dyadicCeilTime_eq_top_iff n (τ ω)).not.2 hω.2
    have hraw := hσ.hasLaw_restrict_stoppedValue_of_countable_range
      (TauCeti.countable_range_dyadicCeilTime τ n) hlaw hind hA'σ
    rwa [hinter] at hraw
  refine HasLaw.of_ae_tendsto_metrizable (l := atTop) (Eventually.of_forall hstep) ?_
  filter_upwards [ae_restrict_of_ae hrc, ae_restrict_mem (hτ.measurableSpace_le _ hA')]
    with ω hω hωA'
  exact TauCeti.tendsto_stoppedValue_dyadicCeilTime U τ ω hωA'.2
    ((isRightContinuous_iff_continuousWithinAt_Ici.1 hω) _)

/-- At an almost-surely finite stopping time on a filtration indexed by `ℝ≥0`, an almost-surely
right-continuous family into a pseudo-metrizable Borel space sharing law `ν` with slices
independent of `ℱ s` retains law `ν`. -/
theorem hasLaw_stoppedValue [IsProbabilityMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ U t ω))
    (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) :
    HasLaw (stoppedValue U τ) ν P := by
  have hrest : HasLaw (stoppedValue U τ) (P {ω | τ ω ≠ ⊤} • ν) (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using hτ.hasLaw_restrict_stoppedValue hrc hlaw hind .univ
  exact hrest.of_restrict_of_ae_mem hfin

/-- Under a zero or probability measure, at an almost-surely finite stopping time on a filtration
indexed by `ℝ≥0`, an almost-surely right-continuous family into a pseudo-metrizable Borel space
sharing law `ν` with slices independent of `ℱ s` has stopped value independent of
`hτ.measurableSpace`. -/
theorem indep_stoppedValue [IsZeroOrProbabilityMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ U t ω))
    (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) :
    Indep (.comap (stoppedValue U τ) inferInstance) hτ.measurableSpace P :=
  indep_comap_of_forall_hasLaw_restrict_inter hτ.measurableSpace_le hfin fun _ hA ↦
    hτ.hasLaw_restrict_stoppedValue hrc hlaw hind hA

/-- At an arbitrary stopping time `τ` on a filtration indexed by `ℝ≥0`, for an almost-surely
right-continuous process `X` into a second-countable pseudo-metrizable Borel additive group with
continuous subtraction whose deterministic shifted increment paths share a law `ν` and are
independent of `ℱ s`, restricting `P` to `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace` gives the
restarted increment path law `P (A ∩ {τ ≠ ⊤}) • ν`. -/
theorem hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [TopologicalSpace.PseudoMetrizableSpace E] [AddGroup E] [ContinuousSub E]
    [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasure P]
    {ν : Measure (ℝ≥0 → E)} {X : ℝ≥0 → Ω → E} (hτ : IsStoppingTime ℱ τ)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    (hlaw : ∀ s, HasLaw (fun ω t ↦ X (s + t) ω - X s ω) ν P)
    (hind : ∀ s, Indep (.comap (fun ω t ↦ X (s + t) ω - X s ω) inferInstance) (ℱ s) P)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω)
      (P (A ∩ {ω | τ ω ≠ ⊤}) • ν) (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  have hX_ae :=
    (hτ.aemeasurable_stoppedValue_add_const_sub_stoppedValue
      (fun s ↦ (hlaw s).aemeasurable) hrc).restrict (s := A ∩ {ω | τ ω ≠ ⊤})
  refine (hasLaw_pi_iff_forall_finset_restrict hX_ae).2 fun I ↦ ?_
  let U : ℝ≥0 → Ω → (I → E) := fun s ω i ↦ X (s + i.val) ω - X s ω
  have hU_rc : ∀ᵐ ω ∂P, IsRightContinuous (fun s ↦ U s ω) := by
    filter_upwards [hrc] with ω hω s
    exact continuousWithinAt_pi.2 fun i ↦
      ((hω (s + i.val)).comp (f := fun u : ℝ≥0 ↦ u + i.val) (s := Ioi s) (by fun_prop)
        fun u (hu : s < u) ↦ add_lt_add_of_lt_of_le hu le_rfl).sub (hω s)
  have hU_law (s : ℝ≥0) : HasLaw (U s) (ν.map I.restrict) P :=
    (hasLaw_map I.measurable_restrict.aemeasurable).comp (hlaw s)
  have hU_ind (s : ℝ≥0) : Indep (.comap (U s) inferInstance) (ℱ s) P := by
    refine indep_of_indep_of_le_left (hind s) ?_
    have hcomp : U s = I.restrict ∘ fun ω t ↦ X (s + t) ω - X s ω := rfl
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono I.measurable_restrict.comap_le
  have hA'_meas : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter hτ.measurableSet_eq_top.compl
  rw [Measure.map_smul (hf := I.measurable_restrict.aemeasurable)]
  refine (hτ.hasLaw_restrict_stoppedValue hU_rc hU_law hU_ind hA).congr ?_
  filter_upwards [ae_restrict_of_forall_mem hA'_meas fun _ hω ↦ hω.2] with ω hω
  ext i
  exact stoppedValue_add_const_sub_stoppedValue (u := X) (τ := τ) i.val hω

/-- At an almost-surely finite stopping time on a filtration indexed by `ℝ≥0`, for an almost-surely
right-continuous process `X` into a second-countable pseudo-metrizable Borel additive group with
continuous subtraction whose deterministic shifted increment paths share a law `ν` and are
independent of `ℱ s`, the restarted increment path retains the law `ν`. -/
theorem hasLaw_stoppedValue_add_const_sub_stoppedValue
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [TopologicalSpace.PseudoMetrizableSpace E] [AddGroup E] [ContinuousSub E]
    [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P]
    {ν : Measure (ℝ≥0 → E)} {X : ℝ≥0 → Ω → E} (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    (hlaw : ∀ s, HasLaw (fun ω t ↦ X (s + t) ω - X s ω) ν P)
    (hind : ∀ s, Indep (.comap (fun ω t ↦ X (s + t) ω - X s ω) inferInstance) (ℱ s) P) :
    HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω) ν P := by
  have hrest :
      HasLaw (fun ω (t : ℝ≥0) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω)
        (P {ω | τ ω ≠ ⊤} • ν) (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using hτ.hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue hrc hlaw hind .univ
  exact hrest.of_restrict_of_ae_mem hfin

/-- Under a zero or probability measure, at an almost-surely finite stopping time on a filtration
indexed by `ℝ≥0`, for an almost-surely right-continuous process `X` into a second-countable
pseudo-metrizable Borel additive group with continuous subtraction whose deterministic shifted
increment paths share a law `ν` and are independent of `ℱ s`, the restarted increment path is
independent of `hτ.measurableSpace`. -/
theorem indep_stoppedValue_add_const_sub_stoppedValue
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [TopologicalSpace.PseudoMetrizableSpace E] [AddGroup E] [ContinuousSub E]
    [MeasurableSpace E] [BorelSpace E] [IsZeroOrProbabilityMeasure P]
    {ν : Measure (ℝ≥0 → E)} {X : ℝ≥0 → Ω → E} (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    (hlaw : ∀ s, HasLaw (fun ω t ↦ X (s + t) ω - X s ω) ν P)
    (hind : ∀ s, Indep (.comap (fun ω t ↦ X (s + t) ω - X s ω) inferInstance) (ℱ s) P) :
    Indep
      (.comap (fun ω (t : ℝ≥0) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω)
        inferInstance)
      hτ.measurableSpace P :=
  indep_comap_of_forall_hasLaw_restrict_inter hτ.measurableSpace_le hfin fun _ hA ↦
    hτ.hasLaw_restrict_stoppedValue_add_const_sub_stoppedValue hrc hlaw hind hA

end NNReal

end MeasureTheory.IsStoppingTime
