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
properties: on every event `A ∈ hτ.measurableSpace`, the restriction to `A ∩ {τ ≠ ⊤}` pushes
`stoppedValue U τ` forward to `P (A ∩ {τ ≠ ⊤}) • ν`. When `τ` is almost surely finite under a
probability measure, `stoppedValue U τ` has law `ν` and is independent of `hτ.measurableSpace`.

The countable-range case decomposes `A ∩ {τ ≠ ⊤}` along the countably many level sets `{τ = s}`,
requiring neither a topology on time nor any regularity of `U`. For nonnegative real times,
upward dyadic approximations pass the restricted law to right-continuous families taking values
in a pseudo-metrizable Borel space, on arbitrary raw filtrations.

## Main declarations

* `MeasureTheory.IsStoppingTime.hasLaw_restrict_stoppedValue_of_countable_range`,
  `MeasureTheory.IsStoppingTime.hasLaw_stoppedValue_of_countable_range`, and
  `MeasureTheory.IsStoppingTime.indep_stoppedValue_of_countable_range`: law and independence at
  countable-range stopping times over a partial order.
* `MeasureTheory.IsStoppingTime.hasLaw_restrict_stoppedValue`,
  `MeasureTheory.IsStoppingTime.hasLaw_stoppedValue`, and
  `MeasureTheory.IsStoppingTime.indep_stoppedValue`: law and independence for right-continuous
  families indexed by `ℝ≥0` at arbitrary stopping times.

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

/-- At a countable-range stopping time `τ`, if each `U s` is measurable with law `ν` and is
independent of `ℱ s`, then on `A ∩ {τ ≠ ⊤}` for any `A ∈ hτ.measurableSpace` the stopped value
`stoppedValue U τ` has law `P (A ∩ {τ ≠ ⊤}) • ν`. -/
theorem hasLaw_restrict_stoppedValue_of_countable_range (hτ : IsStoppingTime ℱ τ)
    (hc : (range τ).Countable) (hm : ∀ s, Measurable (U s)) (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    HasLaw (stoppedValue U τ) (P (A ∩ {ω | τ ω ≠ ⊤}) • ν)
      (P.restrict (A ∩ {ω | τ ω ≠ ⊤})) := by
  let R : Set ι := {s | (s : WithTop ι) ∈ range τ}
  have hR : R.Countable := hc.preimage WithTop.coe_injective
  -- Decompose `A ∩ {τ ≠ ⊤}` into the countably many filtration-measurable slices `A ∩ {τ = s}`.
  have hslice (s : ι) : MeasurableSet[ℱ s] (A ∩ {ω | τ ω = s}) := by
    have heq : A ∩ {ω | τ ω = s} = (A ∩ {ω | τ ω ≤ s}) ∩ {ω | τ ω = s} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨⟨h₁, h₂.le⟩, h₂⟩, fun ⟨⟨h₁, _⟩, h₂⟩ ↦ ⟨h₁, h₂⟩⟩
    rw [heq]
    exact (hA.2 s).inter (hτ.measurableSet_eq_of_countable_range hc s)
  have hslice_meas (s : ι) : MeasurableSet (A ∩ {ω | τ ω = s}) := ℱ.le s _ (hslice s)
  have hdecomp : A ∩ {ω | τ ω ≠ ⊤} = ⋃ s ∈ R, A ∩ {ω | τ ω = s} := by
    ext ω
    cases h : τ ω with
    | top => simp [h]
    | coe s =>
      simpa [h, R] using fun _ ↦ (⟨ω, h⟩ : ∃ y, τ y = (s : WithTop ι))
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
  -- On each slice `{τ = s}`, independence from `ℱ s` factors out the common law `ν C`.
  have hfactor (s : ι) : P (U s ⁻¹' C ∩ (A ∩ {ω | τ ω = s})) = ν C * P (A ∩ {ω | τ ω = s}) := by
    rw [(Indep_iff _ _ _).1 (hind s) _ _ ⟨C, hC, rfl⟩ (hslice s),
      ← Measure.map_apply (hm s) hC, (hlaw s).map_eq]
  have : Countable R := hR.to_subtype
  rw [hpre, measure_biUnion hR hdisj_pre fun s _ ↦ (hm s hC).inter (hslice_meas s)]
  simp only [hfactor, ENNReal.tsum_mul_left]
  rw [← measure_biUnion hR hdisj fun s _ ↦ hslice_meas s, ← hdecomp, smul_apply, smul_eq_mul,
    mul_comm]

/-- At an almost-surely finite stopping time with countable range, a coordinatewise measurable
family sharing a law `ν` with each slice independent of `ℱ s` retains the law `ν`. -/
theorem hasLaw_stoppedValue_of_countable_range [IsProbabilityMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hc : (range τ).Countable) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hm : ∀ s, Measurable (U s))
    (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) :
    HasLaw (stoppedValue U τ) ν P := by
  have hrest : HasLaw (stoppedValue U τ) (P {ω | τ ω ≠ ⊤} • ν) (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using hτ.hasLaw_restrict_stoppedValue_of_countable_range hc hm hlaw hind .univ
  exact hrest.of_restrict_of_ae_mem hfin

/-- At an almost-surely finite stopping time with countable range, a coordinatewise measurable
family sharing a law `ν` with each slice independent of `ℱ s` has stopped value independent of
`hτ.measurableSpace`. -/
theorem indep_stoppedValue_of_countable_range [IsProbabilityMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hc : (range τ).Countable) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hm : ∀ s, Measurable (U s))
    (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) :
    Indep (.comap (stoppedValue U τ) inferInstance) hτ.measurableSpace P :=
  indep_comap_of_forall_hasLaw_restrict_inter hτ.measurableSpace_le hfin fun _ hA ↦
    hτ.hasLaw_restrict_stoppedValue_of_countable_range hc hm hlaw hind hA

end CountableRange

section NNReal

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace β]
  [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
  {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} {ν : Measure β}
  {U : ℝ≥0 → Ω → β} {τ : Ω → WithTop ℝ≥0}

/-- At an arbitrary stopping time `τ` on a filtration indexed by `ℝ≥0`, an almost-surely
right-continuous coordinatewise measurable family into a pseudo-metrizable Borel space with common
law `ν` and slices independent of `ℱ s` has restricted law `P (A ∩ {τ ≠ ⊤}) • ν` on
`A ∩ {τ ≠ ⊤}` for every `A ∈ hτ.measurableSpace`. -/
theorem hasLaw_restrict_stoppedValue [IsFiniteMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hm : ∀ s, Measurable (U s)) (hrc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ U t ω))
    (hlaw : ∀ s, HasLaw (U s) ν P)
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
      (TauCeti.countable_range_dyadicCeilTime τ n) hm hlaw hind hA'σ
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
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hm : ∀ s, Measurable (U s))
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ U t ω)) (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) :
    HasLaw (stoppedValue U τ) ν P := by
  have hrest : HasLaw (stoppedValue U τ) (P {ω | τ ω ≠ ⊤} • ν) (P.restrict {ω | τ ω ≠ ⊤}) := by
    simpa using hτ.hasLaw_restrict_stoppedValue hm hrc hlaw hind .univ
  exact hrest.of_restrict_of_ae_mem hfin

/-- At an almost-surely finite stopping time on a filtration indexed by `ℝ≥0`, an almost-surely
right-continuous family into a pseudo-metrizable Borel space sharing law `ν` with slices
independent of `ℱ s` has stopped value independent of `hτ.measurableSpace`. -/
theorem indep_stoppedValue [IsProbabilityMeasure P] (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hm : ∀ s, Measurable (U s))
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ U t ω)) (hlaw : ∀ s, HasLaw (U s) ν P)
    (hind : ∀ s, Indep (.comap (U s) inferInstance) (ℱ s) P) :
    Indep (.comap (stoppedValue U τ) inferInstance) hτ.measurableSpace P :=
  indep_comap_of_forall_hasLaw_restrict_inter hτ.measurableSpace_le hfin fun _ hA ↦
    hτ.hasLaw_restrict_stoppedValue hm hrc hlaw hind hA

end NNReal

end MeasureTheory.IsStoppingTime
