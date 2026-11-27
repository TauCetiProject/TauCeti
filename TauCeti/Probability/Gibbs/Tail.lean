/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Specification
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.Probability.ConditionalProbability
import TauCeti.Probability.Martingale.Convergence
import TauCeti.Probability.Process.Tail.Subshift
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Gibbs measures and the tail σ-algebra

Let `γ` be a specification on a subshift `X` of configurations `I → S`, with `I` countable. A
*tail event* is an event of `X` that is measurable for the exterior σ-algebra `𝓕_{Λᶜ}`
(`TauCeti.Subshift.exterior`) of every finite `Λ ⊆ I`, and a tail-measurable function is one that
is `𝓕_{Λᶜ}`-measurable for every finite `Λ`. This file shows that a Gibbs measure is determined by
its values on the tail events, and characterises the extreme points of the convex set
`𝒢(γ)` of Gibbs probability measures (`TauCeti.Specification.gibbsMeasures`) as the Gibbs
probability measures that are trivial on the tail.

## Main statements

* `TauCeti.Specification.exists_tail_ae_eq_of_isGibbs_withDensity`: if `μ` is a finite Gibbs
  measure and `f • μ` is a Gibbs measure, then `f` agrees `μ`-almost everywhere with a
  tail-measurable function. This is the converse of `TauCeti.Specification.IsGibbs.withDensity`.
* `TauCeti.Specification.eq_of_forall_tail_eq`: two finite Gibbs measures that agree on the tail
  events are equal.
* `TauCeti.Specification.mem_extremePoints_gibbsMeasures_iff_measure_eq_zero_or_one`: a Gibbs
  probability measure is an extreme point of `𝒢(γ)` if and only if every tail event has measure
  `0` or `1`.
* `TauCeti.Specification.mem_extremePoints_gibbsMeasures_iff_abs_measureReal_inter_sub_mul_le`: a
  Gibbs probability measure is an extreme point of `𝒢(γ)` if and only if it has short-range
  correlations: every event is asymptotically independent of the events outside large finite
  sets.
* `TauCeti.Specification.exists_tail_separating_of_mem_extremePoints`: two distinct extreme
  Gibbs probability measures are carried by disjoint tail events.

## Implementation notes

The first statement holds one finite set at a time
(`TauCeti.Specification.condLExp_ae_eq_of_bind_kernel_withDensity`): if both `μ` and `f • μ` are
invariant under `γ_Λ`, the conditional Lebesgue expectation `μ⁻[f | 𝓕_{Λᶜ}]` is a version of `f`,
because integrating the `𝓕_{Λᶜ}`-measurable function `γ_Λ (C | ·)` against `f • μ` or against
`μ⁻[f | 𝓕_{Λᶜ}] • μ` gives the same masses. The
versions for the finite sets of an exhaustion combine into one tail-measurable version
(`TauCeti.Subshift.exists_forall_measurable_exterior_ae_eq_of_forall_exists`), with no martingale
convergence. The extreme-point characterisation compares a Gibbs measure with the halves of a
decomposition through the tail: conditioning on a tail event preserves the Gibbs property
(`TauCeti.Specification.IsGibbs.cond`), and a Gibbs probability measure absolutely continuous with
respect to a tail-trivial one agrees with it on the tail, hence everywhere. Short-range
correlations follow from tail triviality and Lévy's downward theorem along an exhaustion of `I`
(`MeasureTheory.exists_forall_abs_measureReal_inter_sub_mul_le_of_forall_zero_or_one_iInf`).

## References

* S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press, 2017, Proposition 6.61, Theorem 6.58 and Lemma 6.62.
* D. Ruelle, *Thermodynamic Formalism* (2nd ed., 2004), Theorem 1.11.
* H.-O. Georgii, *Gibbs measures and phase transitions* (2nd ed., 2011), Theorem 7.7.
-/

public section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

namespace Specification

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [TopologicalSpace S] [MeasurableSpace S]
  {X : Subshift Γ I S} {γ : Specification X} {μ ν : Measure X}

/-- **Gibbs densities are exterior-measurable, one finite set at a time.** If a finite measure `μ`
and its reweighting `f • μ` are both invariant under `γ_Λ`, then `f` agrees `μ`-almost everywhere
with its conditional Lebesgue expectation `μ⁻[f | 𝓕_{Λᶜ}]` given the exterior σ-algebra. -/
theorem condLExp_ae_eq_of_bind_kernel_withDensity [IsFiniteMeasure μ] {Λ : Finset I}
    (hμ : μ.bind (γ.kernel Λ) = μ) {f : X → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hfμ : (μ.withDensity f).bind (γ.kernel Λ) = μ.withDensity f) :
    μ⁻[f|X.exterior Λ] =ᵐ[μ] f := by
  have hm := X.exterior_le Λ
  have hg := measurable_condLExp (X.exterior Λ) μ f
  -- `f • μ` and `μ⁻[f | 𝓕_{Λᶜ}] • μ` agree on `𝓕_{Λᶜ}`, so they integrate
  -- `𝓕_{Λᶜ}`-measurable functions alike.
  have htrim : (μ.withDensity μ⁻[f|X.exterior Λ]).trim hm = (μ.withDensity f).trim hm := by
    refine @Measure.ext _ (X.exterior Λ) _ _ fun s hs => ?_
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs),
      withDensity_apply _ (hm s hs), setLIntegral_condLExp hm μ f hs]
  have hint {h : X → ℝ≥0∞} (hh : Measurable[X.exterior Λ] h) :
      ∫⁻ ω, h ω ∂(μ.withDensity μ⁻[f|X.exterior Λ]) = ∫⁻ ω, h ω ∂(μ.withDensity f) := by
    rw [← lintegral_trim hm hh, htrim, lintegral_trim hm hh]
  refine (withDensity_eq_iff_of_sigmaFinite (hg.mono hm le_rfl).aemeasurable hf).1 ?_
  -- Both reweightings are invariant under `γ_Λ`, and `γ_Λ (C | ·)` is `𝓕_{Λᶜ}`-measurable.
  ext C hC
  rw [← bind_kernel_withDensity hμ hg, ← hfμ,
    Measure.bind_apply hC (γ.measurable_kernel Λ).aemeasurable,
    Measure.bind_apply hC (γ.measurable_kernel Λ).aemeasurable,
    hint ((γ.kernel Λ).measurable_coe hC)]

/-- **Gibbs densities are tail-measurable.** If `μ` is a finite Gibbs measure and `f • μ` is Gibbs,
then `f` agrees `μ`-almost everywhere with a function measurable for the exterior σ-algebra of
every finite set. -/
theorem exists_tail_ae_eq_of_isGibbs_withDensity [Countable I] [IsFiniteMeasure μ]
    (hμ : γ.IsGibbs μ) {f : X → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hfμ : γ.IsGibbs (μ.withDensity f)) :
    ∃ g : X → ℝ≥0∞, (∀ Λ : Finset I, Measurable[X.exterior Λ] g) ∧ g =ᵐ[μ] f :=
  Subshift.exists_forall_measurable_exterior_ae_eq_of_forall_exists fun Λ =>
    ⟨_, measurable_condLExp _ μ f,
      condLExp_ae_eq_of_bind_kernel_withDensity (hμ.bind_kernel Λ) hf (hfμ.bind_kernel Λ)⟩

/-- **The tail determines a Gibbs measure.** Two finite Gibbs measures that agree on every event
measurable for the exterior σ-algebra of every finite set are equal. -/
theorem eq_of_forall_tail_eq [Countable I] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : γ.IsGibbs μ) (hν : γ.IsGibbs ν)
    (h : ∀ A : Set X, (∀ Λ : Finset I, MeasurableSet[X.exterior Λ] A) → μ A = ν A) : μ = ν := by
  -- Both measures have tail-measurable densities with respect to the Gibbs measure `μ + ν`.
  have hdens {κ : Measure X} [IsFiniteMeasure κ] (hκ : γ.IsGibbs κ) (hκρ : κ ≪ μ + ν) :
      ∃ g : X → ℝ≥0∞, (∀ Λ : Finset I, Measurable[X.exterior Λ] g) ∧
        κ = (μ + ν).withDensity g := by
    have hκ' : κ = (μ + ν).withDensity (κ.rnDeriv (μ + ν)) :=
      (Measure.withDensity_rnDeriv_eq κ _ hκρ).symm
    obtain ⟨g, hg, hgκ⟩ := exists_tail_ae_eq_of_isGibbs_withDensity (hμ.add hν)
      (Measure.measurable_rnDeriv κ _).aemeasurable (hκ' ▸ hκ)
    exact ⟨g, hg, hκ'.trans (withDensity_congr_ae hgκ.symm)⟩
  obtain ⟨f, hf, hfμ⟩ := hdens hμ (Measure.AbsolutelyContinuous.rfl.add_right ν)
  obtain ⟨g, hg, hgν⟩ := hdens hν (Measure.AbsolutelyContinuous.rfl.add_right' μ)
  -- The densities agree almost everywhere: they are measurable for the tail σ-algebra `m`, and
  -- have the same integrals over its events.
  set m := ⨅ Λ : Finset I, X.exterior Λ
  have hm : m ≤ Subtype.instMeasurableSpace := (iInf_le _ ∅).trans (X.exterior_le _)
  have hmeas {k : X → ℝ≥0∞} (hk : ∀ Λ : Finset I, Measurable[X.exterior Λ] k) :
      Measurable[m] k := fun s hs => MeasurableSpace.measurableSet_iInf.2 fun Λ => hk Λ hs
  have hfg : f =ᵐ[μ + ν] g := ae_eq_of_ae_eq_trim <|
    ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (hmeas hf) (hmeas hg) fun s hs _ => by
      rw [setLIntegral_trim hm (hmeas hf) hs, setLIntegral_trim hm (hmeas hg) hs,
        ← withDensity_apply _ (hm s hs), ← withDensity_apply _ (hm s hs), ← hfμ, ← hgν]
      exact h s (MeasurableSpace.measurableSet_iInf.1 hs)
  rw [hfμ, withDensity_congr_ae hfg, ← hgν]

/-- **Conditioning on a tail event.** A Gibbs measure conditioned on an event measurable for the
exterior σ-algebra of every finite set is Gibbs. -/
theorem IsGibbs.cond (hμ : γ.IsGibbs μ) {A : Set X}
    (hA : ∀ Λ : Finset I, MeasurableSet[X.exterior Λ] A) : γ.IsGibbs μ[|A] := by
  rw [ProbabilityTheory.cond,
    ← withDensity_indicator_one (Subshift.measurableSet_of_forall_measurableSet_exterior hA)]
  exact (hμ.withDensity fun Λ =>
    Measurable.indicator (m := X.exterior Λ) measurable_const (hA Λ)).smul _

/-- **Extreme Gibbs measures are the tail-trivial ones.** A Gibbs probability measure is an extreme
point of the Gibbs probability measures `𝒢(γ)` if and only if every event measurable for the
exterior σ-algebra of every finite set has measure `0` or `1`. -/
theorem mem_extremePoints_gibbsMeasures_iff_measure_eq_zero_or_one [Countable I]
    (hμ : μ ∈ γ.gibbsMeasures) :
    μ ∈ extremePoints ℝ≥0∞ γ.gibbsMeasures ↔
      ∀ A : Set X, (∀ Λ : Finset I, MeasurableSet[X.exterior Λ] A) → μ A = 0 ∨ μ A = 1 := by
  obtain ⟨_, hγμ⟩ := mem_gibbsMeasures_iff.1 hμ
  constructor
  · -- A tail event `A` of mass strictly between `0` and `1` splits `μ` into the conditioned
    -- measures `μ[|A]` and `μ[|Aᶜ]`, which are Gibbs and differ from `μ`.
    intro hext A hA
    have hAm := Subshift.measurableSet_of_forall_measurableSet_exterior hA
    by_contra! hA01
    obtain ⟨h0, h1⟩ := hA01
    have h0' : μ Aᶜ ≠ 0 := by rwa [Ne, prob_compl_eq_zero_iff hAm]
    have hdec : μ A • μ[|A] + μ Aᶜ • μ[|Aᶜ] = μ := by
      ext t -
      simp only [add_apply, smul_apply, smul_eq_mul]
      rw [mul_comm, mul_comm (μ Aᶜ), cond_add_cond_compl_eq hAm]
    have hcond := (mem_extremePoints.1 hext).2 μ[|A]
      (mem_gibbsMeasures_iff.2 ⟨cond_isProbabilityMeasure h0, hγμ.cond hA⟩) μ[|Aᶜ]
      (mem_gibbsMeasures_iff.2 ⟨cond_isProbabilityMeasure h0', hγμ.cond fun Λ => (hA Λ).compl⟩)
      ⟨μ A, μ Aᶜ, pos_iff_ne_zero.2 h0, pos_iff_ne_zero.2 h0', prob_add_prob_compl hAm,
        hdec⟩
    exact h1 (by rw [← hcond.1, cond_apply_self h0 (measure_ne_top _ _)])
  · -- A Gibbs probability measure `ν ≪ μ` agrees with `μ` on the tail, hence everywhere.
    intro htriv
    refine mem_extremePoints.2 ⟨hμ, ?_⟩
    have key {ν : Measure X} [IsProbabilityMeasure ν] (hν : γ.IsGibbs ν) (hνμ : ν ≪ μ) : ν = μ :=
      eq_of_forall_tail_eq hν hγμ fun A hA => by
        have hAm := Subshift.measurableSet_of_forall_measurableSet_exterior hA
        rcases htriv A hA with h | h
        · rw [h, hνμ h]
        · rw [h, ← prob_compl_eq_zero_iff hAm]
          exact hνμ ((prob_compl_eq_zero_iff hAm).2 h)
    rintro ν₁ hν₁ ν₂ hν₂ ⟨a, b, ha, hb, -, rfl⟩
    obtain ⟨_, hν₁⟩ := mem_gibbsMeasures_iff.1 hν₁
    obtain ⟨_, hν₂⟩ := mem_gibbsMeasures_iff.1 hν₂
    exact ⟨key hν₁ ((Measure.absolutelyContinuous_smul ha.ne').add_right _),
      key hν₂ ((Measure.absolutelyContinuous_smul hb.ne').add_right' _)⟩

/-- **Distinct extreme Gibbs measures are singular.** Two distinct extreme points of the Gibbs
probability measures `𝒢(γ)` are carried by disjoint tail events: some event measurable for the
exterior σ-algebra of every finite set has measure `0` for the first and `1` for the second. -/
theorem exists_tail_separating_of_mem_extremePoints [Countable I]
    (hμ : μ ∈ extremePoints ℝ≥0∞ γ.gibbsMeasures) (hν : ν ∈ extremePoints ℝ≥0∞ γ.gibbsMeasures)
    (hne : μ ≠ ν) :
    ∃ A : Set X, (∀ Λ : Finset I, MeasurableSet[X.exterior Λ] A) ∧ μ A = 0 ∧ ν A = 1 := by
  obtain ⟨_, hγμ⟩ := mem_gibbsMeasures_iff.1 hμ.1
  obtain ⟨_, hγν⟩ := mem_gibbsMeasures_iff.1 hν.1
  have hμ' := (mem_extremePoints_gibbsMeasures_iff_measure_eq_zero_or_one hμ.1).1 hμ
  have hν' := (mem_extremePoints_gibbsMeasures_iff_measure_eq_zero_or_one hν.1).1 hν
  obtain ⟨A, hA, hAne⟩ : ∃ A : Set X, (∀ Λ : Finset I, MeasurableSet[X.exterior Λ] A) ∧
      μ A ≠ ν A := by
    by_contra! h
    exact hne (eq_of_forall_tail_eq hγμ hγν h)
  have hmeas := Subshift.measurableSet_of_forall_measurableSet_exterior hA
  rcases hμ' A hA with hμA | hμA <;> rcases hν' A hA with hνA | hνA
  · exact absurd (hμA.trans hνA.symm) hAne
  · exact ⟨A, hA, hμA, hνA⟩
  · exact ⟨Aᶜ, fun Λ => (hA Λ).compl, (prob_compl_eq_zero_iff hmeas).2 hμA,
      (prob_compl_eq_one_iff₀ hmeas.nullMeasurableSet).2 hνA⟩
  · exact absurd (hμA.trans hνA.symm) hAne

/-- **Extreme Gibbs measures are the ones with short-range correlations.** A Gibbs probability
measure `μ` is an extreme point of the Gibbs probability measures `𝒢(γ)` if and only if every
measurable event `A` is asymptotically independent of the configuration far away: for every
`ε > 0` some finite `Λ` has `|μ (A ∩ B) - μ A * μ B| ≤ ε` for every `𝓕_{Λᶜ}`-measurable `B`. -/
theorem mem_extremePoints_gibbsMeasures_iff_abs_measureReal_inter_sub_mul_le [Countable I]
    (hμ : μ ∈ γ.gibbsMeasures) :
    μ ∈ extremePoints ℝ≥0∞ γ.gibbsMeasures ↔
      ∀ A : Set X, MeasurableSet A → ∀ ε : ℝ, 0 < ε → ∃ Λ : Finset I,
        ∀ B : Set X, MeasurableSet[X.exterior Λ] B →
          |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ ε := by
  obtain ⟨_, -⟩ := mem_gibbsMeasures_iff.1 hμ
  rw [mem_extremePoints_gibbsMeasures_iff_measure_eq_zero_or_one hμ]
  constructor
  · -- Along an exhaustion by finite sets `D n` the exterior σ-algebras decrease, and their
    -- intersection is `μ`-trivial.
    intro htriv A hA ε hε
    obtain ⟨D, hanti, hD⟩ := X.exists_antitone_exterior_forall_exists_le
    have htriv' (s : Set X) (hs : MeasurableSet[⨅ n, X.exterior (D n : Set I)] s) :
        μ s = 0 ∨ μ s = 1 := htriv s fun Λ => by
      obtain ⟨n, hn⟩ := hD Λ
      exact hn _ (MeasurableSpace.measurableSet_iInf.1 hs n)
    obtain ⟨n, hn⟩ := exists_forall_abs_measureReal_inter_sub_mul_le_of_forall_zero_or_one_iInf
      hanti (X.exterior_le _) htriv' hA hε
    exact ⟨D n, hn⟩
  · -- Taking `B = A` for a tail event `A` gives `μ A = μ A * μ A`.
    intro hdec A hA
    have hsq : μ.real A * (1 - μ.real A) = 0 := by
      have : |μ.real A - μ.real A * μ.real A| ≤ 0 := le_of_forall_pos_le_add fun ε hε => by
        obtain ⟨Λ, hΛ⟩ := hdec A (Subshift.measurableSet_of_forall_measurableSet_exterior hA) ε hε
        simpa using hΛ A (hA Λ)
      rw [mul_sub, mul_one]
      exact abs_nonpos_iff.1 this
    rcases mul_eq_zero.1 hsq with h | h
    · exact .inl ((measureReal_eq_zero_iff (measure_ne_top μ A)).1 h)
    · exact .inr (ENNReal.toReal_eq_one_iff _ |>.1 (by rw [← measureReal_def]; linarith))

end Specification

end TauCeti
