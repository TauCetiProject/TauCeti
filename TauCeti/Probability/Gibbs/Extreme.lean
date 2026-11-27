/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Specification
public import Mathlib.Probability.ConditionalProbability
import TauCeti.Probability.Process.Tail.Subshift
import TauCeti.MeasureTheory.Group.Action
import Mathlib.Dynamics.Ergodic.RadonNikodym

/-!
# The face property of invariant Gibbs measures

Let a group `Γ` act on a countable index set `I` so that every finite subset of `I` can be moved
off every finite subset by some element of `Γ`, as an infinite group acting properly does
(`TauCeti.Probability.exists_forall_smul_notMem_of_proper`), and let `γ` be a specification on a
subshift `X` of configurations `I → S`. The invariant Gibbs measures `𝒢_inv(γ)`
(`TauCeti.Specification.gibbsInvariant`) form a face of the convex set `𝔓_inv(X)` of invariant
probability measures (`TauCeti.Specification.isExtreme_gibbsInvariant`): if a convex combination
with positive weights of two invariant probability measures is Gibbs, then so are both. Hence, for
a countable group, an invariant Gibbs measure is an extreme point of `𝒢_inv(γ)` if and only if it
is ergodic (`TauCeti.Specification.mem_extremePoints_gibbsInvariant_iff_ergodicSMul`), and
conditioning an invariant Gibbs measure on a null-measurable, almost invariant event of positive
mass gives an invariant Gibbs measure (`TauCeti.Specification.cond_mem_gibbsInvariant`). No
equivariance of `γ` and no hypothesis on the alphabet `S` is needed: only the invariance of the
measures and the displacement property of the action enter.

All three come from one statement, `TauCeti.Specification.IsGibbs.of_absolutelyContinuous`: an
invariant finite measure absolutely continuous with respect to an invariant finite Gibbs measure is
Gibbs. Its density is almost invariant, hence almost everywhere equal to a function measurable
for every exterior σ-algebra (`TauCeti.Subshift.exists_forall_measurable_exterior_ae_eq`), and
reweighting a Gibbs measure by such a density gives a Gibbs measure
(`TauCeti.Specification.IsGibbs.withDensity`).

## Main statements

* `TauCeti.Specification.IsGibbs.of_absolutelyContinuous`: an invariant finite measure absolutely
  continuous with respect to an invariant finite Gibbs measure is Gibbs.
* `TauCeti.Specification.isExtreme_gibbsInvariant`: the face property.
* `TauCeti.Specification.mem_extremePoints_gibbsInvariant_iff_ergodicSMul`: an invariant Gibbs
  measure is extreme among the invariant Gibbs measures if and only if it is ergodic.
* `TauCeti.Specification.cond_mem_gibbsInvariant`: conditioning on an invariant event.

## References

* H.-O. Georgii, *Gibbs measures and phase transitions* (2nd ed., 2011), Theorem 14.15.
* S. Sheffield, *Random surfaces*, Astérisque 304 (2005), Lemma 3.2.2.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set TauCeti.MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Specification

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [Countable I] [TopologicalSpace S]
  [MeasurableSpace S] {X : Subshift Γ I S} {γ : Specification X} {μ ν : Measure X}

/-- **Absolutely continuous invariant measures of an invariant Gibbs measure are Gibbs.** If every
finite subset of the countable index set can be moved off every finite subset by the group, then an
invariant finite measure `ν` absolutely continuous with respect to an invariant finite Gibbs
measure `μ` is Gibbs: its density with respect to `μ` is almost invariant, hence almost everywhere
equal to a function measurable for every exterior σ-algebra. -/
theorem IsGibbs.of_absolutelyContinuous
    (hmove : ∀ F Λ : Finset I, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ)
    [IsFiniteMeasure μ] [SMulInvariantMeasure Γ X μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure Γ X ν] (hμ : γ.IsGibbs μ) (hνμ : ν ≪ μ) : γ.IsGibbs ν := by
  obtain ⟨f, hf, hfν⟩ := Subshift.exists_forall_measurable_exterior_ae_eq hmove
    (Measure.measurable_rnDeriv ν μ).aemeasurable fun g =>
      MeasurePreserving.rnDeriv_comp_aeEq (measurePreserving_smul g ν) (measurePreserving_smul g μ)
  rw [← Measure.withDensity_rnDeriv_eq ν μ hνμ, ← withDensity_congr_ae hfν]
  exact hμ.withDensity hf

variable (γ)

/-- **The face property** of invariant Gibbs measures. If every finite subset of the countable
index set can be moved off every finite subset by the group, then for any specification `γ` on a
subshift, equivariant or not, the invariant Gibbs measures `𝒢_inv(γ)` form a face of the invariant
probability measures: if a convex combination with positive weights of two invariant probability
measures is Gibbs, both are. -/
theorem isExtreme_gibbsInvariant (hmove : ∀ F Λ : Finset I, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ) :
    IsExtreme ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq Γ X 1) γ.gibbsInvariant where
  subset _ h := (mem_gibbsInvariant_iff.1 h).1
  left_mem_of_mem_openSegment := by
    rintro μ₁ hμ₁ μ₂ - μ hμ ⟨a, b, ha, -, -, rfl⟩
    obtain ⟨hinv, hγμ⟩ := mem_gibbsInvariant_iff.1 hμ
    obtain ⟨_, hμu⟩ := mem_invariantMeasuresOfMeasureUnivEq_iff.1 hinv
    obtain ⟨_, hμ₁u⟩ := mem_invariantMeasuresOfMeasureUnivEq_iff.1 hμ₁
    have : IsFiniteMeasure μ₁ := ⟨by simp [hμ₁u]⟩
    have : IsFiniteMeasure (a • μ₁ + b • μ₂) := ⟨by simp [hμu]⟩
    exact mem_gibbsInvariant_iff.2 ⟨hμ₁, hγμ.of_absolutelyContinuous hmove
      ((Measure.absolutelyContinuous_smul ha.ne').add_right _)⟩

/-- **Ergodic invariant Gibbs measures are the extreme ones.** If the countable group `Γ` can move
every finite subset of the countable index set off every finite subset, then an invariant Gibbs
measure is an extreme point of the invariant Gibbs measures if and only if it is ergodic. -/
theorem mem_extremePoints_gibbsInvariant_iff_ergodicSMul [Countable Γ]
    (hmove : ∀ F Λ : Finset I, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ) (hμ : μ ∈ γ.gibbsInvariant) :
    μ ∈ extremePoints ℝ≥0∞ γ.gibbsInvariant ↔ ErgodicSMul Γ X μ := by
  have : IsProbabilityMeasure μ :=
    ⟨(mem_invariantMeasuresOfMeasureUnivEq_iff.1 (mem_gibbsInvariant_iff.1 hμ).1).2⟩
  rw [(γ.isExtreme_gibbsInvariant hmove).extremePoints_eq, ErgodicSMul.iff_mem_extremePoints]
  exact and_iff_right hμ

variable {γ}

/-- **Conditioning on an invariant event.** If every finite subset of the countable index set can be
moved off every finite subset by the group, then an invariant Gibbs measure conditioned on a
null-measurable, almost invariant event of positive mass is an invariant Gibbs measure. -/
theorem cond_mem_gibbsInvariant (hmove : ∀ F Λ : Finset I, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ)
    (hμ : μ ∈ γ.gibbsInvariant) {t : Set X} (ht : NullMeasurableSet t μ)
    (htg : ∀ g : Γ, (fun ω => g • ω) ⁻¹' t =ᵐ[μ] t) (ht₀ : μ t ≠ 0) :
    μ[|t] ∈ γ.gibbsInvariant := by
  obtain ⟨hinv, hγμ⟩ := mem_gibbsInvariant_iff.1 hμ
  obtain ⟨_, hμu⟩ := mem_invariantMeasuresOfMeasureUnivEq_iff.1 hinv
  have : IsProbabilityMeasure μ := ⟨hμu⟩
  -- Replace `t` by a measurable version `t'`; the conditioned measure does not change.
  obtain ⟨t', -, ht', htt'⟩ := ht.exists_measurable_subset_ae_eq
  have hcond_eq : μ[|t] = μ[|t'] := by
    simp only [ProbabilityTheory.cond, measure_congr htt', Measure.restrict_congr_set htt']
  rw [hcond_eq]
  rw [← measure_congr htt'] at ht₀
  have := cond_isProbabilityMeasure (μ := μ) ht₀
  have hcond := SMulInvariantMeasure.cond ht' fun g : Γ =>
    preimage_smul_ae_eq_self_of_ae_eq htt' (htg g)
  exact mem_gibbsInvariant_iff.2
    ⟨mem_invariantMeasuresOfMeasureUnivEq_iff.2 ⟨hcond, measure_univ⟩,
      hγμ.of_absolutelyContinuous hmove cond_absolutelyContinuous⟩

end Specification

end TauCeti
