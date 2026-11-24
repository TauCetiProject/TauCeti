/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Specification
public import Mathlib.Probability.ConditionalProbability
import TauCeti.Probability.Process.Tail.ProperAction
import Mathlib.Dynamics.Ergodic.RadonNikodym

/-!
# The face property of invariant Gibbs measures

Let an infinite group `Γ` act properly on a countable index set `I`, and let `γ` be a
specification on a subshift `X` of configurations `I → S`. The invariant Gibbs measures
`𝒢_inv(γ)` (`TauCeti.Specification.gibbsInvariant`) form a face of the convex set `𝔓_inv(X)` of
invariant probability measures (`TauCeti.Specification.gibbsInvariant_isExtreme`): if a proper
convex combination of two invariant probability measures is Gibbs, then so are both. Hence, for a
countable group, an invariant Gibbs measure is an extreme point of `𝒢_inv(γ)` if and only if it is
ergodic (`TauCeti.Specification.gibbsInvariant_extreme_iff_ergodic`), and conditioning an invariant
Gibbs measure on an invariant event of positive mass gives an invariant Gibbs measure
(`TauCeti.Specification.cond_mem_gibbsInvariant`). No equivariance of `γ` and no hypothesis on the
alphabet `S` is needed: only the invariance of the measures and the properness of the action enter.

All three come from one statement, `TauCeti.Specification.IsGibbs.of_absolutelyContinuous`: an
invariant finite measure absolutely continuous with respect to an invariant finite Gibbs measure is
Gibbs. Its density is almost invariant, so its level sets are almost invariant events; for a proper
action of an infinite group these are almost surely tail events
(`TauCeti.Probability.exists_measurableSet_tailEvents_ae_eq_of_proper`, read on `X` through the
inclusion into `I → S` in `TauCeti.Subshift.exists_forall_measurableSet_exterior_ae_eq`). The
density therefore has a version measurable for every exterior σ-algebra
(`TauCeti.Subshift.exists_forall_measurable_exterior_ae_eq`), and reweighting a Gibbs measure by
such a density gives a Gibbs measure (`TauCeti.Specification.IsGibbs.withDensity`).

## Main statements

* `TauCeti.Subshift.exists_forall_measurableSet_exterior_ae_eq`,
  `TauCeti.Subshift.exists_forall_measurable_exterior_ae_eq`: almost invariant events and functions
  on a subshift agree almost everywhere with ones measurable for every exterior σ-algebra.
* `TauCeti.Specification.IsGibbs.of_absolutelyContinuous`: an invariant finite measure absolutely
  continuous with respect to an invariant finite Gibbs measure is Gibbs.
* `TauCeti.Specification.gibbsInvariant_isExtreme`: the face property.
* `TauCeti.Specification.gibbsInvariant_extreme_iff_ergodic`: an invariant Gibbs measure is
  extreme among the invariant Gibbs measures if and only if it is ergodic.
* `TauCeti.Specification.cond_mem_gibbsInvariant`: conditioning on an invariant event.

## References

* H.-O. Georgii, *Gibbs measures and phase transitions* (2nd ed., 2011), Theorem 14.15.
* S. Sheffield, *Random surfaces*, Astérisque 304 (2005), Lemmas 3.2.1 and 3.2.2.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set TauCeti.MeasureTheory TauCeti.Probability
open scoped ENNReal

namespace TauCeti

variable {Γ I S : Type*} [Group Γ] [Infinite Γ] [MulAction Γ I] [Countable I]
  [TopologicalSpace S] [MeasurableSpace S]

namespace Subshift

variable {X : Subshift Γ I S} {μ : Measure X} [IsFiniteMeasure μ] [SMulInvariantMeasure Γ X μ]

/-- **Invariant events of a subshift are almost surely tail events.** For a proper action of an
infinite group on a countable index set and an invariant finite measure on a subshift `X`, every
almost invariant event agrees almost everywhere with an event measurable for the exterior
σ-algebra of every finite set. -/
theorem exists_forall_measurableSet_exterior_ae_eq
    (hproper : ∀ F F' : Finset I, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite)
    {A : Set X} (hA : MeasurableSet A) (hAg : ∀ g : Γ, (fun ω => g • ω) ⁻¹' A =ᵐ[μ] A) :
    ∃ T : Set X, (∀ Λ : Finset I, MeasurableSet[X.exterior Λ] T) ∧ T =ᵐ[μ] A := by
  -- Read `A` as the trace of an event `A'` of `I → S` and push `μ` forward to `I → S`.
  obtain ⟨A', hA', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  have hval : Measurable (Subtype.val : X → I → S) := measurable_subtypeVal
  have hshift (g : Γ) : Measurable fun (ω : I → S) i => ω (g⁻¹ • i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hcomp (g : Γ) : (fun (ω : I → S) i => ω (g⁻¹ • i)) ∘ Subtype.val =
      Subtype.val ∘ fun ω : X => g • ω := by
    ext ω i
    simp [coe_smul]
  have hν (g : Γ) : MeasurePreserving (fun (ω : I → S) i => ω (g⁻¹ • i))
      (μ.map Subtype.val) (μ.map Subtype.val) :=
    ⟨hshift g, by rw [Measure.map_map (hshift g) hval, hcomp, ← Measure.map_map hval
      (measurable_const_smul g), MeasureTheory.map_smul]⟩
  -- Almost equality of events of `I → S` under the push-forward is that of their traces.
  have hae {s t : Set (I → S)} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      s =ᵐ[μ.map Subtype.val] t ↔ Subtype.val ⁻¹' s =ᵐ[μ] Subtype.val ⁻¹' t := by
    rw [ae_eq_set, ae_eq_set, Measure.map_apply hval (hs.diff ht),
      Measure.map_apply hval (ht.diff hs), preimage_sdiff, preimage_sdiff]
  obtain ⟨T, hT, hTA⟩ := exists_measurableSet_tailEvents_ae_eq_of_proper hproper hν
    hA'.nullMeasurableSet fun g => by
      rw [hae (hshift g hA') hA', ← preimage_comp, hcomp, preimage_comp]
      exact hAg g
  refine ⟨Subtype.val ⁻¹' T, fun Λ => ?_, (hae (tailEvents_le_pi T hT) hA').1 hTA⟩
  rw [exterior_def]
  exact MeasurableSpace.measurableSet_comap.2 ⟨T, measurableSet_tailEvents_iff.1 hT Λ, rfl⟩

/-- **Invariant functions on a subshift are almost surely tail-measurable.** For a proper action of
an infinite group on a countable index set and an invariant finite measure on a subshift `X`, every
almost invariant measurable function `X → ℝ≥0∞` agrees almost everywhere with a function
measurable for the exterior σ-algebra of every finite set. -/
theorem exists_forall_measurable_exterior_ae_eq
    (hproper : ∀ F F' : Finset I, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hfg : ∀ g : Γ, f ∘ (fun ω => g • ω) =ᵐ[μ] f) :
    ∃ f' : X → ℝ≥0∞, (∀ Λ : Finset I, Measurable[X.exterior Λ] f') ∧ f' =ᵐ[μ] f := by
  -- The superlevel sets of `f` at rational heights are almost invariant, hence almost surely
  -- tail events `T q`; `f` is almost surely the supremum of the heights `q` with `ω ∈ T q`.
  choose T hT hTf using fun q : ℚ => exists_forall_measurableSet_exterior_ae_eq hproper
    (hf measurableSet_Ioi : MeasurableSet (f ⁻¹' Ioi (ENNReal.ofReal q)))
    fun g => by rw [← preimage_comp]; exact (hfg g).preimage _
  refine ⟨fun ω => ⨆ q : ℚ, (T q).indicator (fun _ => ENNReal.ofReal q) ω,
    fun Λ => Measurable.iSup fun q => measurable_const.indicator (hT q Λ), ?_⟩
  filter_upwards [ae_all_iff.2 hTf] with ω hω
  have hmem (q : ℚ) : ω ∈ T q ↔ ENNReal.ofReal q < f ω := by rw [hω q, mem_preimage, mem_Ioi]
  refine le_antisymm (iSup_le fun q => ?_) (le_of_forall_lt fun r hr => ?_)
  · by_cases h : ω ∈ T q
    · exact (indicator_of_mem h _).trans_le ((hmem q).1 h).le
    · simp [indicator_of_notMem h]
  · obtain ⟨q, -, hrq, hqf⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hr
    rw [ENNReal.ofNNReal_toNNReal] at hrq hqf
    exact hrq.trans_le <| le_iSup_of_le q
      (indicator_of_mem ((hmem q).2 hqf) fun _ => ENNReal.ofReal q).ge

end Subshift

namespace Specification

variable {X : Subshift Γ I S} {γ : Specification X} {μ ν : Measure X}

/-- **Absolutely continuous invariant measures of an invariant Gibbs measure are Gibbs.** For a
proper action of an infinite group on a countable index set, an invariant finite measure `ν`
absolutely continuous with respect to an invariant finite Gibbs measure `μ` is Gibbs: its density
with respect to `μ` is almost invariant, hence almost surely tail-measurable. -/
theorem IsGibbs.of_absolutelyContinuous
    (hproper : ∀ F F' : Finset I, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite)
    [IsFiniteMeasure μ] [SMulInvariantMeasure Γ X μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure Γ X ν] (hμ : γ.IsGibbs μ) (hνμ : ν ≪ μ) : γ.IsGibbs ν := by
  obtain ⟨f, hf, hfν⟩ := Subshift.exists_forall_measurable_exterior_ae_eq hproper
    (Measure.measurable_rnDeriv ν μ) fun g =>
      MeasurePreserving.rnDeriv_comp_aeEq (measurePreserving_smul g ν) (measurePreserving_smul g μ)
  rw [← Measure.withDensity_rnDeriv_eq ν μ hνμ, ← withDensity_congr_ae hfν]
  exact hμ.withDensity hf

variable (γ)

/-- **The face property** of invariant Gibbs measures. For a proper action of an infinite group on
a countable index set and any specification `γ` on a subshift, equivariant or not, the invariant
Gibbs measures `𝒢_inv(γ)` form a face of the invariant probability measures: if a convex
combination with positive weights of two invariant probability measures is Gibbs, both are. -/
theorem gibbsInvariant_isExtreme
    (hproper : ∀ F F' : Finset I, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite) :
    IsExtreme ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq Γ X 1) γ.gibbsInvariant where
  subset _ h := (mem_gibbsInvariant_iff.1 h).1
  left_mem_of_mem_openSegment := by
    rintro μ₁ hμ₁ μ₂ - μ hμ ⟨a, b, ha, -, -, rfl⟩
    obtain ⟨hinv, hγμ⟩ := mem_gibbsInvariant_iff.1 hμ
    obtain ⟨_, hμu⟩ := mem_invariantMeasuresOfMeasureUnivEq_iff.1 hinv
    obtain ⟨_, hμ₁u⟩ := mem_invariantMeasuresOfMeasureUnivEq_iff.1 hμ₁
    have : IsFiniteMeasure μ₁ := ⟨by simp [hμ₁u]⟩
    have : IsFiniteMeasure (a • μ₁ + b • μ₂) := ⟨by simp [hμu]⟩
    exact mem_gibbsInvariant_iff.2 ⟨hμ₁, hγμ.of_absolutelyContinuous hproper
      ((Measure.absolutelyContinuous_smul ha.ne').add_right _)⟩

/-- **Ergodic invariant Gibbs measures are the extreme ones.** For a proper action of a countable
infinite group on a countable index set, an invariant Gibbs measure is an extreme point of the
invariant Gibbs measures if and only if it is ergodic. -/
theorem gibbsInvariant_extreme_iff_ergodic [Countable Γ]
    (hproper : ∀ F F' : Finset I, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite)
    (hμ : μ ∈ γ.gibbsInvariant) :
    μ ∈ extremePoints ℝ≥0∞ γ.gibbsInvariant ↔ ErgodicSMul Γ X μ := by
  have : IsProbabilityMeasure μ :=
    ⟨(mem_invariantMeasuresOfMeasureUnivEq_iff.1 (mem_gibbsInvariant_iff.1 hμ).1).2⟩
  rw [(γ.gibbsInvariant_isExtreme hproper).extremePoints_eq, ErgodicSMul.iff_mem_extremePoints]
  exact and_iff_right hμ

variable {γ}

/-- **Conditioning on an invariant event.** For a proper action of an infinite group on a
countable index set, an invariant Gibbs measure conditioned on an almost invariant event of
positive mass is an invariant Gibbs measure. -/
theorem cond_mem_gibbsInvariant
    (hproper : ∀ F F' : Finset I, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite)
    (hμ : μ ∈ γ.gibbsInvariant) {t : Set X} (ht : MeasurableSet t)
    (htg : ∀ g : Γ, (fun ω => g • ω) ⁻¹' t =ᵐ[μ] t) (ht₀ : μ t ≠ 0) :
    μ[|t] ∈ γ.gibbsInvariant := by
  obtain ⟨hinv, hγμ⟩ := mem_gibbsInvariant_iff.1 hμ
  obtain ⟨_, hμu⟩ := mem_invariantMeasuresOfMeasureUnivEq_iff.1 hinv
  have : IsProbabilityMeasure μ := ⟨hμu⟩
  have : SMulInvariantMeasure Γ X (μ.restrict t) := SMulInvariantMeasure.restrict ht htg
  have hcond : SMulInvariantMeasure Γ X μ[|t] := by
    -- `μ[|t]` is `(μ t)⁻¹ • μ.restrict t` by the definition of `ProbabilityTheory.cond`
    rw [ProbabilityTheory.cond]
    infer_instance
  have := cond_isProbabilityMeasure (μ := μ) ht₀
  exact mem_gibbsInvariant_iff.2
    ⟨mem_invariantMeasuresOfMeasureUnivEq_iff.2 ⟨hcond, measure_univ⟩,
      hγμ.of_absolutelyContinuous hproper cond_absolutelyContinuous⟩

end Specification

end TauCeti
