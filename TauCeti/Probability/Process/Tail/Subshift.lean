/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.SymbolicDynamics.Subshift
public import TauCeti.Probability.Process.Tail.ProperAction
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable
import TauCeti.MeasureTheory.Function.SuperlevelVersion
import TauCeti.MeasureTheory.Group.Action

/-!
# Invariant events of a subshift are almost surely exterior events

Let a group `Γ` act on a countable index set `I` so that every finite `F ⊆ I` can be moved off
every finite `Λ ⊆ I` by some `g ∈ Γ`, as an infinite group acting properly does
(`TauCeti.Probability.exists_forall_smul_notMem_of_proper`). Let `μ` be a finite invariant measure
on a subshift `X ⊆ I → S`. Then every null-measurable almost invariant event of `X` agrees
`μ`-almost everywhere with one event that is measurable for the exterior σ-algebra
`TauCeti.Subshift.exterior X Λ` of every finite `Λ`
(`TauCeti.Subshift.exists_forall_measurableSet_exterior_ae_eq`), and every almost invariant,
almost everywhere measurable function `X → ℝ≥0∞` agrees almost everywhere with one function
measurable for all of them (`TauCeti.Subshift.exists_forall_measurable_exterior_ae_eq`).

The event statement is `TauCeti.Probability.exists_measurableSet_tailEvents_ae_eq` read on `X`: an
event of `X` is the trace of an event of `I → S`, almost invariant for the push-forward of `μ`,
which is invariant because `μ` is. Neither closedness nor measurability of `X` in `I → S` is used.
The function statement applies the event statement to the superlevel sets
(`TauCeti.MeasureTheory.exists_measurable_ae_eq_of_forall_superlevel`).

Without any group action: for any measure on `X`, a function `X → ℝ≥0∞` that agrees almost
everywhere with an `𝓕_{Λᶜ}`-measurable function for each finite `Λ` separately agrees almost
everywhere with one function measurable for all of them
(`TauCeti.Subshift.exists_forall_measurable_exterior_ae_eq_of_forall_exists`). The exterior
σ-algebras of an exhaustion of `I` decrease and eventually refine each exterior σ-algebra of a
finite set (`TauCeti.Subshift.exists_antitone_exterior_forall_exists_le`), and the versions combine
through `TauCeti.MeasureTheory.aestronglyMeasurable_iInf_of_antitone`.
-/

public section

open Filter MeasureTheory Set TauCeti.MeasureTheory TauCeti.Probability

open scoped ENNReal

namespace TauCeti

namespace Subshift

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [Countable I] [TopologicalSpace S]
  [MeasurableSpace S] {X : Subshift Γ I S} {μ : Measure X}

omit [Countable I] in
/-- An event measurable for the exterior σ-algebra of every finite set is measurable. -/
theorem measurableSet_of_forall_measurableSet_exterior {A : Set X}
    (hA : ∀ Λ : Finset I, MeasurableSet[X.exterior Λ] A) : MeasurableSet A :=
  X.exterior_le _ A (hA ∅)

/-- **An exhaustion by finite sets.** Over a countable index set, some sequence of finite sets
`D n` has decreasing exterior σ-algebras, each exterior σ-algebra of a finite set being coarser
than that of some `D n`. -/
theorem exists_antitone_exterior_forall_exists_le :
    ∃ D : ℕ → Finset I, Antitone (fun n => X.exterior (D n : Set I)) ∧
      ∀ Λ : Finset I, ∃ n, X.exterior (D n : Set I) ≤ X.exterior Λ := by
  obtain ⟨D, hDmono, hD⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop (Finset I)
  refine ⟨D, fun _ _ hmn => X.exterior_anti (Finset.coe_subset.2 (hDmono hmn)), fun Λ => ?_⟩
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.1 hD Λ).exists
  exact ⟨n, X.exterior_anti (Finset.coe_subset.2 hn)⟩

/-- **Versions measurable for every exterior σ-algebra.** On a subshift over a countable index set,
if a function `f : X → ℝ≥0∞` agrees `μ`-almost everywhere with an `𝓕_{Λᶜ}`-measurable function for
each finite `Λ`, then it agrees `μ`-almost everywhere with a single function measurable for the
exterior σ-algebra of every finite set. -/
theorem exists_forall_measurable_exterior_ae_eq_of_forall_exists {f : X → ℝ≥0∞}
    (h : ∀ Λ : Finset I, ∃ g : X → ℝ≥0∞, Measurable[X.exterior Λ] g ∧ g =ᵐ[μ] f) :
    ∃ g : X → ℝ≥0∞, (∀ Λ : Finset I, Measurable[X.exterior Λ] g) ∧ g =ᵐ[μ] f := by
  -- An exhaustion of `I` by finite sets `D n`, along which the exterior σ-algebras decrease.
  obtain ⟨D, hanti, hD⟩ := X.exists_antitone_exterior_forall_exists_le
  have hf := aestronglyMeasurable_iInf_of_antitone (μ := μ) hanti f fun n => by
    obtain ⟨g, hg, hgf⟩ := h (D n)
    exact ⟨g, hg.stronglyMeasurable, hgf.symm⟩
  refine ⟨hf.mk f, fun Λ => ?_, hf.ae_eq_mk.symm⟩
  obtain ⟨n, hn⟩ := hD Λ
  exact hf.stronglyMeasurable_mk.measurable.mono ((iInf_le _ n).trans hn) le_rfl

variable [IsFiniteMeasure μ] [SMulInvariantMeasure Γ X μ]

/-- **Invariant events of a subshift are almost surely exterior events.** If every finite subset of
the countable index set can be moved off every finite subset by the group, then for a finite
invariant measure on a subshift `X` every null-measurable almost invariant event agrees almost
everywhere with an event measurable for the exterior σ-algebra of every finite set. -/
theorem exists_forall_measurableSet_exterior_ae_eq
    (hmove : ∀ F Λ : Finset I, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ)
    {A : Set X} (hA : NullMeasurableSet A μ) (hAg : ∀ g : Γ, (fun ω => g • ω) ⁻¹' A =ᵐ[μ] A) :
    ∃ T : Set X, (∀ Λ : Finset I, MeasurableSet[X.exterior Λ] T) ∧ T =ᵐ[μ] A := by
  -- Replace `A` by a measurable version, the trace of an event `A'` of `I → S`.
  obtain ⟨A₀, hA₀A, hA₀, hA₀μ⟩ := hA.exists_measurable_subset_ae_eq
  have hA₀g (g : Γ) : (fun ω => g • ω) ⁻¹' A₀ =ᵐ[μ] A₀ :=
    preimage_smul_ae_eq_self_of_ae_eq hA₀μ (hAg g)
  obtain ⟨A', hA', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA₀
  -- Push `μ` forward to `I → S`, where the shifts preserve it.
  have hval : Measurable (Subtype.val : X → I → S) := measurable_subtypeVal
  have hshift (g : Γ) : Measurable fun (ω : I → S) i => ω (g⁻¹ • i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hν (g : Γ) : MeasurePreserving (fun (ω : I → S) i => ω (g⁻¹ • i))
      (μ.map Subtype.val) (μ.map Subtype.val) :=
    (MeasurePreserving.of_semiconj (μb := μ.map Subtype.val) ⟨hval, rfl⟩
      (measurePreserving_smul g μ) (fun ω => (coe_smul g ω).symm) (hshift g))
  -- Almost equality of events of `I → S` under the push-forward is that of their traces.
  have hae {s t : Set (I → S)} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      s =ᵐ[μ.map Subtype.val] t ↔ Subtype.val ⁻¹' s =ᵐ[μ] Subtype.val ⁻¹' t := by
    simp only [Filter.eventuallyEqSet_iff]
    exact ae_map_iff hval.aemeasurable (hs.iff ht)
  obtain ⟨T, hT, hTA⟩ := exists_measurableSet_tailEvents_ae_eq hmove hν hA'.nullMeasurableSet
    fun g => (hae (hshift g hA') hA').2 (hA₀g g)
  refine ⟨Subtype.val ⁻¹' T, fun Λ => ?_, ((hae (tailEvents_le_pi T hT) hA').1 hTA).trans hA₀μ⟩
  rw [exterior_def]
  exact MeasurableSpace.measurableSet_comap.2 ⟨T, measurableSet_tailEvents_iff.1 hT Λ, rfl⟩

/-- **Invariant functions on a subshift are almost surely exterior-measurable.** If every finite
subset of the countable index set can be moved off every finite subset by the group, then for a
finite invariant measure `μ` on a subshift `X` every almost invariant, almost everywhere measurable
function `X → ℝ≥0∞` agrees almost everywhere with a function measurable for the exterior σ-algebra
of every finite set. -/
theorem exists_forall_measurable_exterior_ae_eq
    (hmove : ∀ F Λ : Finset I, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ)
    {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hfg : ∀ g : Γ, f ∘ (fun ω => g • ω) =ᵐ[μ] f) :
    ∃ f' : X → ℝ≥0∞, (∀ Λ : Finset I, Measurable[X.exterior Λ] f') ∧ f' =ᵐ[μ] f := by
  obtain ⟨f', hf', hf'f⟩ := exists_measurable_ae_eq_of_forall_superlevel
    (m := ⨅ Λ : Finset I, X.exterior Λ) (μ := μ) (f := f) fun q => by
      obtain ⟨T, hT, hTf⟩ := exists_forall_measurableSet_exterior_ae_eq hmove
        (hf.nullMeasurable measurableSet_Ioi) fun g => by
          rw [← preimage_comp]; exact (hfg g).preimage _
      exact ⟨T, MeasurableSpace.measurableSet_iInf.2 hT, hTf⟩
  exact ⟨f', fun Λ => hf'.mono (iInf_le _ Λ) le_rfl, hf'f⟩

end Subshift

end TauCeti
