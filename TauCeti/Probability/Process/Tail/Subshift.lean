/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.SymbolicDynamics.Subshift
public import TauCeti.Probability.Process.Tail.ProperAction
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
-/

public section

open Filter MeasureTheory Set TauCeti.MeasureTheory TauCeti.Probability

open scoped ENNReal

namespace TauCeti

namespace Subshift

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [Countable I] [TopologicalSpace S]
  [MeasurableSpace S] {X : Subshift Γ I S} {μ : Measure X} [IsFiniteMeasure μ]
  [SMulInvariantMeasure Γ X μ]

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
