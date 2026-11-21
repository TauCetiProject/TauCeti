/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Sets.Opens

/-!
# Restricted measures

A restricted pushforward equal to a scalar multiple of a measure gives a factorization
of preimage-event probabilities. This converts restricted distribution identities into
independence identities without requiring the restricting event to be measurable.

Restricting a measure to the whole space, written as the top open set, does not change it
(`MeasureTheory.Measure.restrict_coe_opens_top`), and neither does its almost-everywhere filter
(`MeasureTheory.Measure.ae_restrict_coe_opens_top`), so almost-everywhere statements for the
measure hold for the restriction (`MeasureTheory.Measure.ae_le_ae_restrict_coe_opens_top`).
Spaces of functions on an open set `Ω` are built on `μ.restrict Ω`, so this identifies their
whole-space instances with the spaces for `μ`.

On a finite type, the restriction of a measure to its points of finite mass is a finite measure
(`MeasureTheory.Measure.isFiniteMeasure_restrict_setOf_measure_singleton_ne_top`).

Two functions agree almost everywhere on a null-measurable set `s` exactly when their indicators
of `s` agree almost everywhere (`MeasureTheory.ae_eq_restrict_iff_indicator_ae_eq₀`, the
null-measurable form of Mathlib's `MeasureTheory.ae_eq_restrict_iff_indicator_ae_eq`).

Splitting a restriction along a second set `E` bounds it by the restriction to `s ∩ E` plus the
mass of `Eᶜ` under the restriction to `s`, with no measurability assumption
(`MeasureTheory.Measure.restrict_apply_le_restrict_inter_add_compl`); this is the counting step of
the comparison between conditioning on `s` and on `s ∩ E`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Restricting a measure to the whole space, as the top open set, does not change it. -/
theorem restrict_coe_opens_top {α : Type*} {_ : MeasurableSpace α} [TopologicalSpace α]
    (μ : Measure α) :
    μ.restrict ((⊤ : TopologicalSpace.Opens α) : Set α) = μ := by
  rw [TopologicalSpace.Opens.coe_top, restrict_univ]

/-- Almost everywhere for the restriction of a measure to the whole space, as the top open set,
is almost everywhere for the measure itself. -/
theorem ae_restrict_coe_opens_top {α : Type*} {_ : MeasurableSpace α} [TopologicalSpace α]
    (μ : Measure α) :
    ae (μ.restrict ((⊤ : TopologicalSpace.Opens α) : Set α)) = ae μ :=
  congrArg ae (restrict_coe_opens_top μ)

/-- Almost-everywhere statements for a measure hold for its restriction to the whole space, as
the top open set. -/
theorem ae_le_ae_restrict_coe_opens_top {α : Type*} {_ : MeasurableSpace α} [TopologicalSpace α]
    {μ : Measure α} : ae μ ≤ ae (μ.restrict ((⊤ : TopologicalSpace.Opens α) : Set α)) :=
  (ae_restrict_coe_opens_top μ).ge

/-- Restricting `μ` to `s` gives an event `A` at most the mass that the restriction to `s ∩ E`
gives `A`, plus the mass that the restriction to `s` gives `Eᶜ`. No set needs to be measurable. -/
theorem restrict_apply_le_restrict_inter_add_compl {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s E A : Set α) :
    μ.restrict s A ≤ μ.restrict (s ∩ E) A + μ.restrict s Eᶜ := calc
  μ.restrict s A ≤ μ.restrict (s ∩ E) A + μ.restrict (s \ E) A := by
    conv_lhs => rw [← Set.inter_union_sdiff s E]
    exact (le_iff'.1 (restrict_union_le _ _) A).trans_eq (_root_.add_apply _ _ _)
  _ ≤ μ.restrict (s ∩ E) A + μ.restrict s Eᶜ := by
    -- The part of `s` outside `E` has mass at most that of `Eᶜ` under the restriction to `s`.
    refine add_le_add le_rfl ((measure_mono A.subset_univ).trans ?_)
    rw [restrict_apply_univ, Set.sdiff_eq, Set.inter_comm]
    exact le_restrict_apply _ _

end MeasureTheory.Measure

namespace TauCeti

/-- Evaluate a restricted distribution identity on a measurable event. -/
theorem measure_preimage_inter_eq_of_map_restrict_eq_smul
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {μ : Measure E} {f : Ω → E} {H : Set Ω} {C : Set E} {c : ℝ≥0∞}
    (hf : Measurable f) (hC : MeasurableSet C) (h : (P.restrict H).map f = c • μ) :
    P (f ⁻¹' C ∩ H) = c * μ C := by
  simpa only [Measure.map_apply hf hC, Measure.restrict_apply (hf hC),
    smul_apply, smul_eq_mul] using congrArg (fun ν : Measure E ↦ ν C) h

end TauCeti

namespace MeasureTheory

/-- Functions agree almost everywhere on a null-measurable set `s` if and only if their indicators
of `s` agree almost everywhere.  This is `MeasureTheory.ae_eq_restrict_iff_indicator_ae_eq` for a
null-measurable rather than measurable `s`. -/
theorem ae_eq_restrict_iff_indicator_ae_eq₀ {α β : Type*} [MeasurableSpace α] [Zero β]
    {μ : Measure α} {s : Set α} {f g : α → β} (hs : NullMeasurableSet s μ) :
    f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] s.indicator g := by
  rw [Filter.EventuallyEq, ae_restrict_iff'₀ hs]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with x hx
  · by_cases hxs : x ∈ s
    · simp [hxs, hx hxs]
    · simp [hxs]
  · intro hxs
    simpa [hxs] using hx

end MeasureTheory

namespace MeasureTheory.Measure

/-- On a finite type, the restriction of a measure to the points of finite mass is finite. -/
theorem isFiniteMeasure_restrict_setOf_measure_singleton_ne_top {α : Type*} [Finite α]
    [MeasurableSpace α] (ν : Measure α) :
    IsFiniteMeasure (ν.restrict {x | ν {x} ≠ ⊤}) := by
  rw [isFiniteMeasure_restrict]
  have h := measure_biUnion_ne_top (μ := ν) (Set.toFinite {x | ν {x} ≠ ⊤})
    (f := fun x ↦ {x}) fun x hx ↦ hx
  rwa [Set.biUnion_of_singleton] at h

end MeasureTheory.Measure
