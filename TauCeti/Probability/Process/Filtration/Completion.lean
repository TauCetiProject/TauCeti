/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.MeasureTheory.Function.ConditionalExpectation.Completion

/-!
# Raw filtrations on completed ambient spaces

`Filtration.monoAmbient` regards a filtration as a filtration on a larger ambient
measurable space, without adding any events to its time slices. In particular, this
allows a raw filtration to be used on the completion of its underlying measure space.
This operation is distinct from null augmentation of the filtration.

Ambient completion preserves the sigma-finiteness of raw filtration trims and
preserves and reflects native localizing sequences, with exactly the same stopping
times. These are the filtration and stopping adapters used to transport local
martingale conclusions back to an uncompleted stochastic basis.
-/

public section

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} [Preorder ι] {m₁ m₂ m₃ : MeasurableSpace Ω}

/-- Regard a filtration as a filtration on a larger ambient measurable space.
Every time slice remains unchanged. This is a reducible rebundling, so types of
functions measurable in a raw time slice do not acquire casts. -/
abbrev monoAmbient (ℱ : Filtration ι m₁) (h : m₁ ≤ m₂) : Filtration ι m₂ where
  seq := ℱ
  mono' _ _ hij := ℱ.mono hij
  le' t := (ℱ.le t).trans h

@[simp]
theorem monoAmbient_apply (ℱ : Filtration ι m₁) (h : m₁ ≤ m₂) (t : ι) :
    ℱ.monoAmbient h t = ℱ t := (rfl)

@[simp]
theorem monoAmbient_refl (ℱ : Filtration ι m₁) : ℱ.monoAmbient le_rfl = ℱ := by
  apply Filtration.ext
  rfl

@[simp]
theorem monoAmbient_trans (ℱ : Filtration ι m₁) (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₃) :
    (ℱ.monoAmbient h₁).monoAmbient h₂ = ℱ.monoAmbient (h₁.trans h₂) := by
  apply Filtration.ext
  rfl

end MeasureTheory.Filtration

namespace MeasureTheory

variable {Ω ι E : Type*} [Preorder ι] {m m' : MeasurableSpace Ω}
  {ℱ : Filtration ι m}

/-- Strong adaptation depends only on the time slices, not on the ambient space. -/
@[simp]
theorem stronglyAdapted_monoAmbient_iff [TopologicalSpace E] (h : m ≤ m')
    {X : ι → Ω → E} : StronglyAdapted (ℱ.monoAmbient h) X ↔ StronglyAdapted ℱ X :=
  (Iff.rfl)

/-- Enlarging the ambient measurable space does not change raw stopping times. -/
@[simp]
theorem isStoppingTime_monoAmbient_iff (h : m ≤ m') {τ : Ω → WithTop ι} :
    IsStoppingTime (ℱ.monoAmbient h) τ ↔ IsStoppingTime ℱ τ := (Iff.rfl)

end MeasureTheory

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
  {P : Measure Ω} {ℱ : Filtration ι mΩ}

/-- Ambient completion preserves sigma-finiteness of every raw filtration trim. -/
instance sigmaFiniteFiltration_completion
    [SigmaFiniteFiltration P ℱ] :
    @SigmaFiniteFiltration (NullMeasurableSpace Ω P) ι _ _
      P.completion (ℱ.monoAmbient le_eventuallyMeasurableSpace) where
  SigmaFinite t := by
    exact (P.trim_completion (ℱ.le t)).symm ▸
      (inferInstance : SigmaFinite (P.trim (ℱ.le t)))

end MeasureTheory.Filtration

namespace ProbabilityTheory

open MeasureTheory Filter

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [Preorder ι] {ℱ : Filtration ι mΩ} [TopologicalSpace ι] [OrderTopology ι]

/-- A raw pre-localizing sequence remains exactly the same pre-localizing sequence
under ambient completion, in either direction. -/
@[simp]
theorem isPreLocalizingSequence_completion_iff {τ : ℕ → Ω → WithTop ι} :
    @IsPreLocalizingSequence ι (NullMeasurableSpace Ω P) _ _ _ _
      (ℱ.monoAmbient le_eventuallyMeasurableSpace) τ P.completion ↔
      IsPreLocalizingSequence ℱ τ P := by
  constructor
  · intro hτ
    exact ⟨fun n ↦ (isStoppingTime_monoAmbient_iff _).mp (hτ.isStoppingTime n),
      P.ae_completion ▸ hτ.tendsto_top⟩
  · intro hτ
    exact ⟨fun n ↦ (isStoppingTime_monoAmbient_iff _).mpr (hτ.isStoppingTime n),
      P.ae_completion.symm ▸ hτ.tendsto_top⟩

/-- Ambient completion preserves and reflects raw localizing sequences, including
their almost-sure monotonicity. No replacement of the stopping times is needed. -/
@[simp]
theorem isLocalizingSequence_completion_iff {τ : ℕ → Ω → WithTop ι} :
    @IsLocalizingSequence ι (NullMeasurableSpace Ω P) _ _ _ _
      (ℱ.monoAmbient le_eventuallyMeasurableSpace) τ P.completion ↔
      IsLocalizingSequence ℱ τ P := by
  constructor
  · intro hτ
    exact ⟨isPreLocalizingSequence_completion_iff.mp hτ.toIsPreLocalizingSequence,
      P.ae_completion ▸ hτ.mono⟩
  · intro hτ
    exact ⟨isPreLocalizingSequence_completion_iff.mpr hτ.toIsPreLocalizingSequence,
      P.ae_completion.symm ▸ hτ.mono⟩

end ProbabilityTheory

namespace ProbabilityTheory.Locally

open MeasureTheory

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [Zero E] [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

/-- Pointwise-equivalent process properties have equivalent native locality statements
across ambient completion, with the same localizers and positive-time indicators. -/
theorem completion_iff (h : ∀ Y, p Y ↔ q Y) :
    @Locally ι (NullMeasurableSpace Ω P) E _ _ _ _ _ _
      p (ℱ.monoAmbient le_eventuallyMeasurableSpace) X P.completion ↔
      Locally q ℱ X P := by
  constructor
  · rintro ⟨τ, hτ, hp⟩
    exact ⟨τ, isLocalizingSequence_completion_iff.mp hτ, fun n ↦ (h _).mp (hp n)⟩
  · rintro ⟨τ, hτ, hq⟩
    exact ⟨τ, isLocalizingSequence_completion_iff.mpr hτ, fun n ↦ (h _).mpr (hq n)⟩

end ProbabilityTheory.Locally
