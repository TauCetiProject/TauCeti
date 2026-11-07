/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.Probability.Process.Indistinguishable

/-!
# Local martingales and progressive representatives

A strongly progressive process is a native local martingale whenever its native stopped
stages have martingale versions. Progressivity supplies literal adaptation at arbitrary-range
stopping times, even on a raw filtration. The same localizing sequence can therefore be kept.

Consequently, replacing a native local martingale by an indistinguishable strongly progressive
process preserves native locality. The original process need not be adapted or progressive.
Equality almost surely at each deterministic time alone would not suffice for this replacement:
the localizing times can sample different exceptional sets.

All statements retain the native initial-time indicator, which suppresses the entire stopped
path when the localizer is zero. No completeness, right continuity of the filtration, path
regularity, or integrability of the original initial value is assumed.

The proofs use Mathlib's `Martingale.congr`, progressive stopped-process measurability and
`ProbabilityTheory.Locally`. For the local-martingale and version conventions, see
Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, second edition, Chapter 1, §5.
-/

public section

open ProbabilityTheory TopologicalSpace

namespace MeasureTheory.IsStronglyProgressive

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [PseudoMetrizableSpace ι] [MeasurableSpace ι] [BorelSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι mΩ} {X Y : ι → Ω → E}

/-- A strongly progressive process is a native local martingale if every native stopped stage
has a martingale version. The supplied localizing sequence is retained, including its
initial-time indicators. Since the stopped stages themselves are literally adapted, equality
with their martingale versions is needed only almost surely at each fixed time. -/
theorem locally_martingale_of_ae_stopped_eq (hX : IsStronglyProgressive ℱ X)
    {τ : ℕ → Ω → WithTop ι} (hτ : IsLocalizingSequence ℱ τ μ)
    {Z : ℕ → ι → Ω → E} (hZ : ∀ n, Martingale (Z n) ℱ μ)
    (heq : ∀ n t, Z n t =ᵐ[μ]
      MeasureTheory.stoppedProcess
        (fun s ↦ {ω | (⊥ : WithTop ι) < τ n ω}.indicator (X s)) (τ n) t) :
    Locally (fun U ↦ Martingale U ℱ μ) ℱ X μ := by
  refine ⟨τ, hτ, fun n ↦ (hZ n).congr (fun t ↦ ?_) (heq n)⟩
  rw [stoppedProcess_indicator_comm']
  exact ((hX.stoppedProcess (hτ.isStoppingTime n)).stronglyAdapted t).indicator
    (ℱ.mono bot_le _ ((hτ.isStoppingTime n).measurableSet_gt ⊥))

/-- An indistinguishable strongly progressive replacement of a native local martingale is a
native local martingale, with the same localizing sequence. No adaptation assumption is
imposed on the original process. The equality must hold simultaneously in time almost surely,
so it can be evaluated at the random stopped times. -/
theorem locally_martingale_of_indist (hY : IsStronglyProgressive ℱ Y)
    (hX : Locally (fun U ↦ Martingale U ℱ μ) ℱ X μ)
    (heq : X ≡ᵐ[μ] Y) :
    Locally (fun U ↦ Martingale U ℱ μ) ℱ Y μ := by
  apply hY.locally_martingale_of_ae_stopped_eq hX.isLocalizingSequence_localSeq
    hX.stoppedProcess_localSeq
  intro n t
  filter_upwards [heq] with ω hω
  simp only [stoppedProcess_indicator_comm', Set.indicator_apply]
  split_ifs
  · exact hω _
  · rfl

end MeasureTheory.IsStronglyProgressive
