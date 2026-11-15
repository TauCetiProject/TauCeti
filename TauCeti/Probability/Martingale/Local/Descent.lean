/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Completion
public import TauCeti.Probability.Martingale.CountableStopping
public import TauCeti.Probability.Martingale.Local.Centering
public import TauCeti.Probability.Martingale.Local.Dominated
public import TauCeti.Probability.Process.CountableLevelLocalizer

/-!
# Descent of continuous local martingales to smaller filtrations

On a finite measure space, an `ℝ≥0`-indexed process strongly adapted to a smaller filtration
with almost surely continuous paths remains a native local martingale there if it is a native
local martingale in a larger filtration on the same measure space. Neither filtration needs
completeness or right continuity. The conclusion supplies
actual stopping times of the smaller filtration, not just martingale versions of stopped paths.
This allows constructions made with extra information to be used on the original filtration.

Centering at the initial value preserves native locality without any initial moment assumption.
Countable-range level localizers constructed in the smaller filtration bound the centered
stopped stages. Countable-range stopping preserves native local martingales; boundedness then
makes these stages true martingales in the larger filtration, and their adaptedness gives the
smaller-filtration martingale identities. The centering dictionary then restores the initial value.
A second theorem allows the larger filtration to live on the completed ambient space, using
`ProbabilityTheory.Locally.martingale_completion_iff` to transfer the resulting raw localizers
back unchanged.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ 𝒢 : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → E}

/-- On a finite measure space, an `ℝ≥0`-indexed process strongly adapted to a smaller
filtration with almost surely continuous paths is a native local martingale there whenever
it is one in a larger filtration on the same measure space. No usual conditions or
integrability of the initial value are assumed. -/
theorem StronglyAdapted.locally_martingale_of_le (hX : StronglyAdapted ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) (hFG : ∀ t, ℱ t ≤ 𝒢 t)
    (hlocal : Locally (fun Y ↦ Martingale Y 𝒢 P) 𝒢 X P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := by
  classical
  -- The centering dictionary handles arbitrary initial values without extra cutoffs here.
  apply ((hX 0).locally_martingale_sub_initialValue_iff (P := P) (ℱ := ℱ) (X := X)).mp
  let Y (t : ℝ≥0) (ω : Ω) := X t ω - X 0 ω
  have hY : StronglyAdapted ℱ Y := fun t ↦ (hX t).sub ((hX 0).mono (ℱ.mono bot_le))
  have hcY : ∀ᵐ ω ∂P, Continuous (Y · ω) :=
    hc.mono fun ω hω ↦ hω.sub continuous_const
  obtain ⟨η, hη, hcount, _, hbound⟩ :=
    hY.exists_isLocalizingSequence_countable_range_level hcY
  let Z (n : ℕ) := MeasureTheory.stoppedProcess
    (fun t ↦ {ω | 0 < η n ω}.indicator (Y t)) (η n)
  have hZF (n : ℕ) : StronglyAdapted ℱ (Z n) := by
    simp only [Z, stoppedProcess_indicator_comm']
    intro t
    exact ((hY.stoppedProcess_of_countable_range (hη.isStoppingTime n) (hcount n)) t).indicator
      (ℱ.mono bot_le _ ((hη.isStoppingTime n).measurableSet_gt 0))
  have hZbound (n : ℕ) : ∀ᵐ ω ∂P, ∀ t, ‖Z n t ω‖ ≤ (n : ℝ) + 1 := by
    filter_upwards [hbound] with ω hω t
    simp only [Z, stoppedProcess_indicator_comm', Set.indicator_apply]
    split_ifs
    · simpa only [Y, sub_self, sub_zero] using (hω n).2 t
    · simp only [norm_zero]
      positivity
  refine ⟨η, hη, fun n ↦ ?_⟩
  -- Upgrade in the larger filtration, then restrict the martingale test events.
  have hηG := (hη.isStoppingTime n).mono_filtration hFG
  have hZG : StronglyAdapted 𝒢 (Z n) := fun t ↦ (hZF n t).mono (hFG t)
  have hm : Martingale (Z n) 𝒢 P :=
    hZG.martingale_of_locally_martingale_of_bounded
      (hlocal.martingale_sub_initialValue.martingale_stoppedProcess_indicator_of_countable_range
        hηG (hcount n))
      (fun _ ↦ ⟨(n : ℝ) + 1, (hZbound n).mono fun ω hω t _ ↦ hω t⟩)
  exact ((hZF n).martingale_iff_setIntegral_eq (fun t ↦ hm.integrable t)).2
    (fun s t hst B hB ↦ hm.setIntegral_eq hst (hFG s _ hB))

/-- On a finite measure space, an `ℝ≥0`-indexed process strongly adapted to `ℱ` with
`P`-almost surely continuous paths is a native local martingale for `(ℱ, P)` if it is a
native local martingale for a larger filtration `𝒢` on `(NullMeasurableSpace Ω P, P.completion)`.
The resulting localizing times are stopping times of the original raw filtration `ℱ`. -/
theorem StronglyAdapted.locally_martingale_of_le_completion (hX : StronglyAdapted ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω))
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P))}
    (hFG : ∀ t, ℱ t ≤ 𝒢 t)
    (hlocal : @Locally ℝ≥0 (NullMeasurableSpace Ω P) E _ _ _ _ _ _
      (fun Y ↦ Martingale Y 𝒢 P.completion) 𝒢 X P.completion) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := by
  let : @IsFiniteMeasure (NullMeasurableSpace Ω P) _ P.completion :=
    ⟨lt_of_eq_of_lt (Measure.completion_apply P univ) (measure_lt_top P univ)⟩
  apply ProbabilityTheory.Locally.martingale_completion_iff.mp
  exact StronglyAdapted.locally_martingale_of_le (P := P.completion) (𝒢 := 𝒢)
    ((stronglyAdapted_monoAmbient_iff _).mpr hX)
    (hc.filter_mono P.ae_completion.le) hFG hlocal

end MeasureTheory
