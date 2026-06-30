module

public import Mathlib.Probability.Independence.Conditional
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Conditional independence from an indicator conditional-expectation criterion

Two adapters between Mathlib's `ProbabilityTheory.CondIndep` and the
indicator/conditional-expectation form used by the de Finetti block-product factorisation:

* `condIndep_of_indicator_condexp_eq` — builds `CondIndep mG mF mH` from the "drop-information"
  criterion `μ[𝟙_H | mF ⊔ mG] =ᵐ μ[𝟙_H | mG]` for all `mH`-measurable `H`;
* `condexp_indicator_inter_bridge` — the product formula
  `μ[𝟙_{A ∩ B} | m] =ᵐ μ[𝟙_A | m] * μ[𝟙_B | m]` extracted from `CondIndep`.

Both are thin layers over Mathlib's `condIndep_iff`; the work in the first is pulling the indicator
factors through the conditional expectation (`condExp_mul_of_aestronglyMeasurable_*`) and the tower
property (`condExp_condExp_of_le`).

Adapted from `cameronfreer/exchangeability` (`Probability/CondExp.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

/-- **Conditional independence from the drop-information criterion.** If conditioning `𝟙_H` on
`mF ⊔ mG` is a.e. the same as conditioning on `mG` (for every `mH`-measurable `H`), then `mF` and
`mH` are conditionally independent given `mG`. -/
theorem condIndep_of_indicator_condexp_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (h : ∀ H, MeasurableSet[mH] H →
      μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG]) :
    CondIndep mG mF mH hmG μ := by
  classical
  refine (condIndep_iff mG mF mH hmG hmF hmH μ).2 ?_
  intro tF tH htF htH
  set f1 : Ω → ℝ := tF.indicator (fun _ : Ω => (1 : ℝ)) with hf1
  set f2 : Ω → ℝ := tH.indicator (fun _ : Ω => (1 : ℝ)) with hf2
  have hf1_int : Integrable f1 μ := Integrable.indicator (integrable_const (1 : ℝ)) (hmF _ htF)
  have hf2_int : Integrable f2 μ := Integrable.indicator (integrable_const (1 : ℝ)) (hmH _ htH)
  have hf1_aesm : AEStronglyMeasurable[mF ⊔ mG] f1 μ :=
    ((stronglyMeasurable_const.indicator htF).aestronglyMeasurable).mono
      (le_sup_left : mF ≤ mF ⊔ mG)
  have hProj : μ[f2 | mF ⊔ mG] =ᵐ[μ] μ[f2 | mG] := h tH htH
  have h_tower : μ[(fun ω => f1 ω * f2 ω) | mG]
      =ᵐ[μ] μ[ μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] | mG] := by
    simpa using (condExp_condExp_of_le (μ := μ) (hm₁₂ := le_sup_right) (hm₂ := sup_le hmF hmG)
      (f := fun ω => f1 ω * f2 ω)).symm
  have hf1f2_int : Integrable (fun ω => f1 ω * f2 ω) μ := by
    have heq : (fun ω => f1 ω * f2 ω) = (tF ∩ tH).indicator (fun _ : Ω => (1 : ℝ)) := by
      funext ω; by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;>
        simp [hf1, hf2, Set.indicator, h1, h2, Set.mem_inter_iff] at *
    rw [heq]
    exact Integrable.indicator (integrable_const (1 : ℝ))
      (MeasurableSet.inter (hmF _ htF) (hmH _ htH))
  have h_pull_middle : μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] :=
    condExp_mul_of_aestronglyMeasurable_left (μ := μ) (m := mF ⊔ mG) hf1_aesm hf1f2_int hf2_int
  have h_middle_to_G : μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] =ᵐ[μ] f1 * μ[f2 | mG] :=
    h_pull_middle.trans <| Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hProj
  have hf1_condexp_int : Integrable (f1 * μ[f2 | mG]) μ := by
    have heq : f1 * μ[f2 | mG] = tF.indicator (fun ω => μ[f2 | mG] ω) := by
      funext ω; by_cases hω : ω ∈ tF <;> simp [hf1, Set.indicator, hω]
    rw [heq]
    exact Integrable.indicator (integrable_condExp (μ := μ) (m := mG) (f := f2)) (hmF _ htF)
  have h_pull_outer : μ[f1 * μ[f2 | mG] | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    condExp_mul_of_aestronglyMeasurable_right (μ := μ) (m := mG)
      (stronglyMeasurable_condExp (μ := μ) (m := mG) (f := f2)).aestronglyMeasurable
      hf1_condexp_int hf1_int
  have h_prod : μ[(fun ω => f1 ω * f2 ω) | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    h_tower.trans ((condExp_congr_ae h_middle_to_G).trans h_pull_outer)
  have h_f1f2 : (fun ω => f1 ω * f2 ω) = (tF ∩ tH).indicator (fun _ => (1 : ℝ)) := by
    funext ω; by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;>
      simp [hf1, hf2, Set.indicator, h1, h2, Set.mem_inter_iff] at *
  rw [h_f1f2] at h_prod
  simpa only [hf1, hf2] using h_prod

/-- **Conditional-independence product formula for indicators.** From `CondIndep m mF mH`, the
conditional expectation of `𝟙_{A ∩ B}` factors as the product of the conditional expectations of
`𝟙_A` and `𝟙_B`, for `mF`-measurable `A` and `mH`-measurable `B`. -/
theorem condexp_indicator_inter_bridge {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m mF mH : MeasurableSpace Ω} (hm : m ≤ m₀)
    (hmF : mF ≤ m₀) (hmH : mH ≤ m₀) (hCI : CondIndep m mF mH hm μ) {A B : Set Ω}
    (hA : MeasurableSet[mF] A) (hB : MeasurableSet[mH] B) :
    μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]
      =ᵐ[μ] μ[A.indicator (fun _ => (1 : ℝ)) | m] * μ[B.indicator (fun _ => (1 : ℝ)) | m] :=
  (condIndep_iff m mF mH hm hmF hmH μ).mp hCI A B hA hB

end Probability

end TauCeti
