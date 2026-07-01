module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional expectation of an indicator under pair-law equality

`condExp_indicator_eq_of_pair_law_eq`: if the pairs `(Y, Z)` and `(Y', Z)` have the same law, then
for every measurable `B` the conditional expectations of `𝟙_B ∘ Y` and `𝟙_B ∘ Y'` given `σ(Z)` agree
almost everywhere.

This is a generic conditional-expectation fact (no exchangeability/tail/directing-measure
hypotheses); it is the bridge that turns a pair-law (distributional) equality into a
conditional-expectation identity, consumed by the de Finetti block-product factorisation.

Adapted from `cameronfreer/exchangeability` (`Probability/CondExp.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

/-- If the pairs `(Y, Z)` and `(Y', Z)` have the same law, then for measurable `B` the conditional
expectations of `𝟙_B ∘ Y` and `𝟙_B ∘ Y'` given `σ(Z)` agree almost everywhere. -/
theorem condExp_indicator_eq_of_pair_law_eq {Ω α β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace α] [mβ : MeasurableSpace β] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β) (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : μ.map (fun ω => (Y ω, Z ω)) = μ.map (fun ω => (Y' ω, Z ω)))
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y | MeasurableSpace.comap Z mβ]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y' | MeasurableSpace.comap Z mβ] := by
  classical
  set f := Set.indicator B (fun _ => (1 : ℝ)) ∘ Y with hf_def
  set f' := Set.indicator B (fun _ => (1 : ℝ)) ∘ Y' with hf'_def
  set mZ := MeasurableSpace.comap Z mβ with hmZ_def
  have hmZ_le : mZ ≤ mΩ := by
    rintro s ⟨E, hE, rfl⟩
    exact hZ hE
  have hf_int : Integrable f μ := Integrable.indicator (integrable_const (1 : ℝ)) (hY hB)
  have hf'_int : Integrable f' μ := Integrable.indicator (integrable_const (1 : ℝ)) (hY' hB)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmZ_le hf_int
    (fun s _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  obtain ⟨E, hE, rfl⟩ := hA
  have h_meas_eq : μ (Y ⁻¹' B ∩ Z ⁻¹' E) = μ (Y' ⁻¹' B ∩ Z ⁻¹' E) := by
    have h := congr_arg (fun ν => ν (B ×ˢ E)) hpair
    simp only [Measure.map_apply (hY.prodMk hZ) (hB.prod hE),
      Measure.map_apply (hY'.prodMk hZ) (hB.prod hE), Set.mk_preimage_prod] at h
    exact h
  -- The set-integral of a preimage indicator over `Z ⁻¹' E`, shared by both coordinates.
  have hint : ∀ W : Ω → α, Measurable[mΩ] W →
      ∫ ω in Z ⁻¹' E, (W ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ
        = (μ (W ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    intro W hW
    rw [setIntegral_indicator (hW hB), setIntegral_const, Set.inter_comm]
    simp [Measure.real]
  have h_lhs : ∫ ω in Z ⁻¹' E, f ω ∂μ = (μ (Y ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    have hf_eq : f = (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hf_def, Function.comp_apply, Set.indicator, Set.mem_preimage]
    rw [hf_eq]; exact hint Y hY
  have h_rhs_ce : ∫ ω in Z ⁻¹' E, μ[f' | mZ] ω ∂μ = ∫ ω in Z ⁻¹' E, f' ω ∂μ :=
    setIntegral_condExp hmZ_le hf'_int ⟨E, hE, rfl⟩
  have h_rhs : ∫ ω in Z ⁻¹' E, f' ω ∂μ = (μ (Y' ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    have hf'_eq : f' = (Y' ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hf'_def, Function.comp_apply, Set.indicator, Set.mem_preimage]
    rw [hf'_eq]; exact hint Y' hY'
  simp_rw [h_lhs, h_rhs_ce, h_rhs, h_meas_eq]

end MeasureTheory

end TauCeti
