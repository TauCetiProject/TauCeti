module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Conditional expectation of an indicator under pair-law equality

`condExp_indicator_eq_of_pair_law_eq`: if the pairs `(Y, Z)` and `(Y', Z)` have the same law, then
for every measurable `B` the conditional expectations of `𝟙_B ∘ Y` and `𝟙_B ∘ Y'` given `σ(Z)` agree
almost everywhere.

This is the bridge that turns a pair-law (distributional) equality into a conditional-expectation
identity. It is consumed by the de Finetti block-product factorisation, where contractability
supplies the pair-law equality that extends the per-coordinate conditional law from `X 0` to every
`X n`.

Adapted from `cameronfreer/exchangeability` (`Probability/CondExp.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

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
  have h_lhs : ∫ ω in Z ⁻¹' E, f ω ∂μ = (μ (Y ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    have hf_eq : f = (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hf_def, Function.comp_apply, Set.indicator, Set.mem_preimage]
    simp_rw [hf_eq, integral_indicator (hY hB)]
    simp only [integral_const]
    simp_rw [Measure.restrict_restrict (hY hB)]
    simp only [smul_eq_mul, mul_one]
    simp [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have h_rhs_ce : ∫ ω in Z ⁻¹' E, μ[f' | mZ] ω ∂μ = ∫ ω in Z ⁻¹' E, f' ω ∂μ :=
    setIntegral_condExp hmZ_le hf'_int ⟨E, hE, rfl⟩
  have h_rhs : ∫ ω in Z ⁻¹' E, f' ω ∂μ = (μ (Y' ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
    have hf'_eq : f' = (Y' ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hf'_def, Function.comp_apply, Set.indicator, Set.mem_preimage]
    simp_rw [hf'_eq, integral_indicator (hY' hB)]
    simp only [integral_const]
    simp_rw [Measure.restrict_restrict (hY' hB)]
    simp only [smul_eq_mul, mul_one]
    simp [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  simp_rw [h_lhs, h_rhs_ce, h_rhs, h_meas_eq]

end Probability

end TauCeti
