module

public import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Conditional independence and the indicator conditional-expectation projection

The two directions relating Mathlib's `ProbabilityTheory.CondIndep` to the "drop-information"
identity `μ[𝟙_H | mF ⊔ mG] =ᵐ μ[𝟙_H | mG]` on conditional expectations of indicators:

* `condIndep_of_indicator_condExp_eq` — builds `CondIndep mG mF mH` from that criterion (for all
  `mH`-measurable `H`).
* `condExp_indicator_sup_eq_of_condIndep` — the converse projection: from `CondIndep mG mF mH`,
  conditioning an `mH`-measurable indicator on the join `mF ⊔ mG` collapses to conditioning on `mG`.

Both are intended for the de Finetti block-product factorisation / prefix-deletion drop-info step —
the standard conditional-independence characterisation of the de Finetti route; see Kallenberg,
*Probabilistic Symmetries and Invariance Principles* (Springer, 2005). Adapted from
`cameronfreer/exchangeability` (`Probability/CondExp.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

/-- **Conditional independence from the drop-information criterion.** If conditioning `𝟙_H` on
`mF ⊔ mG` is a.e. the same as conditioning on `mG` (for every `mH`-measurable `H`), then `mF` and
`mH` are conditionally independent given `mG`. -/
theorem condIndep_of_indicator_condExp_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
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
  -- The product of the two indicators is the indicator of the intersection; named once and reused.
  have h_f1f2 : (fun ω => f1 ω * f2 ω) = (tF ∩ tH).indicator (fun _ => (1 : ℝ)) := by
    funext ω; by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;>
      simp [hf1, hf2, Set.indicator, h1, h2, Set.mem_inter_iff] at *
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
    rw [h_f1f2]
    exact Integrable.indicator (integrable_const (1 : ℝ))
      (MeasurableSet.inter (hmF _ htF) (hmH _ htH))
  have h_pull_middle : μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] :=
    condExp_mul_of_aestronglyMeasurable_left (μ := μ) (m := mF ⊔ mG) hf1_aesm hf1f2_int hf2_int
  have h_middle_to_G : μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] =ᵐ[μ] f1 * μ[f2 | mG] :=
    h_pull_middle.trans <| Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hProj
  have hf1_condExp_int : Integrable (f1 * μ[f2 | mG]) μ := by
    have heq : f1 * μ[f2 | mG] = tF.indicator (fun ω => μ[f2 | mG] ω) := by
      funext ω; by_cases hω : ω ∈ tF <;> simp [hf1, Set.indicator, hω]
    rw [heq]
    exact Integrable.indicator (integrable_condExp (μ := μ) (m := mG) (f := f2)) (hmF _ htF)
  have h_pull_outer : μ[f1 * μ[f2 | mG] | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    condExp_mul_of_aestronglyMeasurable_right (μ := μ) (m := mG)
      (stronglyMeasurable_condExp (μ := μ) (m := mG) (f := f2)).aestronglyMeasurable
      hf1_condExp_int hf1_int
  have h_prod : μ[(fun ω => f1 ω * f2 ω) | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    h_tower.trans ((condExp_congr_ae h_middle_to_G).trans h_pull_outer)
  rw [h_f1f2] at h_prod
  simpa only [hf1, hf2] using h_prod

/-- Rectangle step for `condExp_indicator_sup_eq_of_condIndep`: over a rectangle `tF ∩ tG` (`tF`
`mF`-measurable, `tG` `mG`-measurable), the conditional expectation given `mG` of an
`mH`-measurable indicator integrates to the same value as the indicator itself. -/
private lemma setIntegral_condExp_indicator_eq_on_rectangle {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (hCI : CondIndep mG mF mH hmG μ)
    {H : Set Ω} (hH : MeasurableSet[mH] H)
    {tF tG : Set Ω} (htF : MeasurableSet[mF] tF) (htG : MeasurableSet[mG] tG) :
    ∫ x in tF ∩ tG, (μ[H.indicator (fun _ => (1 : ℝ)) | mG]) x ∂μ
      = ∫ x in tF ∩ tG, H.indicator (fun _ => (1 : ℝ)) x ∂μ := by
  classical
  let m0 : MeasurableSpace Ω := mΩ
  set f : Ω → ℝ := H.indicator (fun _ => (1 : ℝ)) with hf_def
  have htF_m0 : MeasurableSet[m0] tF := hmF _ htF
  set gB : Ω → ℝ := tF.indicator (fun _ => (1 : ℝ)) with hgB_def
  have hInt_ce : Integrable (μ[f | mG]) μ := integrable_condExp
  have h_mul_eq_indicator :
      (fun ω => μ[f | mG] ω * gB ω) = tF.indicator (μ[f | mG]) := by
    funext ω; by_cases hω : ω ∈ tF
    · simp only [hgB_def, Set.indicator_of_mem hω, mul_one]
    · simp only [hgB_def, Set.indicator_of_notMem hω, mul_zero]
  have hint_prod : Integrable (fun ω => μ[f | mG] ω * gB ω) μ := by
    simpa only [h_mul_eq_indicator] using hInt_ce.indicator htF_m0
  have hint_B : Integrable gB μ := Integrable.indicator (integrable_const 1) htF_m0
  have hfg : (f * gB) = (tF ∩ H).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [Pi.mul_apply, hf_def, hgB_def, Set.indicator_apply, Set.mem_inter_iff]
    by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ H <;> simp [h1, h2]
  have hprod_int : Integrable (f * gB) μ := by
    rw [hfg]
    exact Integrable.indicator (integrable_const 1) ((hmF _ htF).inter (hmH _ hH))
  have hprodf : μ[f * gB | mG] =ᵐ[μ] μ[f | mG] * μ[gB | mG] := by
    rw [hfg]
    exact ((condIndep_iff mG mF mH hmG hmF hmH μ).mp hCI _ _ htF hH).trans
      (Filter.EventuallyEq.of_eq (mul_comm _ _))
  have h_pull : μ[(μ[f | mG]) * gB | mG] =ᵐ[μ] (μ[f | mG]) * μ[gB | mG] :=
    condExp_mul_of_aestronglyMeasurable_left
      stronglyMeasurable_condExp.aestronglyMeasurable hint_prod hint_B
  calc ∫ x in tF ∩ tG, (μ[f | mG]) x ∂μ
      = ∫ x in tG, (μ[f | mG] * gB) x ∂μ := by
        have hh1 : ∫ ω in tG ∩ tF, μ[f | mG] ω ∂μ
            = ∫ ω in tG, tF.indicator (μ[f | mG]) ω ∂μ := by
          rw [setIntegral_indicator htF_m0]
        have hh2 : ∫ ω in tG, tF.indicator (μ[f | mG]) ω ∂μ
            = ∫ ω in tG, μ[f | mG] ω * gB ω ∂μ := by rw [h_mul_eq_indicator]
        rw [Set.inter_comm]; exact hh1.trans hh2
    _ = ∫ x in tG, (μ[f | mG] * μ[gB | mG]) x ∂μ := by
        have h_set_eq : ∫ x in tG, μ[(μ[f | mG]) * gB | mG] x ∂μ
            = ∫ x in tG, ((μ[f | mG]) * gB) x ∂μ :=
          setIntegral_condExp hmG hint_prod htG
        rw [← h_set_eq]
        exact setIntegral_congr_ae (hmG _ htG)
          (by filter_upwards [h_pull] with x hx _; exact hx)
    _ = ∫ x in tG, (μ[f * gB | mG]) x ∂μ :=
        setIntegral_congr_ae (hmG _ htG)
          (by filter_upwards [hprodf] with x hx _; exact hx.symm)
    _ = ∫ x in tG, (f * gB) x ∂μ := setIntegral_condExp hmG hprod_int htG
    _ = ∫ x in tF ∩ tG, f x ∂μ := by
        have h_fg : (f * gB) = tF.indicator f := by
          funext ω; simp only [Pi.mul_apply]; by_cases hω : ω ∈ tF
          · simp only [hgB_def, Set.indicator_of_mem hω, mul_one]
          · simp only [hgB_def, Set.indicator_of_notMem hω, mul_zero]
        rw [h_fg, Set.inter_comm tF, setIntegral_indicator htF_m0]

/-- **Projection from conditional independence.** If `mF` and `mH` are conditionally independent
given `mG` (in the sense of Mathlib's `ProbabilityTheory.CondIndep`), then conditioning the
indicator of an `mH`-measurable set `H` on the join `mF ⊔ mG` collapses to conditioning on `mG`.
This is the converse of `condIndep_of_indicator_condExp_eq`. -/
theorem condExp_indicator_sup_eq_of_condIndep {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (hCI : CondIndep mG mF mH hmG μ)
    {H : Set Ω} (hH : MeasurableSet[mH] H) :
    μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
      =ᵐ[μ]
    μ[H.indicator (fun _ => (1 : ℝ)) | mG] := by
  classical
  let m0 : MeasurableSpace Ω := mΩ
  let f : Ω → ℝ := H.indicator (fun _ => (1 : ℝ))
  have hmFG_le : mF ⊔ mG ≤ m0 := sup_le hmF hmG
  have hf_int : Integrable f μ := Integrable.indicator (integrable_const (1 : ℝ)) (hmH _ hH)
  -- The join `mF ⊔ mG` is generated by the π-system of intersections `tF ∩ tG`.
  have hgen : mF ⊔ mG = MeasurableSpace.generateFrom
      {s | ∃ tF tG, MeasurableSet[mF] tF ∧ MeasurableSet[mG] tG ∧ s = tF ∩ tG} := by
    refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨s, Set.univ, hs, MeasurableSet.univ, (Set.inter_univ s).symm⟩
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, s, MeasurableSet.univ, hs, (Set.univ_inter s).symm⟩
    · rintro s ⟨tF, tG, htF, htG, rfl⟩
      have h1 : MeasurableSet[mF ⊔ mG] tF := (le_sup_left : mF ≤ mF ⊔ mG) _ htF
      have h2 : MeasurableSet[mF ⊔ mG] tG := (le_sup_right : mG ≤ mF ⊔ mG) _ htG
      exact h1.inter h2
  have hpi : IsPiSystem
      {s | ∃ tF tG, MeasurableSet[mF] tF ∧ MeasurableSet[mG] tG ∧ s = tF ∩ tG} := by
    rintro s₁ ⟨tF₁, tG₁, htF₁, htG₁, rfl⟩ s₂ ⟨tF₂, tG₂, htF₂, htG₂, rfl⟩ _
    exact ⟨tF₁ ∩ tF₂, tG₁ ∩ tG₂, htF₁.inter htF₂, htG₁.inter htG₂, by
      ext ω; simp only [Set.mem_inter_iff]; tauto⟩
  have hgm : AEStronglyMeasurable[mF ⊔ mG] (μ[f | mG]) μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.mono le_sup_right
  have hg_eq : ∀ s : Set Ω, MeasurableSet[mF ⊔ mG] s → μ s < ∞ →
      ∫ x in s, (μ[f | mG]) x ∂μ = ∫ x in s, f x ∂μ := by
    intro s hs _
    apply MeasurableSpace.induction_on_inter
      (C := fun s _ => ∫ x in s, (μ[f | mG]) x ∂μ = ∫ x in s, f x ∂μ) hgen hpi
    · simp
    · rintro t ⟨tF, tG, htF, htG, rfl⟩
      exact setIntegral_condExp_indicator_eq_on_rectangle hmF hmG hmH hCI hH htF htG
    · intro t htm ht_ind
      have h_add : ∫ x in t, (μ[f | mG]) x ∂μ + ∫ x in tᶜ, (μ[f | mG]) x ∂μ
          = ∫ x, (μ[f | mG]) x ∂μ :=
        integral_add_compl₀ (hmFG_le _ htm).nullMeasurableSet integrable_condExp
      have h_add' : ∫ x in t, f x ∂μ + ∫ x in tᶜ, f x ∂μ = ∫ x, f x ∂μ :=
        integral_add_compl₀ (hmFG_le _ htm).nullMeasurableSet hf_int
      rw [ht_ind] at h_add
      have h_total : ∫ x, (μ[f | mG]) x ∂μ = ∫ x, f x ∂μ := integral_condExp hmG
      linarith
    · intro t_seq hdisjoint htm_seq ht_ind_seq
      have hd : Pairwise (Function.onFun Disjoint t_seq) := hdisjoint
      have h1 := hasSum_integral_iUnion (fun i => hmFG_le _ (htm_seq i)) hd
        (integrable_condExp : Integrable (μ[f | mG]) μ).integrableOn
      have h2 := hasSum_integral_iUnion (fun i => hmFG_le _ (htm_seq i)) hd hf_int.integrableOn
      exact h1.unique ((funext ht_ind_seq : (fun i => ∫ x in t_seq i, (μ[f | mG]) x ∂μ)
        = fun i => ∫ x in t_seq i, f x ∂μ) ▸ h2)
    · exact hs
  exact (ae_eq_condExp_of_forall_setIntegral_eq hmFG_le hf_int
    (fun _ _ _ => integrable_condExp.integrableOn) hg_eq hgm).symm

end Probability

end TauCeti
