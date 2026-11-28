/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.TestFunction.Pullback

/-!
# Borel restriction and proper smooth pushforward

For a current `T` of locally finite mass on `Ω ⊆ E` and a smooth map `Φ : E → E'` proper over
`Ω' ⊆ E'`, the Borel restriction `Distribution.massRestrict` commutes with the pushforward
`Φ_# T = T ∘L TestFunction.pullbackCLM Φ hΦ hΦp`:

`(Φ_# T) ⌞ B = Φ_# (T ⌞ Φ⁻¹(B))`

for every Borel set `B ⊆ Ω'`.

## Main declarations

* `Distribution.massRestrict_comp_pullbackCLM`: Borel restriction commutes with proper smooth
  pushforward.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the restriction `T ⌞ A` and pushforward).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped BoundedContinuousFunction ENNReal Distributions Topology

namespace Distribution

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {Ω' : Opens E'} {k : ℕ}

omit [BorelSpace E] [MeasurableSpace E'] [BorelSpace E'] in
private theorem lintegral_pullbackCLM_smulLeftCLM_sub_indicator
    {Φ : E → E'} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    (μ : Measure Ω) {χ : 𝓓(Ω', ℝ)} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (φ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) (A : Set Ω) :
    ∫⁻ x : Ω, ‖TestFunction.pullbackCLM Φ hΦ hΦp (TestFunction.smulLeftCLM hχ φ) x -
        A.indicator (fun z : Ω => TestFunction.pullbackCLM Φ hΦ hΦp φ z) x‖ₑ ∂μ =
      ∫⁻ x in (↑) ⁻¹' ((Ω : Set E) ∩ Φ ⁻¹' tsupport φ),
        ‖TestFunction.pullbackCLM Φ hΦ hΦp (TestFunction.smulLeftCLM hχ φ) x -
          A.indicator (fun z : Ω => TestFunction.pullbackCLM Φ hΦ hΦp φ z) x‖ₑ ∂μ := by
  refine (setLIntegral_eq_of_support_subset fun x hx => ?_).symm
  by_contra hxC
  have hx' : (x : E) ∉ (Ω : Set E) ∩ Φ ⁻¹' tsupport φ := fun h => hxC h
  have hP1 : TestFunction.pullbackCLM Φ hΦ hΦp (TestFunction.smulLeftCLM hχ φ) x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h =>
      hx' ((TestFunction.tsupport_pullbackCLM_subset _ h).imp_right fun hmem =>
        TestFunction.tsupport_smulLeftCLM_subset_right hχ φ hmem)
  have hP2 : TestFunction.pullbackCLM Φ hΦ hΦp φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h =>
      hx' (TestFunction.tsupport_pullbackCLM_subset φ h)
  by_cases hxA : x ∈ A
  · exact hx (by dsimp only; rw [indicator_of_mem hxA, hP1, hP2, sub_self]; simp [← ofReal_norm])
  · exact hx (by dsimp only; rw [indicator_of_notMem hxA, hP1, sub_zero]; simp [← ofReal_norm])

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E'] in
private theorem enorm_pullbackCLM_smulLeftCLM_sub_indicator_le
    {Φ : E → E'} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    {χ : 𝓓(Ω', ℝ)} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (φ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F))
    {A : Set Ω} {B : Set Ω'} {x : Ω} {y : Ω'} (hy : (y : E') = Φ x)
    (hxC : Φ x ∈ tsupport φ) (hxAB : x ∈ A ↔ y ∈ B) :
    ‖TestFunction.pullbackCLM Φ hΦ hΦp (TestFunction.smulLeftCLM hχ φ) x -
        A.indicator (fun z : Ω => TestFunction.pullbackCLM Φ hΦ hΦp φ z) x‖ₑ ≤
      ‖χ y - (B ∩ (↑) ⁻¹' tsupport φ).indicator (1 : Ω' → ℝ) y‖ₑ *
        ‖(TestFunction.pullbackCLM Φ hΦ hΦp φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ := by
  have hyK : y ∈ ((↑) ⁻¹' tsupport φ : Set Ω') := by simpa [mem_preimage, hy] using hxC
  have hP1 : TestFunction.pullbackCLM Φ hΦ hΦp (TestFunction.smulLeftCLM hχ φ) x =
      χ y • TestFunction.pullbackCLM Φ hΦ hΦp φ x := by
    rw [TestFunction.pullbackCLM_apply_of_mem _ x.property,
      TestFunction.pullbackCLM_apply_of_mem _ x.property, ← hy]
    ext v; simp
  have hsub : TestFunction.pullbackCLM Φ hΦ hΦp (TestFunction.smulLeftCLM hχ φ) x -
      A.indicator (fun z : Ω => TestFunction.pullbackCLM Φ hΦ hΦp φ z) x =
      (χ y - (B ∩ (↑) ⁻¹' tsupport φ).indicator (1 : Ω' → ℝ) y) •
        TestFunction.pullbackCLM Φ hΦ hΦp φ x := by
    rw [hP1]
    by_cases hyB : y ∈ B
    · simp [hxAB.2 hyB, hyB, hyK, sub_smul]
    · simp [mt hxAB.1 hyB, hyB]
  rw [hsub, eNorm_smul]
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (BoundedContinuousFunction.norm_coe_le_norm
    (TestFunction.pullbackCLM Φ hΦ hΦp φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F) x)

/-- **Borel restriction commutes with proper smooth pushforward.** For `T` of locally finite mass
on `Ω`, a smooth map `Φ` on `Ω` proper over `Ω'`, and a measurable set `B ⊆ Ω'`,
`(Φ_# T) ⌞ B = Φ_# (T ⌞ Φ⁻¹(B))`. -/
theorem massRestrict_comp_pullbackCLM [FiniteDimensional ℝ E'] [CompleteSpace F]
    {Φ : E → E'} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ} (hT : HasLocallyFiniteMass T)
    {B : Set Ω'} (hB : MeasurableSet B) :
    massRestrict (T ∘L TestFunction.pullbackCLM Φ hΦ hΦp) hB =
      massRestrict T
        ((Ω'.isOpen.measurableSet.subtype_image hB).preimage
          hΦ.continuousOn.domRestrict.measurable) ∘L
        TestFunction.pullbackCLM Φ hΦ hΦp := by
  set P : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
    TestFunction.pullbackCLM Φ hΦ hΦp
  by_cases hE : FiniteDimensional ℝ E
  swap
  · have hP : P = 0 := by ext1 φ; exact TestFunction.eq_zero_of_not_finiteDimensional (P φ) hE
    simp [hP]
  have hΦc : Continuous fun x : Ω => Φ x := hΦ.continuousOn.domRestrict
  set A : Set Ω := (Ω : Set E).domRestrict Φ ⁻¹' ((↑) '' B : Set E')
  have hA : MeasurableSet A :=
    (Ω'.isOpen.measurableSet.subtype_image hB).preimage hΦ.continuousOn.domRestrict.measurable
  rw [massRestrict_congr_set (T := T) _ hA rfl]
  ext φ
  cases isEmpty_or_nonempty Ω' with
  | inl hE =>
    have hφ0 : φ = 0 := DFunLike.ext _ _ fun z =>
      image_eq_zero_of_notMem_tsupport fun h => hE.false ⟨z, φ.tsupport_subset h⟩
    simp [hφ0]
  | inr hne =>
  classical
  let g : Ω → Ω' := fun x => if hx : Φ x ∈ Ω' then ⟨Φ x, hx⟩ else hne.some
  have hg : Measurable g := Measurable.dite (s := {x : Ω | Φ x ∈ (Ω' : Set E')})
    ((hΦc.comp continuous_subtypeVal).subtype_mk fun p => p.property).measurable
    measurable_const (Ω'.isOpen.preimage hΦc).measurableSet
  let CΩ : Set Ω := (↑) ⁻¹' ((Ω : Set E) ∩ Φ ⁻¹' tsupport φ)
  have hCΩ : IsCompact CΩ :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage'
      (hΦp _ φ.hasCompactSupport φ.tsupport_subset)
      (by rw [Subtype.range_coe]; exact inter_subset_left)
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have : IsFiniteMeasure ((massMeasure T).restrict CΩ) := ⟨by simp [hCΩ.measure_lt_top]⟩
  let ν : Measure Ω' := ((massMeasure T).restrict CΩ).map g
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ g
  let μ' : Measure Ω' := massMeasure (T ∘L P) + ν
  have : IsFiniteMeasureOnCompacts μ' :=
    ⟨fun _ hK => ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, measure_lt_top ν _⟩⟩
  let K' : Set Ω' := (↑) ⁻¹' tsupport φ
  have hK' : IsCompact K' := TestFunction.isCompact_preimage_tsupport φ
  -- Approximate `1_{B ∩ supp φ}` in `L¹(μ')` (`μ' = ‖T ∘L P‖ + g_*(‖T‖ ⌞ CΩ)`) by smooth
  -- scalar test functions `χ m`, then compare the limits of `(T ∘L P)(χ m • φ)` via `extendL1 T`.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_tendsto_lintegral_indicator μ' hB hK'
  have hχc (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (χ m) :=
    (χ m).contDiff.of_le (WithTop.coe_le_coe.2 le_top)
  refine tendsto_nhds_unique (tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hB φ hχ
    hT.comp_pullbackCLM (fun s => by simp [μ', P])) ?_
  rw [ContinuousLinearMap.comp_apply]
  refine (tendsto_congr fun m => ContinuousLinearMap.comp_apply T P _).2
    (tendsto_apply_of_lintegral_eNorm_sub_le hT hA _ (P φ) hχ
      (C := ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ) eNorm_ne_top fun m => ?_)
  -- Bound the `L¹(‖T‖)` error on `Ω` by the `L¹(ν)` error on `Ω'` via `CΩ = Ω ∩ Φ⁻¹(supp φ)`.
  rw [← lintegral_mul_const' _ _ eNorm_ne_top,
    lintegral_pullbackCLM_smulLeftCLM_sub_indicator (massMeasure T) (hχc m) φ A]
  have hpoint : ∀ x ∈ CΩ,
      ‖P (TestFunction.smulLeftCLM (hχc m) φ) x - A.indicator (fun z : Ω => P φ z) x‖ₑ ≤
        ‖χ m (g x) - (B ∩ K').indicator (1 : Ω' → ℝ) (g x)‖ₑ *
          ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ := fun x hxC => by
    have hxΩ' : Φ x ∈ Ω' := φ.tsupport_subset hxC.2
    have hgx : (g x : E') = Φ x := by simp [g, hxΩ']
    have hxAB : x ∈ A ↔ g x ∈ B := by
      simp only [A, mem_preimage, Set.domRestrict_apply, ← hgx,
        Subtype.val_injective.mem_set_image]
    exact enorm_pullbackCLM_smulLeftCLM_sub_indicator_le (hχc m) φ hgx hxC.2 hxAB
  have hf_meas : AEMeasurable (fun y : Ω' =>
      ‖χ m y - (B ∩ K').indicator (1 : Ω' → ℝ) y‖ₑ *
        ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ) ν :=
    (((χ m).continuous.comp continuous_subtypeVal).aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator
        (hB.inter hK'.isClosed.measurableSet))).eNorm.mul_const _
  exact ((setLIntegral_mono' hCΩ.isClosed.measurableSet hpoint).trans_eq
    (lintegral_map' hf_meas hg.aemeasurable).symm).trans
    (lintegral_mono' (fun s => by simp [μ', ν]) le_rfl)

end Distribution
