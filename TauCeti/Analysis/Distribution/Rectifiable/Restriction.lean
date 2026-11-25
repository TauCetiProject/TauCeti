/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.Rectifiable.Mass

/-!
# The mass measure and Borel restrictions of the current of an oriented set

Let `V` be a finite-dimensional real inner product space, `Ω` an open subset, `θ : V → ℝ` a
multiplicity locally integrable on `Ω` for `μHE[k]`, and `τ : V → Fin k → V` measurable orientation
frames, orthonormal wherever `θ` does not vanish, with frame current
`T = Distribution.frameCurrent θ τ`.

The **mass measure** of `T` is `|θ| μHE[k]` on `Ω` (`Distribution.massMeasure_frameCurrent`): as a
measure on `Ω`, `‖T‖ = ((μHE[k]).withDensity |θ|).comap (↑)`. This measure is locally finite since
`θ` is locally integrable, hence outer regular, and it has the value
`∫_{U ∩ Ω} |θ| dμHE[k]` on `Ω ∩ U` for every open `U`, which is the local mass of `T` on `U`
(`Distribution.localMass_frameCurrent`); the mass measure is the only outer regular measure with
these values (`Distribution.eq_massMeasure_of_preimage_coe`).

The **Borel restriction** of `T` to a Borel set `A` is the frame current of the multiplicity
`1_A θ` (`Distribution.massRestrict_frameCurrent`): `τ(A, θ, ξ) ⌞ B = τ(A ∩ B, θ, ξ)`. Both
`T ⌞ A` and the current `R` of `1_A θ` have mass measure `‖T‖ ⌞ A`, and both `T ⌞ Aᶜ` and the
current `R'` of `1_{Aᶜ} θ` have mass measure `‖T‖ ⌞ Aᶜ`. Since `T ⌞ A + T ⌞ Aᶜ = T = R + R'`, the
difference `T ⌞ A - R = R' - T ⌞ Aᶜ` has mass measure dominated both by `2 ‖T‖ ⌞ A` and by
`2 ‖T‖ ⌞ Aᶜ`, hence zero.

## Main declarations

* `Distribution.massMeasure_frameCurrent`: `‖T‖ = |θ| μHE[k]` on `Ω`, and
  `Distribution.massMeasure_frameCurrent_indicator`: the current of `1_A θ` has mass measure
  `‖T‖ ⌞ A`.
* `Distribution.massRestrict_eq_of_massMeasure_eq`: for any current of locally finite mass,
  `T = R + R'` with `‖R‖ = ‖T‖ ⌞ A` and `‖R'‖ = ‖T‖ ⌞ Aᶜ` forces `T ⌞ A = R`.
* `Distribution.massRestrict_frameCurrent`: the Borel restriction of `T` to `A` is the frame
  current of `1_A θ`.

## References

* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §3 (integer multiplicity
  rectifiable currents `τ(M, θ, ξ)` and their mass).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory exteriorPower
open scoped Distributions ENNReal RealInnerProductSpace Topology

namespace Distribution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Opens V} {n : ℕ∞} {k : ℕ} {θ : V → ℝ}
  {τ : V → Fin k → V}

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {U : Opens E}

/-- **Recognizing a Borel restriction.** If `T = R + R'` for maps `R`, `R'` of locally finite mass
whose mass measures are `‖T‖ ⌞ A` and `‖T‖ ⌞ Aᶜ`, then `T ⌞ A = R`: the difference
`T ⌞ A - R = R' - T ⌞ Aᶜ` has mass measure dominated by `2 ‖T‖ ⌞ A` and by `2 ‖T‖ ⌞ Aᶜ`. -/
theorem massRestrict_eq_of_massMeasure_eq {T R R' : 𝓓^{n}(U, F) →L[ℝ] ℝ}
    (hT : HasLocallyFiniteMass T) (hR : HasLocallyFiniteMass R) (hR' : HasLocallyFiniteMass R')
    (hsum : T = R + R') {A : Set U} (hA : MeasurableSet A)
    (hRm : massMeasure R = (massMeasure T).restrict A)
    (hR'm : massMeasure R' = (massMeasure T).restrict Aᶜ) :
    massRestrict T hA = R := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · ext φ
    simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  -- A locally finite measure dominating `‖S₁‖` and `‖S₂‖` twice dominates `‖S₁ - S₂‖`.
  have hle (S₁ S₂ : 𝓓^{n}(U, F) →L[ℝ] ℝ) (h₁ : HasLocallyFiniteMass S₁)
      (h₂ : HasLocallyFiniteMass S₂) (μ : Measure U) [IsLocallyFiniteMeasure μ]
      (hμ₁ : massMeasure S₁ = μ) (hμ₂ : massMeasure S₂ = μ) :
      massMeasure (S₁ - S₂) ≤ μ + μ := by
    have : IsLocallyFiniteMeasure (μ + μ) := by rw [← two_smul NNReal μ]; infer_instance
    refine massMeasure_le_of_enorm_apply_le _ fun φ ↦ ?_
    rw [lintegral_add_measure, sub_apply]
    exact (eNorm_sub_le).trans (add_le_add (hμ₁ ▸ enorm_apply_le_lintegral_massMeasure h₁ φ)
      (hμ₂ ▸ enorm_apply_le_lintegral_massMeasure h₂ φ))
  have hD : massRestrict T hA - R = R' - massRestrict T hA.compl := by
    ext φ
    have h := massRestrict_add_massRestrict_compl_apply hT hA φ
    have h' : T φ = R φ + R' φ := by rw [hsum]; rfl
    simp only [sub_apply]
    linarith
  have h₁ := hle _ _ (hasLocallyFiniteMass_massRestrict hA) hR _ (massMeasure_massRestrict hT hA)
    hRm
  have h₂ := hle _ _ hR' (hasLocallyFiniteMass_massRestrict hA.compl) _ hR'm
    (massMeasure_massRestrict hT hA.compl)
  rw [← hD] at h₂
  have h0 : massMeasure (massRestrict T hA - R) = 0 := by
    refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ bot_le)
    calc massMeasure (massRestrict T hA - R) univ
        ≤ massMeasure (massRestrict T hA - R) A + massMeasure (massRestrict T hA - R) Aᶜ := by
          rw [← measure_union disjoint_compl_right hA.compl, union_compl_self]
      _ ≤ 0 + 0 := add_le_add ((h₂ _).trans (by simp [Measure.restrict_apply hA]))
          ((h₁ _).trans (by simp [Measure.restrict_apply hA.compl]))
      _ = 0 := add_zero 0
  ext φ
  have h := enorm_apply_le_lintegral_massMeasure (T := massRestrict T hA - R)
    (by rw [FunLike.coe_sub]; exact (hasLocallyFiniteMass_massRestrict hA).sub hR) φ
  rw [h0, lintegral_zero_measure, nonpos_iff_eq_zero, eNorm_eq_zero,
    sub_apply, sub_eq_zero] at h
  exact h

end General

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The measure `|θ| μHE[k]` on `Ω` takes the value `∫_{Ω ∩ U} |θ| dμHE[k]` on `Ω ∩ U` for a
measurable set `U`. -/
private theorem comap_withDensity_preimage_coe {U : Set V} (hU : MeasurableSet U) :
    (μHE[k].withDensity fun x ↦ ‖θ x‖ₑ).comap ((↑) : Ω → V) ((↑) ⁻¹' U) =
      ∫⁻ x in Ω ∩ U, ‖θ x‖ₑ ∂μHE[k] := by
  have hemb : MeasurableEmbedding ((↑) : Ω → V) :=
    MeasurableEmbedding.subtypeVal Ω.isOpen.measurableSet
  rw [hemb.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe_subtype,
    SetLike.setOfPred_mem_eq, inter_comm, withDensity_apply _ (Ω.isOpen.measurableSet.inter hU)]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- For `θ` locally integrable on `Ω`, the measure `|θ| μHE[k]` on `Ω` is locally finite. -/
private theorem isLocallyFiniteMeasure_comap_withDensity (hθ : LocallyIntegrableOn θ Ω μHE[k]) :
    IsLocallyFiniteMeasure ((μHE[k].withDensity fun x ↦ ‖θ x‖ₑ).comap ((↑) : Ω → V)) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨t, ht, hint⟩ := hθ x x.property
  obtain ⟨u, hu, hxu, hut⟩ := mem_nhdsWithin.1 ht
  refine ⟨(↑) ⁻¹' u, (hu.preimage continuous_subtypeVal).mem_nhds hxu, ?_⟩
  rw [comap_withDensity_preimage_coe hu.measurableSet]
  exact (lintegral_mono_set (s := (Ω : Set V) ∩ u) fun y hy ↦ hut ⟨hy.2, hy.1⟩).trans_lt hint.2

/-- **The mass measure of a frame current** is `|θ| μHE[k]` on `Ω`, for a multiplicity `θ`
locally integrable on `Ω` and measurable frames `τ`, orthonormal where `θ` does not vanish. -/
theorem massMeasure_frameCurrent (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) :
    massMeasure (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      (μHE[k].withDensity fun x ↦ ‖θ x‖ₑ).comap ((↑) : Ω → V) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have := isLocallyFiniteMeasure_comap_withDensity hθ
  refine (eq_massMeasure_of_preimage_coe (hasLocallyFiniteMass_frameCurrent hθ hτo) _
    fun U hU ↦ ?_).symm
  rw [comap_withDensity_preimage_coe hU.measurableSet, localMass_frameCurrent hθ hτ hτo hU,
    inter_comm]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Cutting the multiplicity off by a measurable set keeps it locally integrable. -/
private theorem locallyIntegrableOn_indicator (hθ : LocallyIntegrableOn θ Ω μHE[k]) {A : Set V}
    (hA : MeasurableSet A) : LocallyIntegrableOn (A.indicator θ) Ω μHE[k] := fun x hx ↦ by
  obtain ⟨t, ht, hint⟩ := hθ x hx
  exact ⟨t, ht, hint.indicator hA⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem orthonormal_of_indicator_ne_zero (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x))
    (A : Set V) (x : V) (hx : A.indicator θ x ≠ 0) : Orthonormal ℝ (τ x) := by
  by_cases hxA : x ∈ A
  · exact hτo x (by simpa [hxA] using hx)
  · simp [hxA] at hx

/-- The mass measure of the frame current of `1_A θ` is the mass measure of the frame current of
`θ` restricted to `A`. -/
theorem massMeasure_frameCurrent_indicator (hθ : LocallyIntegrableOn θ Ω μHE[k])
    (hτ : Measurable τ) (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) {A : Set V}
    (hA : MeasurableSet A) :
    massMeasure (frameCurrent (A.indicator θ) τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      (massMeasure (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)).restrict
        ((↑) ⁻¹' A) := by
  rw [massMeasure_frameCurrent (locallyIntegrableOn_indicator hθ hA) hτ
      (orthonormal_of_indicator_ne_zero hτo A),
    massMeasure_frameCurrent hθ hτ hτo]
  refine Measure.ext fun s hs ↦ ?_
  have hemb : MeasurableEmbedding ((↑) : Ω → V) :=
    MeasurableEmbedding.subtypeVal Ω.isOpen.measurableSet
  rw [Measure.restrict_apply hs, hemb.comap_apply, hemb.comap_apply,
    withDensity_apply _ (hemb.measurableSet_image' hs),
    withDensity_apply _
      (hemb.measurableSet_image' (hs.inter (hA.preimage measurable_subtypeVal))),
    image_inter_preimage]
  simp_rw [eNorm_indicator_eq_indicator_eNorm]
  rw [lintegral_indicator hA, Measure.restrict_restrict hA, inter_comm]


/-- **Borel restriction of a frame current.** For a multiplicity `θ` locally integrable on `Ω`,
measurable frames `τ`, orthonormal where `θ` does not vanish, and a measurable set `A`, the
restriction `T ⌞ A` of the frame current `T` of `(θ, τ)` is the frame current of `(1_A θ, τ)`. -/
theorem massRestrict_frameCurrent (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) {A : Set V} (hA : MeasurableSet A) :
    massRestrict (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
        (hA.preimage measurable_subtypeVal) =
      frameCurrent (A.indicator θ) τ :=
  massRestrict_eq_of_massMeasure_eq (hasLocallyFiniteMass_frameCurrent hθ hτo)
    (hasLocallyFiniteMass_frameCurrent (locallyIntegrableOn_indicator hθ hA)
      (orthonormal_of_indicator_ne_zero hτo A))
    (hasLocallyFiniteMass_frameCurrent (locallyIntegrableOn_indicator hθ hA.compl)
      (orthonormal_of_indicator_ne_zero hτo Aᶜ))
    (frameCurrent_eq_add_of_ae hθ hτ hτo (locallyIntegrableOn_indicator hθ hA) hτ
      (orthonormal_of_indicator_ne_zero hτo A) (locallyIntegrableOn_indicator hθ hA.compl) hτ
      (orthonormal_of_indicator_ne_zero hτo Aᶜ) (ae_of_all _ fun x _ ω ↦ by
        by_cases hx : x ∈ A <;> simp [hx]))
    _ (massMeasure_frameCurrent_indicator hθ hτ hτo hA)
    (massMeasure_frameCurrent_indicator hθ hτ hτo hA.compl)

end Distribution
