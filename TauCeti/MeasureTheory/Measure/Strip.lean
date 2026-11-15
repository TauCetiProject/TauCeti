/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ArctanCenter
public import TauCeti.MeasureTheory.Measure.FiniteMeasure.WithDensity

/-!
# Densities on the strip and their arctan centers

A real function `f` on the strip `ℝ × [0, 1]` defines a measure on the `s`-axis, its *strip
measure* `TauCeti.stripMeasure f`: the measure of a set `A` of `s`-values is the integral of the
positive part of `f` over `A × [0, 1]`. It is the pushforward along `(s, t) ↦ s` of the measure with
density `f⁺` on the strip. For the energy density of a Floer cylinder this measure records how the
energy is distributed along the cylinder, for a vector-space target as for a manifold target.

Translating `f` along the strip translates its strip measure in the opposite direction
(`TauCeti.stripMeasure_comp_add_right`). When the strip measure is finite and nonzero it has an
arctan center (`MeasureTheory.Measure.arctanCenter`), which is therefore translation equivariant
(`TauCeti.arctanCenter_stripMeasure_comp_add_right`): exactly one translate of `f` has center
zero (`TauCeti.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero`). This is what
makes the energy center a slice for the translation action on Floer cylinders.

The center is continuous along densities which converge almost everywhere without loss of mass
(`TauCeti.tendsto_arctanCenter_stripMeasure`): by Scheffé's lemma the measures with these
densities then converge weakly
(`MeasureTheory.FiniteMeasure.tendsto_of_ae_tendsto_of_tendsto_integral`), and so do their strip
measures, whose arctan centers then converge (`MeasureTheory.FiniteMeasure.tendsto_arctanCenter`).

## References

* H. Scheffé, *A useful convergence theorem for probability distributions*, Ann. Math. Statist.
  **18** (1947), 434–438.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti

/-- The *strip measure* of a function `f` on the strip `ℝ × [0, 1]`: the measure on `ℝ` giving
each set `A` of `s`-values the integral of the positive part of `f` over `A × [0, 1]`
(`TauCeti.stripMeasure_apply`). It is the pushforward to the `s`-axis of the measure with density
the positive part of `f` on the strip. -/
def stripMeasure (f : ℝ × ℝ → ℝ) : Measure ℝ :=
  ((volume.restrict ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1)).withDensity fun z ↦
    ENNReal.ofReal (f z)).map Prod.fst

variable {f : ℝ × ℝ → ℝ}

variable (f) in
/-- The strip measure is the pushforward to the `s`-axis of the measure with density the positive
part of `f` on the strip. -/
theorem stripMeasure_def :
    stripMeasure f =
      ((volume.restrict ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1)).withDensity fun z ↦
        ENNReal.ofReal (f z)).map Prod.fst :=
  (rfl)

variable (f) in
/-- The strip measure of a measurable set `A` is the integral of the positive part of `f` over
`A × [0, 1]`. -/
@[simp]
theorem stripMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) :
    stripMeasure f A = ∫⁻ z in A ×ˢ Icc 0 1, ENNReal.ofReal (f z) := by
  rw [stripMeasure, Measure.map_apply measurable_fst hA,
    withDensity_apply _ (measurable_fst hA), Measure.restrict_restrict (measurable_fst hA),
    ← prod_univ, prod_inter_prod, inter_univ, univ_inter]

variable (f) in
/-- The total mass of the strip measure is the integral of the positive part of `f` over the
strip. -/
theorem stripMeasure_univ :
    stripMeasure f univ = ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (f z) :=
  stripMeasure_apply f MeasurableSet.univ

/-- The strip measure of a function whose positive part has finite integral over the strip is
finite. -/
theorem isFiniteMeasure_stripMeasure
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (f z) ≠ ⊤) :
    IsFiniteMeasure (stripMeasure f) :=
  ⟨by rw [stripMeasure_univ]; exact hfin.lt_top⟩

/-- The strip measure vanishes exactly when the integral of the positive part of `f` over the
strip does. -/
theorem stripMeasure_eq_zero_iff :
    stripMeasure f = 0 ↔ ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (f z) = 0 := by
  rw [← Measure.measure_univ_eq_zero, stripMeasure_univ]

variable (f) in
/-- **Translations translate the strip measure.** The strip measure of the translate
`w ↦ f (w + (c, 0))` is the strip measure of `f` translated by `-c`. -/
theorem stripMeasure_comp_add_right (c : ℝ) :
    stripMeasure (fun w ↦ f (w + (c, 0))) = (stripMeasure f).map (· - c) := by
  ext A hA
  have hpre : A ×ˢ Icc (0 : ℝ) 1 = (· + (c, 0)) ⁻¹' (((· - c) ⁻¹' A) ×ˢ Icc 0 1) := by
    ext z
    simp
  have hv : MeasurePreserving (· + ((c, 0) : ℝ × ℝ)) volume volume :=
    (measurePreserving_add_right volume c).prod (measurePreserving_add_right volume 0)
  rw [Measure.map_apply (measurable_sub_const c) hA, stripMeasure_apply _ hA,
    stripMeasure_apply _ (measurable_sub_const c hA), hpre]
  exact hv.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight _)
    (fun z ↦ ENNReal.ofReal (f z)) _

/-- **Translation equivariance of the arctan center.** If the positive part of `f` has finite
nonzero integral over the strip, the arctan center of the strip measure of the translate
`w ↦ f (w + (c, 0))` is that of `f` minus `c`. -/
theorem arctanCenter_stripMeasure_comp_add_right
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (f z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (f z) ≠ 0) (c : ℝ) :
    (stripMeasure fun w ↦ f (w + (c, 0))).arctanCenter = (stripMeasure f).arctanCenter - c := by
  have := isFiniteMeasure_stripMeasure hfin
  have : NeZero (stripMeasure f) := ⟨fun h ↦ hE (stripMeasure_eq_zero_iff.1 h)⟩
  simp_rw [stripMeasure_comp_add_right, sub_eq_add_neg, Measure.arctanCenter_map_add]

/-- **Each translation orbit meets the slice once.** If the positive part of `f` has finite
nonzero integral over the strip, there is exactly one translation `w ↦ w + (c, 0)` after which the
arctan center of the strip measure is `0`; it is translation by the center of `f`. -/
theorem existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (f z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (f z) ≠ 0) :
    ∃! c : ℝ, (stripMeasure fun w ↦ f (w + (c, 0))).arctanCenter = 0 := by
  simp_rw [arctanCenter_stripMeasure_comp_add_right hfin hE, sub_eq_zero]
  exact ⟨_, rfl, fun _ h ↦ h.symm⟩

/-- **Continuity of the arctan center.** Let `f i` be integrable functions on the strip
`ℝ × [0, 1]`, nonnegative almost everywhere, converging almost everywhere on the strip to an
integrable function `f₀`. If moreover no mass is lost in the limit, that is, the integrals of
`f i` over the strip converge to that of `f₀`, and the integral of `f₀` is nonzero, then the arctan
centers of the strip measures of `f i` converge to that of `f₀`. -/
theorem tendsto_arctanCenter_stripMeasure {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → ℝ × ℝ → ℝ} {f₀ : ℝ × ℝ → ℝ}
    (hint : ∀ i, IntegrableOn (f i) ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hint₀ : IntegrableOn f₀ ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hnonneg : ∀ i, 0 ≤ᵐ[volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1)] f i)
    (hlim : ∀ᵐ z ∂volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1),
      Tendsto (fun i ↦ f i z) l (𝓝 (f₀ z)))
    (hmass : Tendsto (fun i ↦ ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, f i z) l
      (𝓝 (∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, f₀ z)))
    (hE : ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, f₀ z ≠ 0) :
    Tendsto (fun i ↦ (stripMeasure (f i)).arctanCenter) l
      (𝓝 (stripMeasure f₀).arctanCenter) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  set S := (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1
  -- The measures with these densities on the strip, as finite measures.
  let μ (g : ℝ × ℝ → ℝ) (hg : IntegrableOn g S) : FiniteMeasure (ℝ × ℝ) :=
    ⟨(volume.restrict S).withDensity fun z ↦ ENNReal.ofReal (g z),
      isFiniteMeasure_withDensity_ofReal hg.hasFiniteIntegral⟩
  -- Their pushforwards to the `s`-axis are the strip measures.
  have hμ (g : ℝ × ℝ → ℝ) (hg : IntegrableOn g S) :
      ((μ g hg).map Prod.fst).toMeasure = stripMeasure g := by
    rw [FiniteMeasure.toMeasure_map, stripMeasure_def]
    simp only [μ, S, FiniteMeasure.toMeasure_mk]
  -- By Scheffé's lemma the finite measures converge weakly, and so do their pushforwards.
  have h := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (FiniteMeasure.tendsto_of_ae_tendsto_of_tendsto_integral (μs := fun i ↦ μ (f i) (hint i))
      (ν := μ f₀ hint₀) hint hint₀ hnonneg (fun _ ↦ rfl) rfl hlim hmass) continuous_fst
  -- The limit is nonzero: otherwise `f₀` would be nonpositive almost everywhere on the strip,
  -- while its integral is a limit of nonnegative integrals.
  have hne : (μ f₀ hint₀).map Prod.fst ≠ 0 := by
    intro h0
    have h0' : stripMeasure f₀ = 0 := by
      rw [← hμ f₀ hint₀, h0, FiniteMeasure.toMeasure_zero]
    have hle : f₀ ≤ᵐ[volume.restrict S] 0 := by
      filter_upwards [(lintegral_eq_zero_iff' hint₀.aemeasurable.ennreal_ofReal).1
        (stripMeasure_eq_zero_iff.1 h0')] with z hz
      exact ENNReal.ofReal_eq_zero.1 hz
    exact hE (le_antisymm (integral_nonpos_of_ae hle)
      (ge_of_tendsto' hmass fun i ↦ integral_nonneg_of_ae (hnonneg i)))
  simpa only [hμ] using FiniteMeasure.tendsto_arctanCenter hne h

end TauCeti
