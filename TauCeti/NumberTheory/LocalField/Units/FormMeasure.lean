/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ConvergenceFactor
public import TauCeti.NumberTheory.LocalField.Units.Haar
import TauCeti.NumberTheory.LocalField.Topology

/-!
# The form measure on the units of a local field

Let `K` be a nonarchimedean local field whose residue field has `q` elements, and `μ` an additive
Haar measure on `K`. The invariant form `dx/x` on `𝔾_m` gives the measure `|dx/x|_K = |x|_K⁻¹ μ`
on `K`. It is invariant under multiplication by every nonzero scalar
(`TauCeti.map_smul_withDensity_inv_normalizedAbsoluteValue`): multiplication by `c` scales `μ` by
`|c|_K⁻¹` and the density by `|c|_K`. Its restriction to `Kˣ` through `Units.val`,
`TauCeti.unitsFormMeasure K μ`, is therefore a σ-finite left-invariant measure on `Kˣ`, giving
the units `𝒪[K]ˣ` mass `(1 - q⁻¹) μ 𝒪[K]`. By uniqueness of Haar measure, the normalized Haar
measure `d^×x = TauCeti.unitsHaar K` with `d^×x(𝒪[K]ˣ) = 1` is `(1 - q⁻¹)⁻¹ |dx/x|_K` when
`μ 𝒪[K] = 1` (`TauCeti.unitsHaar_eq_smul_unitsFormMeasure`).

## Main declarations

* `TauCeti.map_smul_withDensity_inv_normalizedAbsoluteValue`: invariance of `|x|_K⁻¹ μ`.
* `TauCeti.unitsFormMeasure K μ`: the form measure on `Kˣ`, left-invariant and σ-finite.
* `TauCeti.unitsFormMeasure_unitFiltration_zero`: its mass on `𝒪[K]ˣ` is `(1 - q⁻¹) μ 𝒪[K]`.
* `TauCeti.unitsHaar_eq_smul_unitsFormMeasure`: `d^×x = (1 - q⁻¹)⁻¹ |dx/x|_K`.
-/

public section

open MeasureTheory Measure TauCeti ValuativeRel
open scoped NNReal ENNReal Pointwise

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsAddHaarMeasure]

omit [MeasurableSpace K] [BorelSpace K] in
/-- The density `|x|_K⁻¹` of the form measure `|dx/x|_K` scales by `|c|_K⁻¹` under `x ↦ c • x`. -/
private theorem inv_normalizedAbsoluteValue_smul {c : K} (hc : c ≠ 0) (x : K) :
    ((normalizedAbsoluteValue K (c • x) : ℝ≥0) : ℝ≥0∞)⁻¹ =
      ((normalizedAbsoluteValue K c : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹ := by
  simp only [smul_eq_mul, map_mul, NNRat.cast_mul, ENNReal.coe_mul]
  refine ENNReal.mul_inv (Or.inl ?_) (Or.inl ENNReal.coe_ne_top)
  simpa using hc

/-- **Invariance of the form measure.** The measure `|x|_K⁻¹ μ` on `K` is invariant under
multiplication by every nonzero scalar. -/
theorem map_smul_withDensity_inv_normalizedAbsoluteValue {c : K} (hc : c ≠ 0) :
    (μ.withDensity fun x ↦ ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹).map (c • ·) =
      μ.withDensity fun x ↦ ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹ := by
  set a : ℝ≥0∞ := ((normalizedAbsoluteValue K c : ℝ≥0) : ℝ≥0∞)⁻¹
  have ha0 : a ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top
  have hatop : a ≠ ⊤ := ENNReal.inv_ne_top.2 (by simpa using hc)
  have he := (MeasurableEquiv.smul₀ (α := K) c hc).measurableEmbedding
  ext t ht
  rw [map_apply (measurable_const_smul c) ht, withDensity_apply _ ht,
    withDensity_apply _ (measurable_const_smul c ht), ← ENNReal.mul_right_inj ha0 hatop]
  have h₁ : ∫⁻ x in t, ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹ ∂(μ.map (c • ·)) =
      a * ∫⁻ x in t, ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹ ∂μ := by
    rw [map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul μ hc, restrict_smul,
      lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (by simpa using hc)]
  have h₂ : ∫⁻ x in t, ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹ ∂(μ.map (c • ·)) =
      a * ∫⁻ y in (c • ·) ⁻¹' t, ((normalizedAbsoluteValue K y : ℝ≥0) : ℝ≥0∞)⁻¹ ∂μ := by
    rw [← MeasurableEquiv.coe_smul₀ hc, he.restrict_map, he.lintegral_map,
      ← lintegral_const_mul' _ _ hatop]
    exact lintegral_congr fun y ↦ inv_normalizedAbsoluteValue_smul hc y
  rw [← h₁, h₂]

variable (K) in
/-- The **form measure** `|dx/x|_K` on the units `Kˣ`: the restriction to `Kˣ`, through
`Units.val`, of the measure `|x|_K⁻¹ μ` with density `|x|_K⁻¹` against an additive Haar measure
`μ` on `K`. -/
noncomputable def unitsFormMeasure : Measure Kˣ :=
  (μ.withDensity fun x ↦ ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹).comap Units.val

omit [μ.IsAddHaarMeasure] in
/-- The form measure of a set of units is the measure `|x|_K⁻¹ μ` of its image in `K`. -/
theorem unitsFormMeasure_apply (s : Set Kˣ) :
    unitsFormMeasure K μ s =
      (μ.withDensity fun x ↦ ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹) (Units.val '' s) :=
  Units.measurableEmbedding_val₀.comap_apply _ s

instance isMulLeftInvariant_unitsFormMeasure : (unitsFormMeasure K μ).IsMulLeftInvariant := by
  refine ⟨fun u ↦ Measure.ext fun s hs ↦ ?_⟩
  have himage : Units.val '' ((u * ·) ⁻¹' s) = ((u : K) • ·) ⁻¹' (Units.val '' s) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨u * v, hv, rfl⟩
    · rintro ⟨w, hw, hwx⟩
      refine ⟨u⁻¹ * w, by simpa using hw, ?_⟩
      simp [hwx]
  rw [map_apply (measurable_const_mul u) hs, unitsFormMeasure_apply, unitsFormMeasure_apply,
    himage, ← map_apply (measurable_const_smul _)
      (Units.measurableEmbedding_val₀.measurableSet_image' hs),
    map_smul_withDensity_inv_normalizedAbsoluteValue μ u.ne_zero]

instance sigmaFinite_unitsFormMeasure : SigmaFinite (unitsFormMeasure K μ) := by
  have : SigmaFinite (μ.withDensity fun x ↦ ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹) := by
    refine SigmaFinite.withDensity_of_ne_top ?_
    have h0 : μ {0} = 0 := by
      have h := addHaar_smul_eq_normalizedAbsoluteValue_mul μ (0 : K) Set.univ
      rw [Set.zero_smul_set Set.univ_nonempty, AbsoluteValue.map_zero, NNRat.cast_zero,
        ENNReal.coe_zero, zero_mul] at h
      exact h
    refine measure_mono_null (fun x hx ↦ ?_) h0
    by_contra h0
    exact hx (ENNReal.inv_ne_top.2 (by simpa using h0))
  refine SigmaFinite.of_map _ Units.measurableEmbedding_val₀.measurable.aemeasurable ?_
  rw [unitsFormMeasure, Units.measurableEmbedding_val₀.map_comap]
  infer_instance

/-- **The form measure of the units of `𝒪[K]`** is `(1 - q⁻¹) μ 𝒪[K]`, where `q` is the
cardinality of the residue field. -/
theorem unitsFormMeasure_unitFiltration_zero :
    unitsFormMeasure K μ (unitFiltration K 0) = (1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹) * μ 𝒪[K] := by
  rw [unitsFormMeasure_apply, image_unitFiltration_zero,
    withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one]

/-- **The normalized Haar measure of `Kˣ` is the form measure with its convergence factor.**
For the additive Haar measure `μ` on `K` with `μ 𝒪[K] = 1`, the Haar measure `d^×x` of `Kˣ`
normalized by `d^×x(𝒪[K]ˣ) = 1` is `(1 - q⁻¹)⁻¹ |dx/x|_K`. -/
theorem unitsHaar_eq_smul_unitsFormMeasure (hμ : μ 𝒪[K] = 1) :
    unitsHaar K = (1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹)⁻¹ • unitsFormMeasure K μ := by
  have hq : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  have h0 : 1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹ ≠ 0 :=
    (tsub_pos_iff_lt.2 (ENNReal.inv_lt_one.2 hq)).ne'
  have htop : 1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have : SigmaFinite ((1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹)⁻¹ • unitsFormMeasure K μ) := by
    rw [← ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 h0), ← ENNReal.smul_def]
    infer_instance
  rw [unitsHaar_eq_iff, smul_apply, unitsFormMeasure_unitFiltration_zero, hμ, mul_one,
    smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

end TauCeti
