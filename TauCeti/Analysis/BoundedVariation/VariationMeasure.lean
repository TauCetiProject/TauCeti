/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
public import Mathlib.MeasureTheory.Measure.Content

/-!
# The variation measure of a function of locally finite variation

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and let `u : E → ℝ`
be locally integrable on `Ω`. The variational total variation `|Du|(U)` of `u` on open sets
`U ⊆ Ω` (`TauCeti.totalVariationOn`) is the restriction to open sets of a regular Borel measure
on `Ω`, the **variation measure** `|Du|` (`TauCeti.variationMeasure`), provided `u` has locally
finite variation on `Ω`: every compact `K ⊆ Ω` has an open neighbourhood `U` with
`|Du|(U) < ∞`. No global finiteness of the variation is needed, so this covers functions of
locally bounded variation on unbounded open sets, and perimeter measures of sets of locally
finite perimeter.

The construction is the De Giorgi–Letta criterion in the form of Mathlib's contents. As a
function of the open set, the total variation is countably subadditive
(`TauCeti.totalVariationOn_iSup_le_tsum`) and additive on disjoint open sets
(`TauCeti.totalVariationOn_sup_of_disjoint`). The set function
`K ↦ inf { |Du|(U) | K ⊆ U ⊆ Ω open }` on the compact subsets of `Ω` is therefore a content
(`MeasureTheory.Content`), whose measure agrees with `|Du|` on open sets because a test vector
field is admissible on every open neighbourhood of its compact support. Uniqueness among outer
regular measures follows from `MeasureTheory.Measure.OuterRegular.ext_isOpen`.

## Main declarations

* `TauCeti.variationMeasure μ Ω u`: the variation measure `|Du|` on `Ω`, a regular measure.
* `TauCeti.variationMeasure_preimage_coe`: `|Du|(U) = totalVariationOn μ U u` for every open
  `U ⊆ Ω`, and `TauCeti.variationMeasure_univ`: `|Du|(Ω) = totalVariationOn μ Ω u`.
* `TauCeti.eq_variationMeasure`: an outer regular measure with these values on open sets is
  the variation measure.
* `TauCeti.variationMeasure_congr_ae`: the variation measure only depends on `u` almost
  everywhere on `Ω`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.1 (the structure theorem for functions of locally bounded variation).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §1.5 (the De Giorgi–Letta criterion) and §3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω U V : Opens E} {u v : E → ℝ}

/-! ### The variation content -/

section Content

variable [OpensMeasurableSpace E]

/-- The outer approximation of the variation measure on a set `K` of `Ω`: the infimum of the
total variation over the open sets `V ⊆ Ω` containing `K`. -/
private def variationOuter (μ : Measure E) (Ω : Opens E) (u : E → ℝ) (K : Set Ω) : ℝ≥0∞ :=
  ⨅ V : {V : Opens E // (↑) '' K ⊆ (V : Set E) ∧ V ≤ Ω}, totalVariationOn μ V u

omit [OpensMeasurableSpace E] in
private theorem variationOuter_le {K : Set Ω} (hKV : (↑) '' K ⊆ (V : Set E)) (hV : V ≤ Ω) :
    variationOuter μ Ω u K ≤ totalVariationOn μ V u :=
  iInf_le_of_le ⟨V, hKV, hV⟩ le_rfl

omit [OpensMeasurableSpace E] in
private theorem le_variationOuter {K : Set Ω} {c : ℝ≥0∞}
    (h : ∀ V : Opens E, (↑) '' K ⊆ (V : Set E) → V ≤ Ω → c ≤ totalVariationOn μ V u) :
    c ≤ variationOuter μ Ω u K :=
  le_iInf fun V => h V V.2.1 V.2.2

omit [OpensMeasurableSpace E] in
private theorem variationOuter_mono {K₁ K₂ : Set Ω} (h : K₁ ⊆ K₂) :
    variationOuter μ Ω u K₁ ≤ variationOuter μ Ω u K₂ :=
  le_variationOuter fun _ hV hVΩ => variationOuter_le ((image_mono h).trans hV) hVΩ

omit [OpensMeasurableSpace E] in
private theorem variationOuter_ne_top
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    {K : Set Ω} (hK : IsCompact K) : variationOuter μ Ω u K ≠ ∞ := by
  obtain ⟨U, hKU, hU⟩ := hfin _ (hK.image continuous_subtype_val) (Subtype.coe_image_subset _ _)
  refine ne_top_of_le_ne_top hU ((variationOuter_le (V := U ⊓ Ω) ?_ inf_le_right).trans
    (totalVariationOn_mono inf_le_left))
  rw [Opens.coe_inf]
  exact subset_inter hKU (Subtype.coe_image_subset _ _)

private theorem variationOuter_union_le (hu : LocallyIntegrableOn u Ω μ) (K₁ K₂ : Set Ω) :
    variationOuter μ Ω u (K₁ ∪ K₂) ≤ variationOuter μ Ω u K₁ + variationOuter μ Ω u K₂ :=
  ENNReal.le_iInf_add_iInf fun ⟨V₁, hKV₁, hV₁⟩ ⟨V₂, hKV₂, hV₂⟩ => by
    refine (variationOuter_le (V := V₁ ⊔ V₂) ?_ (sup_le hV₁ hV₂)).trans
      (totalVariationOn_sup_le (hu.mono_set (sup_le hV₁ hV₂)))
    simpa [image_union] using union_subset_union hKV₁ hKV₂

private theorem variationOuter_add_le_union (hu : LocallyIntegrableOn u Ω μ) {K₁ K₂ : Set Ω}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (h : Disjoint K₁ K₂) :
    variationOuter μ Ω u K₁ + variationOuter μ Ω u K₂ ≤ variationOuter μ Ω u (K₁ ∪ K₂) := by
  -- Separate the two compact sets by disjoint open sets `W₁` and `W₂`.
  obtain ⟨W₁, W₂, hW₁, hW₂, hKW₁, hKW₂, hW⟩ := SeparatedNhds.of_isCompact_isCompact
    (hK₁.image continuous_subtype_val) (hK₂.image continuous_subtype_val)
    ((disjoint_image_iff Subtype.val_injective).2 h)
  refine le_variationOuter fun V hKV hVΩ => ?_
  have hKV' : (↑) '' K₁ ⊆ (V : Set E) ∧ (↑) '' K₂ ⊆ (V : Set E) := by
    simpa [image_union] using hKV
  let V₁ : Opens E := V ⊓ ⟨W₁, hW₁⟩
  let V₂ : Opens E := V ⊓ ⟨W₂, hW₂⟩
  have hV₁ : V₁ ≤ Ω := inf_le_left.trans hVΩ
  have hV₂ : V₂ ≤ Ω := inf_le_left.trans hVΩ
  have hdisj : Disjoint V₁ V₂ := by
    rw [← Opens.coe_disjoint]
    exact hW.mono inter_subset_right inter_subset_right
  calc variationOuter μ Ω u K₁ + variationOuter μ Ω u K₂
      ≤ totalVariationOn μ V₁ u + totalVariationOn μ V₂ u :=
        add_le_add (variationOuter_le (subset_inter hKV'.1 hKW₁) hV₁)
          (variationOuter_le (subset_inter hKV'.2 hKW₂) hV₂)
    _ = totalVariationOn μ (V₁ ⊔ V₂) u :=
        (totalVariationOn_sup_of_disjoint (hu.mono_set (sup_le hV₁ hV₂)) hdisj).symm
    _ ≤ totalVariationOn μ V u := totalVariationOn_mono (sup_le inf_le_left inf_le_left)

variable (hu : LocallyIntegrableOn u Ω μ)
  (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
include hu hfin

/-- The variation content on `Ω`: the outer approximation of the total variation on compact
subsets of `Ω`, which is finite by local finiteness of the variation. -/
private def variationContent : Content Ω where
  toFun K := (variationOuter μ Ω u K).toNNReal
  mono' K₁ K₂ h := ENNReal.toNNReal_mono (variationOuter_ne_top hfin K₂.isCompact)
    (variationOuter_mono h)
  sup_disjoint' K₁ K₂ h _ _ := by
    rw [Compacts.coe_sup, ← ENNReal.toNNReal_add (variationOuter_ne_top hfin K₁.isCompact)
      (variationOuter_ne_top hfin K₂.isCompact)]
    exact congrArg ENNReal.toNNReal (le_antisymm (variationOuter_union_le hu _ _)
      (variationOuter_add_le_union hu K₁.isCompact K₂.isCompact h))
  sup_le' K₁ K₂ := by
    rw [Compacts.coe_sup, ← ENNReal.toNNReal_add (variationOuter_ne_top hfin K₁.isCompact)
      (variationOuter_ne_top hfin K₂.isCompact)]
    exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨variationOuter_ne_top hfin K₁.isCompact,
      variationOuter_ne_top hfin K₂.isCompact⟩) (variationOuter_union_le hu _ _)

private theorem variationContent_apply (K : Compacts Ω) :
    variationContent hu hfin K = variationOuter μ Ω u K := by
  simp [variationContent, ENNReal.coe_toNNReal (variationOuter_ne_top hfin K.isCompact)]

/-- The inner content of the variation content on an open set `U ⊆ Ω` is the total variation
on `U`. -/
private theorem innerContent_variationContent (hU : U ≤ Ω) :
    (variationContent hu hfin).innerContent
      ⟨(↑) ⁻¹' (U : Set E), U.isOpen.preimage continuous_subtype_val⟩ =
      totalVariationOn μ U u := by
  simp only [Content.innerContent, variationContent_apply, Opens.coe_mk]
  refine le_antisymm (iSup₂_le fun K hK => variationOuter_le (image_subset_iff.2 hK) hU)
    (totalVariationOn_le_iff.mpr fun φ hφ => ?_)
  -- The support of `φ` is a compact subset of `Ω`, on which the outer approximation is tested.
  have himage : ((↑) : Ω → E) '' ((↑) ⁻¹' tsupport φ) = tsupport φ :=
    image_preimage_eq_of_subset (by simpa using φ.tsupport_subset.trans hU)
  let K : Compacts Ω := ⟨(↑) ⁻¹' tsupport φ, by
    rw [Subtype.isCompact_iff, himage]
    exact φ.hasCompactSupport.isCompact⟩
  refine le_iSup₂_of_le K (preimage_mono φ.tsupport_subset) (le_variationOuter fun V hV _ => ?_)
  exact ofReal_integral_le_totalVariationOn_of_tsupport_subset φ hφ (himage ▸ hV)

end Content

/-! ### The variation measure -/

section Measure

variable [BorelSpace E]

open scoped Classical in
/-- The **variation measure** `|Du|` of `u` on the open set `Ω`: if `u` is locally integrable on
`Ω` and has locally finite variation there, meaning that every compact `K ⊆ Ω` has an open
neighbourhood `U` with `totalVariationOn μ U u < ∞`, it is the regular measure on `Ω` whose value
on every open `U ⊆ Ω` is the total variation of `u` on `U`
(`TauCeti.variationMeasure_preimage_coe`). Otherwise it is `0` by convention. -/
def variationMeasure (μ : Measure E) (Ω : Opens E) (u : E → ℝ) : Measure Ω :=
  if h : LocallyIntegrableOn u Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞ then
    (variationContent h.1 h.2).measure
  else 0

/-- The variation measure is a regular measure. -/
instance : (variationMeasure μ Ω u).Regular := by
  have := Ω.isOpen.locallyCompactSpace
  unfold variationMeasure
  split_ifs <;> infer_instance

/-- **The total variation is a measure.** The variation measure of a function of locally finite
variation on `Ω` gives every open set `U ⊆ Ω` its total variation `|Du|(U)`. -/
theorem variationMeasure_preimage_coe (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (hU : U ≤ Ω) :
    variationMeasure μ Ω u ((↑) ⁻¹' (U : Set E)) = totalVariationOn μ U u := by
  rw [variationMeasure, dite_eq_left ⟨hu, hfin⟩,
    Content.measure_apply _ (U.isOpen.preimage continuous_subtype_val).measurableSet,
    Content.outerMeasure_of_isOpen _ _ (U.isOpen.preimage continuous_subtype_val),
    innerContent_variationContent hu hfin hU]

/-- The total mass of the variation measure of a function of locally finite variation on `Ω` is
its total variation `|Du|(Ω)`. -/
theorem variationMeasure_univ (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞) :
    variationMeasure μ Ω u univ = totalVariationOn μ Ω u := by
  rw [← variationMeasure_preimage_coe hu hfin le_rfl]
  exact congrArg _ (eq_univ_of_forall fun x => x.2).symm

/-- The variation measure is `0` for a function which is not locally integrable on `Ω` or does
not have locally finite variation there. -/
theorem variationMeasure_eq_zero_of_not (h : ¬(LocallyIntegrableOn u Ω μ ∧
    ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)) :
    variationMeasure μ Ω u = 0 :=
  dite_eq_right h

/-- **Uniqueness of the variation measure.** An outer regular measure on `Ω` which gives every
open set `U ⊆ Ω` the total variation `|Du|(U)` is the variation measure. -/
theorem eq_variationMeasure (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    {ν : Measure Ω} [ν.OuterRegular]
    (h : ∀ U : Opens E, U ≤ Ω → ν ((↑) ⁻¹' (U : Set E)) = totalVariationOn μ U u) :
    ν = variationMeasure μ Ω u := by
  refine Measure.OuterRegular.ext_isOpen fun W hW => ?_
  -- An open subset of `Ω` is the trace of its image, an open subset of `E` inside `Ω`.
  let U : Opens E := ⟨(↑) '' W, Ω.isOpen.isOpenMap_subtype_val W hW⟩
  have hU : U ≤ Ω := Subtype.coe_image_subset _ _
  have hW' : ((↑) : Ω → E) ⁻¹' (U : Set E) = W := preimage_image_eq W Subtype.val_injective
  rw [← hW', h U hU, variationMeasure_preimage_coe hu hfin hU]

/-- **Locality.** The variation measure on `Ω` only depends on `u` almost everywhere on `Ω`. -/
theorem variationMeasure_congr_ae (h : u =ᵐ[μ.restrict Ω] v) :
    variationMeasure μ Ω u = variationMeasure μ Ω v := by
  have htv {U : Opens E} (hU : U ≤ Ω) : totalVariationOn μ U u = totalVariationOn μ U v :=
    totalVariationOn_congr_ae (ae_restrict_of_ae_restrict_of_subset hU h)
  -- Local finiteness of the variation only needs neighbourhoods inside `Ω`.
  have hfin {w : E → ℝ} : (∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U w ≠ ∞) ↔
      ∀ K, IsCompact K → K ⊆ Ω →
        ∃ U : Opens E, K ⊆ (U : Set E) ∧ U ≤ Ω ∧ totalVariationOn μ U w ≠ ∞ := by
    refine forall₃_congr fun K _ hKΩ => ⟨fun ⟨U, hKU, hU⟩ => ⟨U ⊓ Ω, ?_, inf_le_right,
      ne_top_of_le_ne_top hU (totalVariationOn_mono inf_le_left)⟩,
      fun ⟨U, hKU, _, hU⟩ => ⟨U, hKU, hU⟩⟩
    simpa using ⟨hKU, hKΩ⟩
  have hiff : (LocallyIntegrableOn u Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞) ↔
      (LocallyIntegrableOn v Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U v ≠ ∞) := by
    rw [locallyIntegrableOn_congr h, hfin, hfin]
    refine and_congr_right fun _ => forall₃_congr fun K _ _ => exists_congr fun U => ?_
    exact and_congr_right fun _ => and_congr_right fun hU => by rw [htv hU]
  by_cases hu : LocallyIntegrableOn u Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞
  · have hv := hiff.1 hu
    exact eq_variationMeasure hv.1 hv.2 fun U hU => by
      rw [variationMeasure_preimage_coe hu.1 hu.2 hU, htv hU]
  · rw [variationMeasure_eq_zero_of_not hu, variationMeasure_eq_zero_of_not (hiff.not.1 hu)]

end Measure

end TauCeti
