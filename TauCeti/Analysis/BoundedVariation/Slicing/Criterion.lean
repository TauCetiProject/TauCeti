/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DeGiorgi
public import TauCeti.Analysis.BoundedVariation.Slicing.Converse
public import TauCeti.MeasureTheory.Covering.EssentialBoundary.Basic
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.OneDimensional.EssentialBoundary
import TauCeti.MeasureTheory.Covering.EssentialBoundary.LineSection
import TauCeti.MeasureTheory.Function.Coarea.LineSection
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Federer's criterion for finite perimeter

Let `E` be a real inner product space of dimension `n` with its volume, `Ω ⊆ E` open and `s ⊆ E`
null-measurable, with essential boundary `∂ᵉs`. This file proves that the perimeter of `s` in `Ω`
is controlled by the `(n - 1)`-dimensional Hausdorff measure of `∂ᵉs ∩ Ω`:

* `TauCeti.perimeter_le_mul_euclideanHausdorffMeasure_essentialBoundary_inter`: in every
  dimension, `P(s; Ω) ≤ n 2ⁿ⁻¹ Hⁿ⁻¹(∂ᵉs ∩ Ω)`;
* `TauCeti.exists_perimeter_ne_top_of_euclideanHausdorffMeasure_essentialBoundary_inter_ne_top`:
  **Federer's criterion**: if `Hⁿ⁻¹(∂ᵉs ∩ K) < ∞` for every compact `K ⊆ Ω`, then `s` has locally
  finite perimeter in `Ω`;
* `TauCeti.perimeter_le_euclideanHausdorffMeasure_essentialBoundary_inter`: in every dimension,
  the sharp bound `P(s; Ω) ≤ Hⁿ⁻¹(∂ᵉs ∩ Ω)` in `[0, ∞]`.

Finite measure of the essential boundary is a hypothesis on `s` from which finite perimeter is
concluded; no regularity of `s` is assumed.

## Strategy

Fix a unit vector `e`. For almost every `y` in the hyperplane `(ℝ ∙ e)ᗮ`, the one-dimensional
essential boundary of the line section `{t | y + t • e ∈ s}`, inside the open set of parameters
of the line lying in `Ω`, consists of points of `∂ᵉs ∩ Ω` whenever the line meets `∂ᵉs ∩ Ω` in
finitely many points (`TauCeti.ae_essentialBoundary_lineSection_inter_subset`). On the line, the
perimeter is at most the number of essential boundary points
(`TauCeti.Real.perimeter_le_encard_essentialBoundary_inter`), so the perimeter of almost every
line section is at most the number of points of `∂ᵉs ∩ Ω` on the line (trivially so when there
are infinitely many). Integrating over the hyperplane, the projection bound
`TauCeti.lintegral_encard_lineSection_le_euclideanHausdorffMeasure` gives
`∫ P(s_y; Ω_y) dy ≤ 2ⁿ⁻¹ Hⁿ⁻¹(∂ᵉs ∩ Ω)`
(`TauCeti.lintegral_perimeter_lineSection_le_euclideanHausdorffMeasure`), and the converse
slicing inequality `TauCeti.perimeter_le_sum_lintegral_perimeter_lineSection`, applied along an
orthonormal basis, sums these bounds. In dimension `n ≤ 1` the factor `n 2ⁿ⁻¹` is at most `1`;
in dimension `n ≥ 2` the sharp bound follows from the criterion, De Giorgi's theorem
`TauCeti.perimeter_eq_euclideanHausdorffMeasure_reducedBoundary` and the inclusion
`TauCeti.reducedBoundary_subset_essentialBoundary`.

## References

* H. Federer, *Geometric Measure Theory*, 4.5.11.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.11 (criterion for finite perimeter).
-/

public section

open MeasureTheory Set TopologicalSpace Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {s : Set E}

namespace TauCeti

/-- **The perimeters of the line sections in one direction.** For a measurable set `s`, an open
set `Ω` and a unit vector `e`, the perimeters of the line sections `{t | y + t • e ∈ s}` in the
open sets of parameters of the lines lying in `Ω`, integrated over the orthogonal hyperplane, are
at most `2ⁿ⁻¹ Hⁿ⁻¹(∂ᵉs ∩ Ω)`. -/
theorem lintegral_perimeter_lineSection_le_euclideanHausdorffMeasure (hs : MeasurableSet s)
    (Ω : Opens E) {e : E} (he : ‖e‖ = 1) :
    ∫⁻ y : (ℝ ∙ e)ᗮ, perimeter volume
      (Opens.comap ⟨fun t : ℝ => (y : E) + t • e, by fun_prop⟩ Ω)
      {t : ℝ | (y : E) + t • e ∈ s} ≤
      2 ^ (finrank ℝ E - 1) * μHE[finrank ℝ E - 1] (essentialBoundary volume s ∩ Ω) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  refine (lintegral_mono_ae ?_).trans
    (lintegral_encard_lineSection_le_euclideanHausdorffMeasure he0 _)
  filter_upwards [ae_essentialBoundary_lineSection_inter_subset hs.nullMeasurableSet e he]
    with y hy
  set U : Opens ℝ := Opens.comap ⟨fun t : ℝ => (y : E) + t • e, by fun_prop⟩ Ω
  have hsec : MeasurableSet {t : ℝ | (y : E) + t • e ∈ s} :=
    hs.preimage (by fun_prop : Measurable fun t : ℝ => (y : E) + t • e)
  refine (Real.perimeter_le_encard_essentialBoundary_inter hsec.nullMeasurableSet U).trans ?_
  have heq : {t ∈ (U : Set ℝ) | (y : E) + t • e ∈ essentialBoundary volume s} =
      {t : ℝ | (y : E) + t • e ∈ essentialBoundary volume s ∩ Ω} := by
    ext t
    simp only [U, Opens.coe_comap, mem_preimage, ContinuousMap.coe_mk, SetLike.mem_coe,
      mem_ofPred_eq, mem_inter_iff, and_comm]
  rcases {t : ℝ | (y : E) + t • e ∈ essentialBoundary volume s ∩ Ω}.finite_or_infinite
    with hfin | hinf
  · have hsub : essentialBoundary volume {t : ℝ | (y : E) + t • e ∈ s} ∩ U ⊆
        {t : ℝ | (y : E) + t • e ∈ essentialBoundary volume s ∩ Ω} := fun t ht =>
      ⟨hy U U.isOpen (heq ▸ hfin) ht, ht.2⟩
    exact_mod_cast encard_le_encard hsub
  · rw [hinf.encard_eq]
    simp

/-- **The perimeter is bounded by the essential boundary.** For a null-measurable set `s` in a
space of dimension `n` and an open set `Ω`, `P(s; Ω) ≤ n 2ⁿ⁻¹ Hⁿ⁻¹(∂ᵉs ∩ Ω)`. In particular a set
whose essential boundary has finite `(n - 1)`-dimensional Hausdorff measure in `Ω` has finite
perimeter in `Ω`. -/
theorem perimeter_le_mul_euclideanHausdorffMeasure_essentialBoundary_inter
    (hs : NullMeasurableSet s volume) (Ω : Opens E) :
    perimeter volume Ω s ≤ finrank ℝ E * 2 ^ (finrank ℝ E - 1) *
      μHE[finrank ℝ E - 1] (essentialBoundary volume s ∩ Ω) := by
  obtain ⟨t, -, ht, hts⟩ := hs.exists_measurable_superset_ae_eq
  rw [perimeter_congr_ae (ae_restrict_of_ae hts.symm), essentialBoundary_congr_ae hts.symm]
  let b := stdOrthonormalBasis ℝ E
  refine (perimeter_le_sum_lintegral_perimeter_lineSection b ht.nullMeasurableSet).trans ?_
  refine (Finset.sum_le_sum fun i _ =>
    lintegral_perimeter_lineSection_le_euclideanHausdorffMeasure ht Ω
      (b.orthonormal.1 i)).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- **Federer's criterion for finite perimeter.** If the essential boundary of a null-measurable
set `s` has locally finite `(n - 1)`-dimensional Hausdorff measure in `Ω`, that is
`Hⁿ⁻¹(∂ᵉs ∩ K) < ∞` for every compact `K ⊆ Ω`, then `s` has locally finite perimeter in `Ω`:
every compact subset of `Ω` has an open neighborhood `U` with `P(s; U) < ∞`. -/
theorem exists_perimeter_ne_top_of_euclideanHausdorffMeasure_essentialBoundary_inter_ne_top
    (hs : NullMeasurableSet s volume)
    (h : ∀ K, IsCompact K → K ⊆ Ω →
      μHE[finrank ℝ E - 1] (essentialBoundary volume s ∩ K) ≠ ∞)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ U : Opens E, K ⊆ (U : Set E) ∧ perimeter volume U s ≠ ∞ := by
  obtain ⟨V, hVo, hKV, hVΩ, hV⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  refine ⟨⟨V, hVo⟩, hKV, ne_top_of_le_ne_top ?_
    (perimeter_le_mul_euclideanHausdorffMeasure_essentialBoundary_inter hs ⟨V, hVo⟩)⟩
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp))
    (ne_top_of_le_ne_top (h _ hV hVΩ) ?_)
  exact measure_mono (inter_subset_inter_right _ subset_closure)

/-- **The perimeter is at most the Hausdorff measure of the essential boundary.** Every
null-measurable set `s` in a real inner product space of any dimension `n` has
`P(s; Ω) ≤ Hⁿ⁻¹(∂ᵉs ∩ Ω)` in every open set `Ω`, as an inequality in `[0, ∞]`. -/
theorem perimeter_le_euclideanHausdorffMeasure_essentialBoundary_inter (Ω : Opens E)
    (hs : NullMeasurableSet s volume) :
    perimeter volume Ω s ≤ μHE[finrank ℝ E - 1] (essentialBoundary volume s ∩ Ω) := by
  rcases le_or_gt (finrank ℝ E) 1 with h1 | hn
  · refine (perimeter_le_mul_euclideanHausdorffMeasure_essentialBoundary_inter hs Ω).trans
      (mul_le_of_le_one_left zero_le ?_)
    obtain h | h : finrank ℝ E = 0 ∨ finrank ℝ E = 1 := by omega
    all_goals simp [h]
  by_cases hM : μHE[finrank ℝ E - 1] (essentialBoundary volume s ∩ Ω) = ∞
  · rw [hM]
    exact le_top
  have hfin (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞ := by
    simpa only [perimeter_def] using
      exists_perimeter_ne_top_of_euclideanHausdorffMeasure_essentialBoundary_inter_ne_top hs
        (fun L _ hLΩ => ne_top_of_le_ne_top hM (measure_mono (inter_subset_inter_right _ hLΩ)))
        hK hKΩ
  rw [perimeter_eq_euclideanHausdorffMeasure_reducedBoundary
    (locallyIntegrableOn_indicator_const (hs.mono Measure.restrict_le_self) 1) hfin]
  exact measure_mono (subset_inter (reducedBoundary_subset_essentialBoundary hn)
    reducedBoundary_subset)

end TauCeti
