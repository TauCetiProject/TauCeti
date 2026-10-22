/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices

/-!
# The coarea formula for linear maps

Let `L : E →ₗ[ℝ] F` be a linear map between finite-dimensional real inner product spaces of
dimensions `n` and `m`. Every nonempty fibre `L ⁻¹' {y}` is a translate of `ker L`; when `L` is
surjective it has dimension `n - m`. Slicing Lebesgue measure on `E` by these fibres gives the
linear coarea formula
`∫⁻ y, ∫⁻ x in L ⁻¹' {y}, g x ∂μHE[n - m] = J L * ∫⁻ x, g x`,
whose Jacobian `J L = (L.adjoint).normDet` is the norm determinant of the adjoint.
The fibres carry the normalized Hausdorff measure `μHE[n - m]` of the ambient space.
The formula holds for every linear map and every a.e.-measurable weight. When `L` is not
surjective, both sides vanish: the Jacobian is zero and almost every fibre is empty.

For the orthogonal projection onto a subspace the Jacobian is one. Its fibres are the affine
subspaces orthogonal to the subspace, so integrals over `E` slice along those subspaces.
Mathlib's `AffineSubspace.euclideanHausdorffMeasure_eq_lintegral` is the corresponding statement
for measurable sets, indexed by an affine subspace rather than by the projection.

The proof decomposes `E` orthogonally as `ker L × (ker L)ᗮ`. Mathlib's
`Submodule.measurePreserving_measurableEquivProd` then reduces the formula to Tonelli's theorem.
The restriction of `L` to `(ker L)ᗮ` is an isomorphism onto `F`, whose Jacobian is computed by
`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`.

## Main statements

* `LinearMap.lintegral_setLIntegral_preimage_singleton`: the linear coarea formula.
* `LinearMap.lintegral_euclideanHausdorffMeasure_inter_preimage_singleton`: its form for
  measurable sets.
* `LinearMap.measurable_setLIntegral_preimage_singleton`: measurability of the fibre integrals
  of a surjective linear map.
* `Submodule.lintegral_setLIntegral_preimage_orthogonalProjectionOnto`: slicing by orthogonal
  projections.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.2 (the coarea formula for linear maps).
-/

public section

open MeasureTheory Measure Set Module
open scoped ENNReal

namespace LinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The integral of `g` over the fibre `L ⁻¹' {L w}`, with Hausdorff measure of the dimension of
`ker L`, equals the Lebesgue integral over `ker L` of `a ↦ g (w + a)`. -/
theorem setLIntegral_preimage_singleton_eq_lintegral_ker (L : E →ₗ[ℝ] F) (w : E) (g : E → ℝ≥0∞) :
    ∫⁻ x in L ⁻¹' {L w}, g x ∂μHE[finrank ℝ (ker L)] = ∫⁻ a : ker L, g (w + a) := by
  let φ : ker L → E := fun a ↦ w + a
  have hφ : Isometry φ := (isometry_add_left w).comp isometry_subtype_coe
  have hrange : Set.range φ = L ⁻¹' {L w} := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨⟨x - w, by simp_all⟩, by simp [φ]⟩⟩
    rintro ⟨a, rfl⟩
    simp [φ]
  rw [← hrange, ← hφ.map_euclideanHausdorffMeasure,
    hφ.isClosedEmbedding.measurableEmbedding.lintegral_map,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

/-- A surjective linear map restricts to an isomorphism `e` from the orthogonal complement of its
kernel onto its codomain. The isomorphism scales Lebesgue measure by the Jacobian of the adjoint,
and each fibre integral is an integral over the kernel translated by `e.symm y`. -/
private theorem exists_orthogonal_ker_equiv (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) :
    ∃ e : (ker L)ᗮ ≃L[ℝ] F,
      (volume : Measure F) = ENNReal.ofReal L.adjoint.normDet •
        (volume : Measure (ker L)ᗮ).map e.toHomeomorph.toMeasurableEquiv ∧
      ∀ (g : E → ℝ≥0∞) (y : F), ∫⁻ x in L ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] =
        ∫⁻ a : ker L, g (e.symm y + a) := by
  have hdim := L.finrank_orthogonal_ker_of_surjective hL
  have h₁ := (ker L).finrank_add_finrank_orthogonal
  set W := (ker L)ᗮ
  set M := L ∘ₗ W.subtype
  have hMinj : Function.Injective M := by
    refine (injective_iff_map_eq_zero M).2 fun w hw ↦ Subtype.ext ?_
    have hk : (w : E) ∈ ker L := by simpa [M] using hw
    exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hk w.2)
  have hMbij : Function.Bijective M :=
    ⟨hMinj, (injective_iff_surjective_of_finrank_eq_finrank hdim).mp hMinj⟩
  let e : W ≃L[ℝ] F := (LinearEquiv.ofBijective M hMbij).toContinuousLinearEquiv
  have he (w : W) : e w = L w := by
    simp [e, M, LinearEquiv.ofBijective_apply]
  refine ⟨e, ?_, fun g y ↦ ?_⟩
  · -- Lebesgue measure on `F` is the image of Lebesgue measure on `W`, scaled by the Jacobian.
    ext t ht
    rw [Measure.smul_apply, MeasurableEquiv.map_apply, smul_eq_mul,
      normDet_adjoint_eq_normDet_comp_subtype L hL,
      ← M.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, hdim,
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    congr 1
    ext y
    exact ⟨fun hy ↦ ⟨e.symm y, by simpa [M, ← he] using hy, e.apply_symm_apply y⟩,
      by rintro ⟨w, hw, rfl⟩; simpa [M, ← he] using hw⟩
  · have hy : L (e.symm y : E) = y := by rw [← he, e.apply_symm_apply]
    rw [← L.setLIntegral_preimage_singleton_eq_lintegral_ker (e.symm y), hy,
      show finrank ℝ E - finrank ℝ F = finrank ℝ (ker L) by omega]

/-- The fibre integrals of a measurable function along a surjective linear map depend measurably
on the fibre. -/
theorem measurable_setLIntegral_preimage_singleton (L : E →ₗ[ℝ] F) (hL : Function.Surjective L)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun y ↦ ∫⁻ x in L ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  obtain ⟨e, -, hfib⟩ := L.exists_orthogonal_ker_equiv hL
  simp_rw [hfib]
  exact (Measurable.lintegral_prod_right' (f := fun q : (ker L)ᗮ × ker L ↦ g (q.1 + q.2))
    (hg.comp (measurable_fst.subtype_coe.add measurable_snd.subtype_coe))).comp
    e.symm.continuous.measurable

/-- The fibre integrals of a measurable function along any linear map are almost everywhere
measurable functions of the fibre. -/
theorem aemeasurable_setLIntegral_preimage_singleton (L : E →ₗ[ℝ] F) {g : E → ℝ≥0∞}
    (hg : Measurable g) :
    AEMeasurable fun y ↦ ∫⁻ x in L ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  by_cases hL : Function.Surjective L
  · exact (L.measurable_setLIntegral_preimage_singleton hL hg).aemeasurable
  · exact (aemeasurable_const (b := (0 : ℝ≥0∞))).congr
      ((L.ae_preimage_singleton_eq_empty volume hL).mono fun y hy ↦ by simp [hy])

/-- **The coarea formula for linear maps.** Integrating over the fibres of `L`, each with the
normalized Hausdorff measure of dimension `dim E - dim F`, gives the Jacobian `normDet` of the
adjoint of `L` times the Lebesgue integral. Both sides vanish when `L` is not surjective. -/
theorem lintegral_setLIntegral_preimage_singleton (L : E →ₗ[ℝ] F) {g : E → ℝ≥0∞}
    (hg : AEMeasurable g) :
    ∫⁻ y, ∫⁻ x in L ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] =
      ENNReal.ofReal L.adjoint.normDet * ∫⁻ x, g x := by
  by_cases hL : Function.Surjective L
  · obtain ⟨e, hvol, hfib⟩ := L.exists_orthogonal_ker_equiv hL
    simp_rw [hfib]
    rw [hvol, lintegral_smul_measure, lintegral_map_equiv, smul_eq_mul,
      (ker L).lintegral_eq_lintegral_lintegral_add hg]
    simp
  · have hJ : L.adjoint.normDet = 0 := by
      rw [normDet_eq_zero_iff_ker_ne_bot, ← orthogonal_range, Ne,
        Submodule.orthogonal_eq_bot_iff]
      exact mt range_eq_top.mp hL
    rw [hJ, ENNReal.ofReal_zero, zero_mul, ← lintegral_zero]
    exact lintegral_congr_ae
      ((L.ae_preimage_singleton_eq_empty volume hL).mono fun y hy ↦ by simp [hy])

/-- **The coarea formula for linear maps**, for Lebesgue-measurable sets: integrating the
`(dim E - dim F)`-dimensional measures of the fibres of a set gives the Jacobian of the adjoint
times its volume. -/
theorem lintegral_euclideanHausdorffMeasure_inter_preimage_singleton (L : E →ₗ[ℝ] F) {s : Set E}
    (hs : NullMeasurableSet s) :
    ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (s ∩ L ⁻¹' {y}) =
      ENNReal.ofReal L.adjoint.normDet * volume s := by
  have hind {t : Set E} (ht : MeasurableSet t) (y : F) :
      ∫⁻ x in L ⁻¹' {y}, t.indicator 1 x ∂μHE[finrank ℝ E - finrank ℝ F] =
        μHE[finrank ℝ E - finrank ℝ F] (t ∩ L ⁻¹' {y}) := by
    rw [lintegral_indicator_one ht, Measure.restrict_apply ht]
  have key {t : Set E} (ht : MeasurableSet t) :
      ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (t ∩ L ⁻¹' {y}) =
        ENNReal.ofReal L.adjoint.normDet * volume t := by
    simpa [hind ht, lintegral_indicator_one ht] using
      L.lintegral_setLIntegral_preimage_singleton (measurable_one.indicator ht).aemeasurable
  -- Squeeze `s` between measurable sets `t ⊆ s ⊆ u` differing by a null set.
  obtain ⟨t, hts, ht, hst⟩ := hs.exists_measurable_subset_ae_eq
  set u := toMeasurable volume s
  have hu : MeasurableSet u := measurableSet_toMeasurable _ _
  have hut : volume (u \ t) = 0 :=
    (ae_eq_set.1 (hs.toMeasurable_ae_eq.trans hst.symm)).1
  -- Almost every fibre of the null set `u \ t` is null.
  have hnull : ∀ᵐ y, μHE[finrank ℝ E - finrank ℝ F] ((u \ t) ∩ L ⁻¹' {y}) = 0 := by
    have h := key (hu.diff ht)
    rw [hut, mul_zero] at h
    refine (lintegral_eq_zero_iff' ?_).1 h
    simpa [hind (hu.diff ht)] using
      L.aemeasurable_setLIntegral_preimage_singleton (measurable_one.indicator (hu.diff ht))
  rw [← measure_congr hst, ← key ht]
  refine lintegral_congr_ae (hnull.mono fun y hy ↦ le_antisymm ?_ (measure_mono ?_))
  · calc μHE[finrank ℝ E - finrank ℝ F] (s ∩ L ⁻¹' {y})
        ≤ μHE[finrank ℝ E - finrank ℝ F] (t ∩ L ⁻¹' {y} ∪ (u \ t) ∩ L ⁻¹' {y}) := by
          refine measure_mono fun x ⟨hxs, hxy⟩ ↦ ?_
          by_cases hxt : x ∈ t
          · exact .inl ⟨hxt, hxy⟩
          · exact .inr ⟨⟨subset_toMeasurable _ _ hxs, hxt⟩, hxy⟩
      _ ≤ _ := (measure_union_le _ _).trans (by rw [hy, add_zero])
  · exact inter_subset_inter_left _ hts

end LinearMap

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Slicing by orthogonal projections.** Integrating over the fibres of the orthogonal
projection onto `K`, which are the affine subspaces parallel to `Kᗮ`, recovers the Lebesgue
integral. -/
theorem lintegral_setLIntegral_preimage_orthogonalProjectionOnto (K : Submodule ℝ E)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g) :
    ∫⁻ y : K, ∫⁻ x in K.orthogonalProjectionOnto ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ K] =
      ∫⁻ x, g x := by
  have h := (K.orthogonalProjectionOnto : E →ₗ[ℝ] K).lintegral_setLIntegral_preimage_singleton hg
  rw [ContinuousLinearMap.adjoint_toLinearMap, K.adjoint_orthogonalProjectionOnto] at h
  simpa using h

end Submodule
