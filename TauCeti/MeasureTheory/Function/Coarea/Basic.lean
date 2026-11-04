/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.MeasureTheory.Function.Coarea.Linear
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# The coarea formula for maps with surjective derivative

Let `E` and `F` be finite-dimensional real inner product spaces of dimensions `n` and `m`, and let
`f : E → F` be differentiable at every point of a Lebesgue-measurable set `s`, with surjective
derivative. This file proves the **coarea formula**

`∫⁻ y, μHE[n - m] (s ∩ f ⁻¹' {y}) = ∫⁻ x in s, J f x`,

where `J f x = (fderiv ℝ f x)†.normDet` is the coarea Jacobian, the norm determinant
(`LinearMap.normDet`) of the adjoint of the derivative, and the fibres carry the normalized
Hausdorff measure `μHE[n - m]` of `E`. For a Lipschitz map this is the coarea formula on the set
of points where the derivative exists and has full rank; for a submersion it holds on every
measurable set.

## The argument

Suppose that `f` is approximated on `s` by a linear map `L` up to `δ`, in the sense of
`ApproximatesLinearOn`, and that `M` is a continuous linear right inverse of `L`. The map
`h x = x + M (f x - L x)` satisfies `L ∘ h = f`, and it is approximated on `s` by the identity up to
`c = δ ‖M‖`. When `c < 1`, it distorts distances on `s` by factors between `1 - c` and `1 + c`,
and it maps each fibre `s ∩ f ⁻¹' {y}` onto the fibre `h '' s ∩ L ⁻¹' {y}` of the linear map `L`.
The linear coarea formula `LinearMap.lintegral_euclideanHausdorffMeasure_inter_preimage_singleton`
for `h '' s` then gives the coarea formula for `f` on `s` up to factors close to `1`
(`ApproximatesLinearOn.lintegral_euclideanHausdorffMeasure_inter_preimage_le`,
`ApproximatesLinearOn.ofReal_normDet_adjoint_mul_volume_le`).

To globalize, fix `τ > 1`. Splitting `s` into the level sets `τ ^ j ≤ J f x < τ ^ (j + 1)`,
`j ∈ ℤ`, and then by Mathlib's partition
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` gives countably many disjoint
measurable pieces on which both sides of the formula agree up to the factor `τ²`. The fibre
measures of the pieces are measurable functions of the fibre up to null sets
(`LocallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage`), so the estimates add
up, and `τ → 1` gives the formula for measurable `s`. A Lebesgue-null set has null fibres for
almost every `y` by Eilenberg's inequality, which extends the formula to Lebesgue-measurable `s`.
The structure follows the proof of the area formula in
`TauCeti.MeasureTheory.Function.AreaFormula.Basic`.

## Main declarations

* `ApproximatesLinearOn.exists_lipschitzOnWith_eq_image_inter_preimage`: near a linear map with a
  right inverse, the fibres of `f` are Lipschitz images of slices of the linear fibres.
* `ApproximatesLinearOn.lintegral_euclideanHausdorffMeasure_inter_preimage_le`,
  `ApproximatesLinearOn.ofReal_normDet_adjoint_mul_volume_le`: the coarea formula up to a
  controlled factor for a map approximated by a linear map with a right inverse.
* `TauCeti.measurable_normDet_adjoint_fderiv`: Borel measurability of the coarea Jacobian.
* `lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv`:
  the coarea formula for maps with surjective derivative.
* `ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_hasFDerivWithinAt`: almost every
  fibre of a Lebesgue-null set is null for a map differentiable on it.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 (the coarea formula).
* H. Federer, *Geometric Measure Theory*, §3.2 (the area and coarea formulas).
-/

public section

open MeasureTheory Measure Set Filter Metric Module Function
open scoped NNReal ENNReal Topology

namespace ApproximatesLinearOn

/-! ### Straightening a map along a right inverse of its linear approximation -/

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E →L[ℝ] F} {M : F →L[ℝ] E}
  {s : Set E} {δ : ℝ≥0}

/-- The map `x ↦ x + M (f x - L x)` is approximated on `s` by the identity up to `δ ‖M‖`. -/
private theorem approximatesLinearOn_straighten (hf : ApproximatesLinearOn f L s δ) :
    ApproximatesLinearOn (fun x ↦ x + M (f x - L x))
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) s (δ * ‖M‖₊) := by
  refine LipschitzOnWith.approximatesLinearOn ?_
  have h : (fun x ↦ x + M (f x - L x)) - ⇑(ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) =
      M ∘ (f - ⇑L) := by
    ext x
    simp
  rw [h, mul_comm]
  exact M.lipschitzWith.comp_lipschitzOnWith hf.lipschitzOnWith

/-- The map `x ↦ x + M (f x - L x)` is `(1 + δ ‖M‖)`-Lipschitz on `s`. -/
private theorem lipschitzOnWith_straighten (hf : ApproximatesLinearOn f L s δ) :
    LipschitzOnWith (1 + δ * ‖M‖₊) (fun x ↦ x + M (f x - L x)) s := by
  refine lipschitzOnWith_iff_restrict.2
    ((approximatesLinearOn_straighten hf).lipschitzWith.weaken ?_)
  gcongr
  rw [ContinuousLinearEquiv.coe_refl, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact ContinuousLinearMap.norm_id_le

/-- If `δ ‖M‖ < 1`, then the map `x ↦ x + M (f x - L x)` expands distances on `s` by at least the
factor `1 - δ ‖M‖`. -/
private theorem antilipschitzWith_straighten (hf : ApproximatesLinearOn f L s δ)
    (hδ : δ * ‖M‖₊ < 1) :
    AntilipschitzWith (1 - δ * ‖M‖₊)⁻¹ (s.domRestrict fun x ↦ x + M (f x - L x)) := by
  -- The identity has norm `1` unless `E` is trivial.
  cases subsingleton_or_nontrivial E
  · exact AntilipschitzWith.of_subsingleton
  simpa using (approximatesLinearOn_straighten hf).antilipschitzWith (Or.inr (by simpa using hδ))

/-- If `δ ‖M‖ < 1`, then the map `x ↦ x + M (f x - L x)` is injective on `s`. -/
private theorem injOn_straighten (hf : ApproximatesLinearOn f L s δ) (hδ : δ * ‖M‖₊ < 1) :
    InjOn (fun x ↦ x + M (f x - L x)) s :=
  injOn_iff_injective.2 (antilipschitzWith_straighten hf hδ).injective

/-- The map `x ↦ x + M (f x - L x)` sends the fibre `s ∩ f ⁻¹' {y}` onto the fibre of the linear
map `L` through its image. -/
private theorem image_straighten_inter_preimage (hM : RightInverse M L) (y : F) :
    (fun x ↦ x + M (f x - L x)) '' (s ∩ f ⁻¹' {y}) =
      (fun x ↦ x + M (f x - L x)) '' s ∩ L ⁻¹' {y} := by
  have hL (x : E) : L (x + M (f x - L x)) = f x := by rw [map_add, hM, add_sub_cancel]
  ext z
  simp only [mem_image, mem_inter_iff, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨x, ⟨hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hL x⟩
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, (hL x).symm.trans hy⟩, rfl⟩

/-- If `δ ‖M‖ < 1`, the straightening map `h x = x + M (f x - L x)` admits a
`(1 - δ ‖M‖)⁻¹`-Lipschitz left inverse on `h '' s`. -/
private theorem exists_lipschitzOnWith_leftInvOn_straighten (hf : ApproximatesLinearOn f L s δ)
    (hδ : δ * ‖M‖₊ < 1) :
    ∃ g : E → E, LipschitzOnWith (1 - δ * ‖M‖₊)⁻¹ g ((fun x ↦ x + M (f x - L x)) '' s) ∧
      LeftInvOn g (fun x ↦ x + M (f x - L x)) s :=
  ⟨invFunOn (fun x ↦ x + M (f x - L x)) s,
    lipschitzOnWith_iff_restrict.2 ((antilipschitzWith_straighten hf hδ).to_rightInvOn'
      (surjOn_image _ s).mapsTo_invFunOn (surjOn_image _ s).rightInvOn_invFunOn),
    (injOn_straighten hf hδ).leftInvOn_invFunOn⟩

/-- If `f` is approximated on `s` up to `δ` by a continuous linear map `L` with a continuous linear
right inverse `M` satisfying `δ ‖M‖ < 1`, then there are a set `t` and a `(1 - δ ‖M‖)⁻¹`-Lipschitz
map `g` on `t` that maps each linear slice `t ∩ L ⁻¹' {y}` onto the fibre `s ∩ f ⁻¹' {y}`. -/
theorem exists_lipschitzOnWith_eq_image_inter_preimage (hf : ApproximatesLinearOn f L s δ)
    (hM : RightInverse M L) (hδ : δ * ‖M‖₊ < 1) :
    ∃ (t : Set E) (g : E → E), LipschitzOnWith (1 - δ * ‖M‖₊)⁻¹ g t ∧
      ∀ y, s ∩ f ⁻¹' {y} = g '' (t ∩ L ⁻¹' {y}) := by
  obtain ⟨g, hlip, hg⟩ := exists_lipschitzOnWith_leftInvOn_straighten hf hδ
  refine ⟨(fun x ↦ x + M (f x - L x)) '' s, g, hlip, fun y ↦ ?_⟩
  rw [← image_straighten_inter_preimage hM, image_image]
  exact ((image_congr fun x (hx : x ∈ s ∩ f ⁻¹' {y}) ↦ hg hx.1).trans (image_id' _)).symm

variable [MeasurableSpace E] [BorelSpace E]

/-- If `δ ‖M‖ < 1`, then the map `x ↦ x + M (f x - L x)` shrinks the `d`-dimensional measure of
subsets of `s` by at most the factor `(1 - δ ‖M‖)ᵈ`. -/
private theorem euclideanHausdorffMeasure_le_image_straighten
    (hf : ApproximatesLinearOn f L s δ) (hδ : δ * ‖M‖₊ < 1) {t : Set E} (ht : t ⊆ s) (d : ℕ) :
    μHE[d] t ≤ ((1 - δ * ‖M‖₊)⁻¹ ^ d : ℝ≥0) * μHE[d] ((fun x ↦ x + M (f x - L x)) '' t) := by
  obtain ⟨g, hlip, hg⟩ := exists_lipschitzOnWith_leftInvOn_straighten hf hδ
  have himage : t = g '' ((fun x ↦ x + M (f x - L x)) '' t) := by
    rw [image_image]
    exact ((image_congr fun x hx ↦ hg (ht hx)).trans (image_id' t)).symm
  rw [ENNReal.coe_pow]
  conv_lhs => rw [himage]
  exact (hlip.mono (image_mono ht)).euclideanHausdorffMeasure_image_le d

end NormedSpace

/-! ### The coarea formula near a linear map -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f : E → F} {L : E →L[ℝ] F} {M : F →L[ℝ] E}
  {s : Set E} {δ : ℝ≥0} [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Upper coarea bound near a linear map.** If `f` is approximated on `s` up to `δ` by a linear
map `L` with a right inverse `M`, and `δ ‖M‖ < 1`, then the integral of the
`(n - m)`-dimensional measures of the fibres of `f` on `s` is at most
`((1 - δ ‖M‖)⁻¹)^(n - m) (1 + δ ‖M‖)ⁿ J L vol s`, where `n = dim E`, `m = dim F` and `J L` is
the norm determinant of the adjoint of `L`. No measurability of `s` is needed. -/
theorem lintegral_euclideanHausdorffMeasure_inter_preimage_le
    (hf : ApproximatesLinearOn f L s δ) (hM : RightInverse M L) (hδ : δ * ‖M‖₊ < 1) :
    ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) ≤
      ((1 - δ * ‖M‖₊)⁻¹ ^ (finrank ℝ E - finrank ℝ F) * (1 + δ * ‖M‖₊) ^ finrank ℝ E : ℝ≥0) *
        (ENNReal.ofReal L.adjoint.normDet * volume s) := by
  set h : E → E := fun x ↦ x + M (f x - L x)
  set k := finrank ℝ E - finrank ℝ F
  set T := toMeasurable volume (h '' s)
  have hfib (y : F) : μHE[k] (s ∩ f ⁻¹' {y}) ≤
      ((1 - δ * ‖M‖₊)⁻¹ ^ k : ℝ≥0) * μHE[k] (T ∩ (L : E →ₗ[ℝ] F) ⁻¹' {y}) := by
    refine (euclideanHausdorffMeasure_le_image_straighten hf hδ inter_subset_left k).trans ?_
    rw [image_straighten_inter_preimage hM, ContinuousLinearMap.coe_coe]
    gcongr
    exact subset_toMeasurable _ _
  have hvol : volume (h '' s) ≤ ((1 + δ * ‖M‖₊) ^ finrank ℝ E : ℝ≥0) * volume s := by
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, ENNReal.coe_pow]
    exact (lipschitzOnWith_straighten hf).euclideanHausdorffMeasure_image_le _
  calc ∫⁻ y, μHE[k] (s ∩ f ⁻¹' {y})
      ≤ ∫⁻ y, ((1 - δ * ‖M‖₊)⁻¹ ^ k : ℝ≥0) * μHE[k] (T ∩ (L : E →ₗ[ℝ] F) ⁻¹' {y}) :=
        lintegral_mono hfib
    _ = ((1 - δ * ‖M‖₊)⁻¹ ^ k : ℝ≥0) * (ENNReal.ofReal L.adjoint.normDet * volume (h '' s)) := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          (L : E →ₗ[ℝ] F).lintegral_euclideanHausdorffMeasure_inter_preimage_singleton
            (measurableSet_toMeasurable _ _).nullMeasurableSet, measure_toMeasurable,
          ContinuousLinearMap.adjoint_toLinearMap]
    _ ≤ ((1 - δ * ‖M‖₊)⁻¹ ^ k : ℝ≥0) * (ENNReal.ofReal L.adjoint.normDet *
          (((1 + δ * ‖M‖₊) ^ finrank ℝ E : ℝ≥0) * volume s)) := by gcongr
    _ = _ := by rw [ENNReal.coe_mul]; ring

/-- **Lower coarea bound near a linear map.** If `f` is approximated on a Lebesgue-measurable set
`s` up to `δ` by a linear map `L` with a right inverse `M`, and `δ ‖M‖ < 1`, then `J L vol s` is
at most `((1 - δ ‖M‖)⁻¹)ⁿ (1 + δ ‖M‖)^(n - m)` times the integral of the `(n - m)`-dimensional
measures of the fibres of `f` on `s`, where `n = dim E`, `m = dim F` and `J L` is the norm
determinant of the adjoint of `L`. -/
theorem ofReal_normDet_adjoint_mul_volume_le
    (hf : ApproximatesLinearOn f L s δ) (hM : RightInverse M L) (hδ : δ * ‖M‖₊ < 1)
    (hs : NullMeasurableSet s) :
    ENNReal.ofReal L.adjoint.normDet * volume s ≤
      ((1 - δ * ‖M‖₊)⁻¹ ^ finrank ℝ E * (1 + δ * ‖M‖₊) ^ (finrank ℝ E - finrank ℝ F) : ℝ≥0) *
        ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) := by
  set h : E → E := fun x ↦ x + M (f x - L x)
  set k := finrank ℝ E - finrank ℝ F
  have hlip := lipschitzOnWith_straighten (M := M) hf
  -- `h '' s` is Lebesgue measurable: `h` is a continuous injection on a Borel subset of `s` of
  -- full measure, and Lipschitz on the null remainder.
  have hmeas : NullMeasurableSet (h '' s) := by
    obtain ⟨t, hts, ht, hst⟩ := hs.exists_measurable_subset_ae_eq
    have hnull : volume (h '' (s \ t)) = 0 := by
      rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      refine nonpos_iff_eq_zero.1 (((hlip.mono sdiff_subset).euclideanHausdorffMeasure_image_le
        _).trans_eq ?_)
      rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, (ae_eq_set.1 hst).2, mul_zero]
    rw [← union_sdiff_cancel hts, image_union]
    exact (ht.image_of_continuousOn_injOn (hlip.continuousOn.mono hts)
      ((injOn_straighten hf hδ).mono hts)).nullMeasurableSet.union
      (NullMeasurableSet.of_null hnull)
  have hvol : volume s ≤ ((1 - δ * ‖M‖₊)⁻¹ ^ finrank ℝ E : ℝ≥0) * volume (h '' s) := by
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
      euclideanHausdorffMeasure_le_image_straighten hf hδ subset_rfl (finrank ℝ E)
  have hfib (y : F) : μHE[k] (h '' s ∩ (L : E →ₗ[ℝ] F) ⁻¹' {y}) ≤
      ((1 + δ * ‖M‖₊) ^ k : ℝ≥0) * μHE[k] (s ∩ f ⁻¹' {y}) := by
    rw [ContinuousLinearMap.coe_coe, ← image_straighten_inter_preimage hM, ENNReal.coe_pow]
    exact (hlip.mono inter_subset_left).euclideanHausdorffMeasure_image_le k
  calc ENNReal.ofReal L.adjoint.normDet * volume s
      ≤ ENNReal.ofReal L.adjoint.normDet *
          (((1 - δ * ‖M‖₊)⁻¹ ^ finrank ℝ E : ℝ≥0) * volume (h '' s)) := by gcongr
    _ = ((1 - δ * ‖M‖₊)⁻¹ ^ finrank ℝ E : ℝ≥0) *
          ∫⁻ y, μHE[k] (h '' s ∩ (L : E →ₗ[ℝ] F) ⁻¹' {y}) := by
        rw [(L : E →ₗ[ℝ] F).lintegral_euclideanHausdorffMeasure_inter_preimage_singleton hmeas,
          ContinuousLinearMap.adjoint_toLinearMap]
        ring
    _ ≤ ((1 - δ * ‖M‖₊)⁻¹ ^ finrank ℝ E : ℝ≥0) *
          ∫⁻ y, ((1 + δ * ‖M‖₊) ^ k : ℝ≥0) * μHE[k] (s ∩ f ⁻¹' {y}) := by
        gcongr with y
        exact hfib y
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ENNReal.coe_mul]

end ApproximatesLinearOn

namespace TauCeti

/-- The coarea Jacobian `x ↦ (fderiv ℝ f x)†.normDet` of a map between finite-dimensional real
inner product spaces is Borel measurable. -/
@[fun_prop]
theorem measurable_normDet_adjoint_fderiv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (f : E → F) :
    Measurable fun x ↦ (fderiv ℝ f x).adjoint.normDet :=
  ContinuousLinearMap.continuous_normDet_adjoint.measurable.comp (measurable_fderiv ℝ f)

end TauCeti

namespace MeasureTheory

/-! ### Globalization -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f : E → F} {L : E →L[ℝ] F} {M : F →L[ℝ] E}
  {s : Set E} {δ : ℝ≥0} [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The coarea formula on one piece, up to factors: if `f` is approximated on `Q` by a linear map
`L` with a right inverse `M`, with a precision for which the factors of the two linear coarea
bounds are at most `τ`, and `j` agrees with `J L` on `Q` up to the factor `σ`, then the integral of
the fibre measures of `Q` and `∫⁻ x in Q, j x` agree up to the factor `τ σ`. -/
private theorem lintegral_le_and_setLIntegral_le {Q : Set E} (hQ : MeasurableSet Q)
    {j : E → ℝ≥0∞} {τ σ : ℝ≥0} (hf : ApproximatesLinearOn f L Q δ) (hM : RightInverse M L)
    (hδ : δ * ‖M‖₊ < 1)
    (h₁ : (1 - δ * ‖M‖₊)⁻¹ ^ (finrank ℝ E - finrank ℝ F) * (1 + δ * ‖M‖₊) ^ finrank ℝ E ≤ τ)
    (h₂ : (1 - δ * ‖M‖₊)⁻¹ ^ finrank ℝ E * (1 + δ * ‖M‖₊) ^ (finrank ℝ E - finrank ℝ F) ≤ τ)
    (hj : ∀ x ∈ Q, ENNReal.ofReal L.adjoint.normDet ≤ σ * j x ∧
      j x ≤ σ * ENNReal.ofReal L.adjoint.normDet) :
    ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (Q ∩ f ⁻¹' {y}) ≤ (τ * σ : ℝ≥0) * ∫⁻ x in Q, j x ∧
      ∫⁻ x in Q, j x ≤
        (σ * τ : ℝ≥0) * ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (Q ∩ f ⁻¹' {y}) := by
  constructor
  · calc ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (Q ∩ f ⁻¹' {y})
        ≤ _ := hf.lintegral_euclideanHausdorffMeasure_inter_preimage_le hM hδ
      _ ≤ (τ : ℝ≥0∞) * ∫⁻ x in Q, (σ : ℝ≥0∞) * j x := by
          rw [← setLIntegral_const]
          exact mul_le_mul' (ENNReal.coe_le_coe.2 h₁) (setLIntegral_mono' hQ fun x hx ↦ (hj x hx).1)
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ENNReal.coe_mul]
  · calc ∫⁻ x in Q, j x ≤ ∫⁻ x in Q, (σ : ℝ≥0∞) * ENNReal.ofReal L.adjoint.normDet :=
          setLIntegral_mono' hQ fun x hx ↦ (hj x hx).2
      _ = σ * (ENNReal.ofReal L.adjoint.normDet * volume Q) := by
          rw [setLIntegral_const, mul_assoc]
      _ ≤ σ * (τ * ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (Q ∩ f ⁻¹' {y})) := by
          exact mul_le_mul' le_rfl
            ((hf.ofReal_normDet_adjoint_mul_volume_le hM hδ hQ.nullMeasurableSet).trans
              (mul_le_mul' (ENNReal.coe_le_coe.2 h₂) le_rfl))
      _ = _ := by rw [← mul_assoc, ENNReal.coe_mul]

/-- A measurable set `s` on which `f` is differentiable with surjective derivative splits into
countably many disjoint measurable pieces, on each of which `f` is Lipschitz and the coarea formula
holds up to the factor `τ²`. -/
private theorem exists_partition_le_and_le (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    {τ : ℝ≥0} (hτ : 1 < τ) :
    ∃ P : ℤ × ℕ → Set E, (∀ p, MeasurableSet (P p)) ∧ Pairwise (Disjoint on P) ∧
      ⋃ p, P p = s ∧ ∀ p, ∃ K, LipschitzOnWith K f (P p) ∧
        ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (P p ∩ f ⁻¹' {y}) ≤
            (τ ^ 2 : ℝ≥0) * ∫⁻ x in P p, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet ∧
          ∫⁻ x in P p, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet ≤
            (τ ^ 2 : ℝ≥0) * ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (P p ∩ f ⁻¹' {y}) := by
  have hτ' : (1 : ℝ) < τ := by exact_mod_cast hτ
  -- For each surjective `A`, choose a right inverse `M A` and a precision `δ A` adapted to `τ`.
  have hA (A : E →L[ℝ] F) : ∃ (M : F →L[ℝ] E) (δ : ℝ≥0), 0 < δ ∧ (Surjective A →
      RightInverse M A ∧ δ * ‖M‖₊ < 1 ∧
      (1 - δ * ‖M‖₊)⁻¹ ^ (finrank ℝ E - finrank ℝ F) * (1 + δ * ‖M‖₊) ^ finrank ℝ E ≤ τ ∧
      (1 - δ * ‖M‖₊)⁻¹ ^ finrank ℝ E * (1 + δ * ‖M‖₊) ^ (finrank ℝ E - finrank ℝ F) ≤ τ) := by
    by_cases h : Surjective A
    · have hR : A.HasRightInverse := .of_surjective_of_finiteDimensional h
      -- Both factors are continuous in `δ` and equal `1 < τ` at `δ = 0`.
      have hlim (a b : ℕ) : ∀ᶠ δ : ℝ≥0 in 𝓝 0,
          (1 - δ * ‖hR.rightInverse‖₊)⁻¹ ^ a * (1 + δ * ‖hR.rightInverse‖₊) ^ b < τ := by
        have hc : ContinuousAt
            (fun δ : ℝ≥0 ↦ (1 - δ * ‖hR.rightInverse‖₊)⁻¹ ^ a * (1 + δ * ‖hR.rightInverse‖₊) ^ b)
            0 := by
          fun_prop (disch := simp)
        exact hc.tendsto.eventually_lt_const (by simpa using hτ)
      have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * ‖hR.rightInverse‖₊ < 1 :=
        (continuous_id.mul continuous_const).continuousAt.tendsto.eventually_lt_const
          (by simp)
      obtain ⟨δ, ⟨⟨h₁, h₂⟩, h₃⟩, hδ⟩ :=
        ((((hlim _ _).and (hlim _ _)).and hsmall).filter_mono nhdsWithin_le_nhds).and
          (self_mem_nhdsWithin (s := Ioi (0 : ℝ≥0))) |>.exists
      exact ⟨hR.rightInverse, δ, hδ, fun _ ↦
        ⟨hR.rightInverse_rightInverse, h₃, h₁.le, h₂.le⟩⟩
    · exact ⟨0, 1, one_pos, fun h' ↦ (h h').elim⟩
  choose M δ hδpos hδ using hA
  -- Split `s` into the level sets `τ ^ j ≤ J f x < τ ^ (j + 1)` of the coarea Jacobian, then
  -- into pieces on which `f` is approximated by a linear map.
  set J : E → ℝ := fun x ↦ (fderiv ℝ f x).adjoint.normDet
  set S : ℤ → Set E := fun j ↦ s ∩ J ⁻¹' Ico ((τ : ℝ) ^ j) ((τ : ℝ) ^ (j + 1))
  have hSm (j : ℤ) : MeasurableSet (S j) :=
    hs.inter (TauCeti.measurable_normDet_adjoint_fderiv f measurableSet_Ico)
  have hSd : Pairwise (Disjoint on S) := by
    intro i j hij
    refine disjoint_left.2 fun x hi hj ↦ hij (le_antisymm ?_ ?_)
    · exact Int.lt_add_one_iff.1 ((zpow_lt_zpow_iff_right₀ hτ').1 (hi.2.1.trans_lt hj.2.2))
    · exact Int.lt_add_one_iff.1 ((zpow_lt_zpow_iff_right₀ hτ').1 (hj.2.1.trans_lt hi.2.2))
  choose t A ht_disj ht_meas ht_cover ht_approx ht_A using fun j ↦
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f (S j) (fderiv ℝ f)
      (fun x hx ↦ (hd x hx.1).hasFDerivAt.hasFDerivWithinAt) δ fun A ↦ (hδpos A).ne'
  refine ⟨fun p ↦ S p.1 ∩ t p.1 p.2, fun p ↦ (hSm p.1).inter (ht_meas p.1 p.2), ?_, ?_, ?_⟩
  · rintro ⟨i, n⟩ ⟨j, n'⟩ hne
    by_cases hij : i = j
    · subst hij
      exact (ht_disj i fun hn ↦ hne (Prod.ext rfl hn)).mono inter_subset_right
        inter_subset_right
    · exact (hSd hij).mono inter_subset_left inter_subset_left
  · refine Subset.antisymm (iUnion_subset fun p ↦ inter_subset_left.trans inter_subset_left)
      fun x hx ↦ ?_
    obtain ⟨j, hj⟩ := exists_mem_Ico_zpow
      (ContinuousLinearMap.normDet_adjoint_pos_iff.2 (hsurj x hx)) hτ'
    obtain ⟨n, hn⟩ := mem_iUnion.1 (ht_cover j ⟨hx, hj⟩)
    exact mem_iUnion.2 ⟨(j, n), ⟨hx, hj⟩, hn⟩
  · -- On a nonempty piece, `J A` and every `J f x` lie in the same interval `[τ ^ j, τ ^ (j + 1))`,
    -- so they agree up to the factor `τ`.
    rintro ⟨j, n⟩
    refine ⟨_, lipschitzOnWith_iff_restrict.2 (ht_approx j n).lipschitzWith, ?_⟩
    rcases (S j ∩ t j n).eq_empty_or_nonempty with h | ⟨x₁, hx₁⟩
    · simp [h]
    obtain ⟨y, hy, hAy⟩ := ht_A j ⟨x₁, hx₁.1⟩ n
    obtain ⟨hM, hδM, h₁, h₂⟩ := hδ (A j n) (hAy ▸ hsurj y hy.1)
    have hAJ : (A j n).adjoint.normDet ∈ Ico ((τ : ℝ) ^ j) ((τ : ℝ) ^ (j + 1)) := hAy ▸ hy.2
    rw [sq]
    refine lintegral_le_and_setLIntegral_le ((hSm j).inter (ht_meas j n)) (ht_approx j n) hM hδM
      h₁ h₂ fun x hx ↦ ?_
    have hxJ : J x ∈ Ico ((τ : ℝ) ^ j) ((τ : ℝ) ^ (j + 1)) := hx.1.2
    rw [zpow_add_one₀ (by positivity)] at hAJ hxJ
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul τ.coe_nonneg,
      ← ENNReal.ofReal_mul τ.coe_nonneg]
    exact ⟨ENNReal.ofReal_le_ofReal (by nlinarith [hAJ.2, hxJ.1]),
      ENNReal.ofReal_le_ofReal (by nlinarith [hAJ.1, hxJ.2])⟩

/-- The coarea formula up to the factor `τ²`, for every `τ > 1`: sum the estimates on the pieces
of `exists_partition_le_and_le`, whose fibres are disjoint and measurable. -/
private theorem lintegral_le_and_setLIntegral_le_of_one_lt (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    {τ : ℝ≥0} (hτ : 1 < τ) :
    ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) ≤
        (τ ^ 2 : ℝ≥0) * ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet ∧
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet ≤
        (τ ^ 2 : ℝ≥0) * ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) := by
  obtain ⟨P, hPm, hPd, hPU, hpiece⟩ := exists_partition_le_and_le hs hd hsurj hτ
  choose K hK hpiece using hpiece
  -- The fibres of the pieces are disjoint and measurable, since `f` is continuous on each piece.
  have hfib (y : F) : μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∑' p, μHE[finrank ℝ E - finrank ℝ F] (P p ∩ f ⁻¹' {y}) := by
    rw [← hPU, iUnion_inter]
    refine measure_iUnion (fun p q hpq ↦ (hPd hpq).mono inter_subset_left inter_subset_left)
      fun p ↦ ?_
    obtain ⟨u, hu, hfu⟩ := continuousOn_iff_isClosed.1 (hK p).continuousOn {y} isClosed_singleton
    rw [inter_comm, hfu]
    exact hu.measurableSet.inter (hPm p)
  have hint : ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∑' p, ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (P p ∩ f ⁻¹' {y}) := by
    simp_rw [hfib]
    exact lintegral_tsum fun p ↦
      (hK p).locallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage
        volume (hPm p).nullMeasurableSet le_add_tsub
  rw [hint, ← hPU, lintegral_iUnion hPm hPd, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨tsum_le_tsum fun p ↦ (hpiece p).1, tsum_le_tsum fun p ↦ (hpiece p).2⟩

/-- The coarea formula for maps with surjective derivative on a measurable set: both
inequalities hold up to the factor `τ²` for every `τ > 1`; let `τ → 1`. -/
private theorem lintegral_eq_setLIntegral_normDet_adjoint_fderiv (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) :
    ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet := by
  have hlim {a b : ℝ≥0∞} (h : ∀ τ : ℝ≥0, 1 < τ → a ≤ (τ ^ 2 : ℝ≥0) * b) : a ≤ b := by
    rcases eq_or_ne b ⊤ with rfl | hb
    · exact le_top
    have ht : Tendsto (fun τ : ℝ≥0 ↦ ((τ ^ 2 : ℝ≥0) : ℝ≥0∞) * b) (𝓝[>] 1) (𝓝 b) := by
      have h1 : Tendsto (fun τ : ℝ≥0 ↦ ((τ ^ 2 : ℝ≥0) : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) := by
        have := ((continuous_pow 2).tendsto (1 : ℝ≥0)).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
        simpa using ENNReal.tendsto_coe.2 this
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hb)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun τ hτ ↦ h τ hτ)
  exact le_antisymm
    (hlim fun _ hτ ↦ (lintegral_le_and_setLIntegral_le_of_one_lt hs hd hsurj hτ).1)
    (hlim fun _ hτ ↦ (lintegral_le_and_setLIntegral_le_of_one_lt hs hd hsurj hτ).2)

/-- If `f` has a derivative within a Lebesgue-null set `N` at each of its points, then almost
every fibre `N ∩ f ⁻¹' {y}` is null for the `(dim E - dim F)`-dimensional Euclidean Hausdorff
measure. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_hasFDerivWithinAt {N : Set E}
    {f' : E → E →L[ℝ] F} (hN : volume N = 0) (hd : ∀ x ∈ N, HasFDerivWithinAt f (f' x) N x) :
    ∀ᵐ y, μHE[finrank ℝ E - finrank ℝ F] (N ∩ f ⁻¹' {y}) = 0 := by
  -- `f` is Lipschitz on each piece of a countable cover of `N`; apply Eilenberg's inequality.
  obtain ⟨t, A, -, -, hcover, happrox, -⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f N f' hd (fun _ ↦ 1)
      fun _ ↦ one_ne_zero
  have hnull (n : ℕ) : μHE[finrank ℝ F + (finrank ℝ E - finrank ℝ F)] (N ∩ t n) = 0 := by
    have h : μHE[finrank ℝ E] (N ∩ t n) = 0 := by
      rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact measure_mono_null inter_subset_left hN
    rw [euclideanHausdorffMeasure_eq_zero_iff] at h ⊢
    exact nonpos_iff_eq_zero.1
      ((hausdorffMeasure_mono (by exact_mod_cast le_add_tsub) _).trans h.le)
  have hfib := ae_all_iff.2 fun n ↦ (lipschitzOnWith_iff_restrict.2
    (happrox n).lipschitzWith).ae_euclideanHausdorffMeasure_inter_preimage_eq_zero volume (hnull n)
  filter_upwards [hfib] with y hy
  refine measure_mono_null (fun x hx ↦ ?_) (measure_iUnion_null hy)
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hcover hx.1)
  exact mem_iUnion.2 ⟨n, ⟨hx.1, hn⟩, hx.2⟩

/-- **The coarea formula** for maps with surjective derivative. Let `E` and `F` be
finite-dimensional real inner product spaces and let `f : E → F` be differentiable at every point
of a Lebesgue-measurable set `s`, with surjective derivative. Then integrating over `F` the
`(dim E - dim F)`-dimensional Euclidean Hausdorff measures of the fibres `s ∩ f ⁻¹' {y}` gives the
integral over `s` of the coarea Jacobian, the norm determinant of the adjoint of
`fderiv ℝ f x`. -/
theorem lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
    (hs : NullMeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) :
    ∫⁻ y, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet := by
  -- Reduce to a measurable subset `t` of full measure: almost every fibre of `s \ t` is null.
  obtain ⟨t, hts, ht, hst⟩ := hs.exists_measurable_subset_ae_eq
  have hfib := ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_hasFDerivWithinAt
    (ae_eq_set.1 hst).2 fun x hx ↦ (hd x hx.1).hasFDerivAt.hasFDerivWithinAt
  rw [setLIntegral_congr hst.symm, ← lintegral_eq_setLIntegral_normDet_adjoint_fderiv ht
    (fun x hx ↦ hd x (hts hx)) fun x hx ↦ hsurj x (hts hx)]
  refine lintegral_congr_ae (hfib.mono fun y hy ↦
    le_antisymm ?_ (measure_mono (inter_subset_inter_left _ hts)))
  calc μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y})
      ≤ μHE[finrank ℝ E - finrank ℝ F] (t ∩ f ⁻¹' {y} ∪ (s \ t) ∩ f ⁻¹' {y}) :=
        measure_mono (by rw [← union_inter_distrib_right, union_sdiff_self]; gcongr; exact
          subset_union_right)
    _ ≤ _ := (measure_union_le _ _).trans (by rw [hy, add_zero])

end MeasureTheory
