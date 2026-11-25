/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Measure
public import TauCeti.MeasureTheory.Function.Coarea.Eilenberg
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Hausdorff

/-!
# Counting the points of a set on parallel lines

Let `E` be a real inner product space of finite dimension `n` and `e` a nonzero vector. The lines
parallel to `e` are parametrized by their intersection `y` with the orthogonal hyperplane
`(ℝ ∙ e)ᗮ`, and the line through `y` meets a set `A ⊆ E` in the points `y + t • e` with `t` in the
line section `{t | y + t • e ∈ A}`. Integrating the number of these points over the hyperplane
gives at most a constant times the `(n - 1)`-dimensional Hausdorff measure of `A`:

`∫_{(ℝ ∙ e)ᗮ} #{t | y + t • e ∈ A} dy ≤ |B_{n-1}| · Hⁿ⁻¹(A)`

(`TauCeti.lintegral_encard_lineSection_le`), where `|B_{n-1}|` is the volume of the unit ball of
the hyperplane; for the normalized Hausdorff measure `μHE[n - 1]` the constant is `2ⁿ⁻¹`
(`TauCeti.lintegral_encard_lineSection_le_euclideanHausdorffMeasure`). So if `Hⁿ⁻¹(A)` is finite,
almost every line parallel to `e` meets `A` in finitely many points
(`TauCeti.ae_finite_lineSection`, `TauCeti.ae_finite_lineSection_of_euclideanHausdorffMeasure`).
No measurability of `A` is assumed; for non-measurable integrands `∫⁻` is the lower integral.

This is the projection bound in the proof of Federer's criterion for finite perimeter: applied
to the essential boundary of a set, it bounds the integrated number of essential boundary points
of the line sections. The proof applies Eilenberg's inequality
`LipschitzOnWith.lintegral_hausdorffMeasure_inter_preimage_le` in dimension `0` to Mathlib's
orthogonal projection onto `(ℝ ∙ e)ᗮ`, which is `1`-Lipschitz
(`Submodule.lipschitzWith_orthogonalProjectionOnto`), and whose fiber over `y` is the line through
`y` parallel to `e`; zero-dimensional Hausdorff measure counts points.

## Main results

* `TauCeti.lintegral_encard_lineSection_le`: the integrated number of points of `A` on the lines
  parallel to `e` is at most `|B_{n-1}| · Hⁿ⁻¹(A)`, and
  `TauCeti.lintegral_encard_lineSection_le_euclideanHausdorffMeasure`: at most
  `2ⁿ⁻¹ μHE[n - 1](A)`.
* `TauCeti.ae_finite_lineSection` and `TauCeti.ae_finite_lineSection_of_euclideanHausdorffMeasure`:
  if `Hⁿ⁻¹(A) < ∞`, almost every line parallel to `e` meets `A` in finitely many points.

## References

* H. Federer, *Geometric Measure Theory*, 2.10.25 and 4.5.11.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.4.1 and §5.11.
-/

public section

open MeasureTheory Measure Metric Set Module
open scoped ENNReal NNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace TauCeti

/-- The fiber of `A` over `y` under the orthogonal projection onto `(ℝ ∙ e)ᗮ` has as many points
as the line section `{t | y + t • e ∈ A}`. -/
private theorem hausdorffMeasure_zero_inter_preimage_eq_encard [MeasurableSpace E] [BorelSpace E]
    {e : E} (he : e ≠ 0) (A : Set E) (y : (ℝ ∙ e)ᗮ) :
    μH[0] (A ∩ (ℝ ∙ e)ᗮ.orthogonalProjectionOnto ⁻¹' {y}) =
      ({t : ℝ | (y : E) + t • e ∈ A}.encard : ℝ≥0∞) := by
  have himage : A ∩ (ℝ ∙ e)ᗮ.orthogonalProjectionOnto ⁻¹' {y} =
      (fun t : ℝ => (y : E) + t • e) '' {t : ℝ | (y : E) + t • e ∈ A} := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
      Submodule.orthogonalProjectionOnto_orthogonal_span_singleton_eq_iff, mem_image,
      mem_ofPred_eq]
    constructor
    · rintro ⟨hA, t, rfl⟩
      exact ⟨t, hA, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, t, rfl⟩
  have hinj : Function.Injective fun t : ℝ => (y : E) + t • e :=
    (add_right_injective _).comp (smul_left_injective ℝ he)
  rw [himage, hausdorffMeasure_zero_apply, hinj.encard_image]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The projection bound.** For a nonzero vector `e` of an `n`-dimensional real inner product
space and any set `A`, the number of points of `A` on the line through `y` parallel to `e`,
integrated over the orthogonal hyperplane `(ℝ ∙ e)ᗮ`, is at most the volume of the unit ball of
the hyperplane times the `(n - 1)`-dimensional Hausdorff measure of `A`. -/
theorem lintegral_encard_lineSection_le {e : E} (he : e ≠ 0) (A : Set E)
    (μ : Measure (ℝ ∙ e)ᗮ) [μ.IsAddHaarMeasure] :
    ∫⁻ y, ({t : ℝ | (y : E) + t • e ∈ A}.encard : ℝ≥0∞) ∂μ ≤
      μ (ball (0 : (ℝ ∙ e)ᗮ) 1) * μH[(finrank ℝ E - 1 : ℕ)] A := by
  have h := ((ℝ ∙ e)ᗮ.lipschitzWith_orthogonalProjectionOnto.lipschitzOnWith (s := A))
    |>.lintegral_hausdorffMeasure_inter_preimage_le μ (t := 0)
  simp only [hausdorffMeasure_zero_inter_preimage_eq_encard he, ENNReal.coe_one, one_pow, mul_one,
    add_zero, Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one he] at h
  exact h

/-- **The projection bound for the normalized Hausdorff measure.** For a nonzero vector `e` of an
`n`-dimensional real inner product space and any set `A`, the number of points of `A` on the line
through `y` parallel to `e`, integrated over the orthogonal hyperplane `(ℝ ∙ e)ᗮ`, is at most
`2ⁿ⁻¹ μHE[n - 1](A)`. -/
theorem lintegral_encard_lineSection_le_euclideanHausdorffMeasure {e : E} (he : e ≠ 0)
    (A : Set E) :
    ∫⁻ y : (ℝ ∙ e)ᗮ, ({t : ℝ | (y : E) + t • e ∈ A}.encard : ℝ≥0∞) ≤
      2 ^ (finrank ℝ E - 1) * μHE[finrank ℝ E - 1] A := by
  refine (lintegral_encard_lineSection_le he A volume).trans_eq ?_
  rw [euclideanHausdorffMeasure_eq_smul_hausdorffMeasure, smul_apply, smul_eq_mul,
    volume_ball_eq_of_finrank_eq (F := EuclideanSpace ℝ (Fin (finrank ℝ E - 1)))
      (by simp [Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one he]) 0 0 1,
    ← mul_assoc,
    ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

/-- If `A` has finite `(n - 1)`-dimensional Hausdorff measure in an `n`-dimensional real inner
product space, then almost every line parallel to a nonzero vector `e` meets `A` in finitely many
points. -/
theorem ae_finite_lineSection {e : E} (he : e ≠ 0) (ν : Measure (ℝ ∙ e)ᗮ) [ν.IsAddHaarMeasure]
    {A : Set E} (hA : μH[(finrank ℝ E - 1 : ℕ)] A ≠ ∞) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂ν, {t : ℝ | (y : E) + t • e ∈ A}.Finite := by
  have h := ((ℝ ∙ e)ᗮ.lipschitzWith_orthogonalProjectionOnto.lipschitzOnWith (s := A))
    |>.ae_hausdorffMeasure_inter_preimage_lt_top ν (t := 0)
      (by rwa [add_zero, Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one he])
  filter_upwards [h] with y hy
  rw [hausdorffMeasure_zero_inter_preimage_eq_encard he] at hy
  exact Set.encard_lt_top_iff.mp (by exact_mod_cast hy)

/-- If `A` has finite normalized `(n - 1)`-dimensional Hausdorff measure in an `n`-dimensional
real inner product space, then almost every line parallel to a nonzero vector `e` meets `A` in
finitely many points. -/
theorem ae_finite_lineSection_of_euclideanHausdorffMeasure {e : E} (he : e ≠ 0)
    (ν : Measure (ℝ ∙ e)ᗮ) [ν.IsAddHaarMeasure] {A : Set E}
    (hA : μHE[finrank ℝ E - 1] A ≠ ∞) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂ν, {t : ℝ | (y : E) + t • e ∈ A}.Finite :=
  ae_finite_lineSection he ν (euclideanHausdorffMeasure_lt_top_iff.1 (lt_top_iff_ne_top.2 hA)).ne

end TauCeti
