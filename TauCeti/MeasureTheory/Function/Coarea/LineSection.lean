/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.MeasureTheory.Function.Coarea.Eilenberg
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine
import TauCeti.MeasureTheory.Measure.Hausdorff

/-!
# Counting the points of a set on parallel lines

Let `E` be a real inner product space of finite dimension `n` and `e` a unit vector. The lines
parallel to `e` are parametrized by their intersection `y` with the orthogonal hyperplane
`(ℝ ∙ e)ᗮ`, and the line through `y` meets a set `A ⊆ E` in the points `y + t • e` with `t` in the
line section `{t | y + t • e ∈ A}`. Integrating the number of these points over the hyperplane
gives at most a constant times the `(n - 1)`-dimensional Hausdorff measure of `A`:

`∫_{(ℝ ∙ e)ᗮ} #{t | y + t • e ∈ A} dy ≤ |B_{n-1}| · Hⁿ⁻¹(A)`

(`TauCeti.lintegral_encard_lineSection_le`), where `|B_{n-1}|` is the volume of the unit ball of
the hyperplane. So if `Hⁿ⁻¹(A)` is finite, almost every line parallel to `e` meets `A` in finitely
many points (`TauCeti.ae_finite_lineSection`). No measurability of `A` is assumed; for
non-measurable integrands `∫⁻` is the lower integral.

This is the projection bound in the proof of Federer's criterion for finite perimeter: applied
to the essential boundary of a set, it bounds the integrated number of essential boundary points
of the line sections. The proof applies Eilenberg's inequality
`LipschitzOnWith.lintegral_hausdorffMeasure_inter_preimage_le` in dimension `0` to the orthogonal
projection onto `(ℝ ∙ e)ᗮ`, which is `1`-Lipschitz, and whose fiber over `y` is the line through
`y` parallel to `e`; zero-dimensional Hausdorff measure counts points.

## Main results

* `TauCeti.lipschitzWith_orthogonalLineEquiv_symm_fst`: the transverse coordinate of orthogonal
  line coordinates, the orthogonal projection onto `(ℝ ∙ e)ᗮ`, is `1`-Lipschitz.
* `TauCeti.lintegral_encard_lineSection_le`: the integrated number of points of `A` on the lines
  parallel to `e` is at most `|B_{n-1}| · Hⁿ⁻¹(A)`.
* `TauCeti.ae_finite_lineSection`: if `Hⁿ⁻¹(A) < ∞`, almost every line parallel to `e` meets `A`
  in finitely many points.

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

private theorem orthogonalLineEquiv_symm_add_smul (e : E) (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ)
    (t : ℝ) : (orthogonalLineEquiv e he).symm ((y : E) + t • e) = (y, t) := by
  rw [← orthogonalLineEquiv_apply e he, ContinuousLinearEquiv.symm_apply_apply]

/-- The transverse coordinate `x ↦ x - ⟪e, x⟫ • e` of orthogonal line coordinates, the orthogonal
projection onto `(ℝ ∙ e)ᗮ`, is `1`-Lipschitz. -/
theorem lipschitzWith_orthogonalLineEquiv_symm_fst (e : E) (he : ‖e‖ = 1) :
    LipschitzWith 1 fun x : E => ((orthogonalLineEquiv e he).symm x).1 := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
  obtain ⟨⟨y', t'⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x'
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
    NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub, Prod.mk_sub_mk,
    orthogonalLineEquiv_apply]
  have hsq := norm_add_smul_sq e he (y - y') (t - t')
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by rw [hsq]; nlinarith [sq_nonneg (t - t')])

/-- The fiber of `A` over `y` under the orthogonal projection onto `(ℝ ∙ e)ᗮ` has as many points
as the line section `{t | y + t • e ∈ A}`. -/
private theorem hausdorffMeasure_zero_inter_preimage_eq_encard [MeasurableSpace E] [BorelSpace E]
    (e : E) (he : ‖e‖ = 1) (A : Set E) (y : (ℝ ∙ e)ᗮ) :
    μH[0] (A ∩ (fun x : E => ((orthogonalLineEquiv e he).symm x).1) ⁻¹' {y}) =
      ({t : ℝ | (y : E) + t • e ∈ A}.encard : ℝ≥0∞) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have himage : A ∩ (fun x : E => ((orthogonalLineEquiv e he).symm x).1) ⁻¹' {y} =
      (fun t : ℝ => (y : E) + t • e) '' {t : ℝ | (y : E) + t • e ∈ A} := by
    ext x
    obtain ⟨⟨z, s⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, orthogonalLineEquiv_apply,
      orthogonalLineEquiv_symm_add_smul, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨hA, rfl⟩
      exact ⟨s, hA, rfl⟩
    · rintro ⟨r, hr, hrx⟩
      have h := congrArg (fun x => ((orthogonalLineEquiv e he).symm x).1) hrx
      simp only [orthogonalLineEquiv_symm_add_smul] at h
      subst h
      exact ⟨hrx ▸ hr, rfl⟩
  have hinj : Function.Injective fun t : ℝ => (y : E) + t • e :=
    (add_right_injective _).comp (smul_left_injective ℝ he0)
  rw [himage, hausdorffMeasure_zero_eq_count, ← hinj.encard_image]
  rcases ((fun t : ℝ => (y : E) + t • e) '' {t : ℝ | (y : E) + t • e ∈ A}).finite_or_infinite
    with hfin | hinf
  · exact count_apply hfin.measurableSet
  · rw [count_apply_infinite hinf, hinf.encard_eq]
    simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem finrank_orthogonal_span_singleton_eq (e : E) (he : ‖e‖ = 1) :
    finrank ℝ (ℝ ∙ e)ᗮ = finrank ℝ E - 1 := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have h := (ℝ ∙ e).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he0] at h
  omega

/-- **The projection bound.** For a unit vector `e` of an `n`-dimensional real inner product
space and any set `A`, the number of points of `A` on the line through `y` parallel to `e`,
integrated over the orthogonal hyperplane `(ℝ ∙ e)ᗮ`, is at most the volume of the unit ball of
the hyperplane times the `(n - 1)`-dimensional Hausdorff measure of `A`. -/
theorem lintegral_encard_lineSection_le (e : E) (he : ‖e‖ = 1) (A : Set E) :
    ∫⁻ y : (ℝ ∙ e)ᗮ, ({t : ℝ | (y : E) + t • e ∈ A}.encard : ℝ≥0∞) ≤
      volume (ball (0 : (ℝ ∙ e)ᗮ) 1) * μH[(finrank ℝ E - 1 : ℕ)] A := by
  have h := ((lipschitzWith_orthogonalLineEquiv_symm_fst e he).lipschitzOnWith (s := A))
    |>.lintegral_hausdorffMeasure_inter_preimage_le volume (t := 0)
  simp only [hausdorffMeasure_zero_inter_preimage_eq_encard, ENNReal.coe_one, one_pow, mul_one,
    add_zero, finrank_orthogonal_span_singleton_eq e he] at h
  exact h

/-- If `A` has finite `(n - 1)`-dimensional Hausdorff measure in an `n`-dimensional real inner
product space, then almost every line parallel to a unit vector `e` meets `A` in finitely many
points. -/
theorem ae_finite_lineSection (e : E) (he : ‖e‖ = 1) {A : Set E}
    (hA : μH[(finrank ℝ E - 1 : ℕ)] A ≠ ∞) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ, {t : ℝ | (y : E) + t • e ∈ A}.Finite := by
  have h := ((lipschitzWith_orthogonalLineEquiv_symm_fst e he).lipschitzOnWith (s := A))
    |>.ae_hausdorffMeasure_inter_preimage_lt_top volume (t := 0)
      (by rwa [add_zero, finrank_orthogonal_span_singleton_eq e he])
  filter_upwards [h] with y hy
  rw [hausdorffMeasure_zero_inter_preimage_eq_encard] at hy
  exact Set.encard_lt_top_iff.mp (by exact_mod_cast hy)

end TauCeti
