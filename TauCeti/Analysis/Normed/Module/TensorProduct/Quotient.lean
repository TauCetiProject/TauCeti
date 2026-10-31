/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion

/-!
# The projective tensor product preserves metric quotient maps

A bounded operator `q` between seminormed spaces is a metric quotient map when `‖q‖ ≤ 1` and
every vector of norm less than `r` is the image of a vector of norm less than `r`; equivalently,
`q` maps each open ball about `0` onto the open ball of the same radius. The quotient projection
`E → E ⧸ S` by a subspace is the basic example (`QuotientAddGroup.norm_lt_iff`).

This file proves that the projective tensor product preserves metric quotient maps, for the
algebraic and for the completed projective tensor products: if `f : E →L[𝕜] E'` and
`g : F →L[𝕜] F'` are metric quotient maps, then so are `ProjectiveTensor.mapL f g` and
`CompletedProjectiveTensor.mapL f g`. In other words, the projective norm of a tensor in
`E' ⊗ F'` is the infimum of the projective norms of its preimages in `E ⊗ F`.

The algebraic statement lifts a finite decomposition `∑ i, x i ⊗ₜ y i` of nearly optimal cost
factor by factor. The completed statement follows from the algebraic one, because extension to
completions preserves metric quotient maps (`ContinuousLinearMap.image_completion_ball`).

## Main results

* `TensorProduct.exists_map_eq_of_projectiveSeminorm_lt`: if `f` and `g` lift vectors of norm
  less than `r` to vectors of norm less than `r`, then `map f g` lifts tensors of projective
  seminorm less than `c` to tensors of projective seminorm less than `c`.
* `TauCeti.ProjectiveTensor.image_mapL_ball`: `mapL f g` of metric quotient maps maps each
  open ball about `0` onto the open ball of the same radius.
* `TauCeti.CompletedProjectiveTensor.image_mapL_ball`: the same for completed projective tensor
  products.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §2.1.
-/

public section

open Metric
open scoped TensorProduct

namespace TensorProduct

variable {𝕜 E E' F F' : Type*} [NormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- If `f` and `g` lift every vector of norm less than `r` to a vector of norm less than `r`,
then every tensor `u` of projective seminorm less than `c` is `map f g v` for some tensor `v` of
projective seminorm less than `c`. -/
theorem exists_map_eq_of_projectiveSeminorm_lt {f : E →ₗ[𝕜] E'} {g : F →ₗ[𝕜] F'}
    (hf : ∀ r, ball (0 : E') r ⊆ f '' ball 0 r) (hg : ∀ r, ball (0 : F') r ⊆ g '' ball 0 r)
    {u : E' ⊗[𝕜] F'} {c : ℝ} (hu : projectiveSeminorm 𝕜 E' F' u < c) :
    ∃ v, map f g v = u ∧ projectiveSeminorm 𝕜 E F v < c := by
  obtain ⟨n, x, y, rfl, hc⟩ := exists_sum_tmul_eq_of_projectiveSeminorm_lt hu
  set S := ∑ i, ‖x i‖ * ‖y i‖
  set T := ∑ i, (‖x i‖ + ‖y i‖ + 1)
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ ↦ by positivity
  -- Lift every factor up to an error `η ≤ 1` in norm, chosen so that `S + η * T < c`.
  set η := min 1 ((c - S) / (T + 1))
  have hη : 0 < η := lt_min one_pos (div_pos (sub_pos.2 hc) (by linarith))
  have hη₁ : η ≤ 1 := min_le_left _ _
  have hx (i : Fin n) : ∃ a, f a = x i ∧ ‖a‖ < ‖x i‖ + η := by
    obtain ⟨a, ha, hfa⟩ := hf _ (mem_ball_zero_iff.2 (lt_add_of_pos_right ‖x i‖ hη))
    exact ⟨a, hfa, mem_ball_zero_iff.1 ha⟩
  have hy (i : Fin n) : ∃ b, g b = y i ∧ ‖b‖ < ‖y i‖ + η := by
    obtain ⟨b, hb, hgb⟩ := hg _ (mem_ball_zero_iff.2 (lt_add_of_pos_right ‖y i‖ hη))
    exact ⟨b, hgb, mem_ball_zero_iff.1 hb⟩
  choose a hfa ha using hx
  choose b hgb hb using hy
  refine ⟨∑ i, a i ⊗ₜ b i, by simp [hfa, hgb], ?_⟩
  calc projectiveSeminorm 𝕜 E F (∑ i, a i ⊗ₜ b i) ≤ ∑ i, ‖a i‖ * ‖b i‖ :=
        projectiveSeminorm_sum_tmul_le _ _ _
    _ ≤ ∑ i, (‖x i‖ * ‖y i‖ + η * (‖x i‖ + ‖y i‖ + 1)) := Finset.sum_le_sum fun i _ ↦ by
        have h := mul_le_mul (ha i).le (hb i).le (norm_nonneg _) (by positivity)
        nlinarith [norm_nonneg (x i), norm_nonneg (y i)]
    _ = S + η * T := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ < c := by
        have h₁ : η * T ≤ (c - S) / (T + 1) * T := by gcongr; exact min_le_right _ _
        have h₂ : (c - S) / (T + 1) * T < c - S := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
        linarith

end TensorProduct

namespace TauCeti

variable {𝕜 E E' F F' : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {f : E →L[𝕜] E'} {g : F →L[𝕜] F'}

namespace ProjectiveTensor

/-- If `f` and `g` lift every vector of norm less than `r` to a vector of norm less than `r`,
then so does `mapL f g` on projective tensor products. -/
theorem ball_subset_image_mapL_ball (hf : ∀ r, ball (0 : E') r ⊆ f '' ball 0 r)
    (hg : ∀ r, ball (0 : F') r ⊆ g '' ball 0 r) (r : ℝ) :
    ball (0 : ProjectiveTensor 𝕜 E' F') r ⊆ mapL f g '' ball 0 r := by
  rintro ⟨u⟩ hu
  rw [mem_ball_zero_iff, norm_def] at hu
  obtain ⟨v, hv, hvr⟩ := TensorProduct.exists_map_eq_of_projectiveSeminorm_lt hf hg hu
  exact ⟨⟨v⟩, by rwa [mem_ball_zero_iff, norm_def], by simp [hv]⟩

/-- The projective tensor product preserves **metric quotient maps**: if `‖f‖ ≤ 1`, `‖g‖ ≤ 1`
and both lift every vector of norm less than `r` to a vector of norm less than `r`, then
`mapL f g` maps each open ball about `0` onto the open ball of the same radius. -/
theorem image_mapL_ball (hf₁ : ‖f‖ ≤ 1) (hg₁ : ‖g‖ ≤ 1)
    (hf : ∀ r, ball (0 : E') r ⊆ f '' ball 0 r) (hg : ∀ r, ball (0 : F') r ⊆ g '' ball 0 r)
    (r : ℝ) : mapL f g '' ball 0 r = ball 0 r := by
  refine subset_antisymm ?_ (ball_subset_image_mapL_ball hf hg r)
  have h : ‖mapL f g‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_one, coe_nnnorm]
    exact (norm_mapL_le f g).trans ((mul_le_of_le_one_left (norm_nonneg g) hf₁).trans hg₁)
  simpa using (((mapL f g).lipschitzWith.weaken h).mapsTo_ball one_ne_zero 0 r).image_subset

end ProjectiveTensor

namespace CompletedProjectiveTensor

/-- If `f` and `g` lift every vector of norm less than `r` to a vector of norm less than `r`,
then so does `mapL f g` on completed projective tensor products. -/
theorem ball_subset_image_mapL_ball (hf : ∀ r, ball (0 : E') r ⊆ f '' ball 0 r)
    (hg : ∀ r, ball (0 : F') r ⊆ g '' ball 0 r) (r : ℝ) :
    ball (0 : CompletedProjectiveTensor 𝕜 E' F') r ⊆ mapL f g '' ball 0 r :=
  mapL_eq_completion f g ▸ (ProjectiveTensor.mapL f g).ball_subset_image_completion_ball
    (ProjectiveTensor.ball_subset_image_mapL_ball hf hg) r

/-- The completed projective tensor product preserves **metric quotient maps**: if `‖f‖ ≤ 1`,
`‖g‖ ≤ 1` and both lift every vector of norm less than `r` to a vector of norm less than `r`,
then `mapL f g` maps each open ball about `0` onto the open ball of the same radius. -/
theorem image_mapL_ball (hf₁ : ‖f‖ ≤ 1) (hg₁ : ‖g‖ ≤ 1)
    (hf : ∀ r, ball (0 : E') r ⊆ f '' ball 0 r) (hg : ∀ r, ball (0 : F') r ⊆ g '' ball 0 r)
    (r : ℝ) : mapL f g '' ball 0 r = ball 0 r :=
  mapL_eq_completion f g ▸ (ProjectiveTensor.mapL f g).image_completion_ball
    ((ProjectiveTensor.norm_mapL_le f g).trans
      ((mul_le_of_le_one_left (norm_nonneg g) hf₁).trans hg₁))
    (ProjectiveTensor.ball_subset_image_mapL_ball hf hg) r

end CompletedProjectiveTensor

end TauCeti
