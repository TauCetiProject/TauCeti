/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TensorProduct.Series

/-!
# The projective tensor product preserves metric quotient maps

A bounded operator `f : E →L[𝕜] E'` is a *metric quotient map* when it maps every open ball
`ball 0 r` of `E` onto the open ball `ball 0 r` of `E'`. Equivalently, `‖f x‖ ≤ ‖x‖` for every
`x`, and every `y : E'` has preimages `x` with `‖x‖` arbitrarily close to `‖y‖`, so that the norm
of `E'` is the quotient norm of `E` along `f`. The basic example is the projection
`Submodule.mkQL S` of `E` onto its normed quotient `E ⧸ S` by a submodule
(`Submodule.image_mkQL_ball`).

This file proves that if `f : E →L[𝕜] E'` and `g : F →L[𝕜] F'` are metric quotient maps, then
so is the induced operator `x ⊗ₜ y ↦ f x ⊗ₜ g y`, both between the algebraic projective tensor
products `ProjectiveTensor 𝕜 E F → ProjectiveTensor 𝕜 E' F'` and between the completed projective
tensor products `E ⊗̂π F → E' ⊗̂π F'`. No factor is assumed complete. The lifting half holds
without the norm bound: if every ball of `E'` and of `F'` is covered by the image of the ball of
the same radius, the same holds for the induced operators.

The proof lifts the factors of a decomposition of a tensor of small cost. For an algebraic
tensor this is a finite decomposition; for a completed tensor it is the series representation
`TauCeti.CompletedProjectiveTensor.exists_hasSum_tmul_of_norm_lt`, whose lifted series converges
absolutely in the complete domain.

## Main results

* `TauCeti.ProjectiveTensor.ball_subset_image_mapL_ball` and
  `TauCeti.CompletedProjectiveTensor.ball_subset_image_mapL_ball`: lifting of balls through the
  induced operators.
* `TauCeti.ProjectiveTensor.image_mapL_ball` and
  `TauCeti.CompletedProjectiveTensor.image_mapL_ball`: the projective tensor product of metric
  quotient maps is a metric quotient map.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002,
  Proposition 2.5.
-/

public section

open scoped TensorProduct

open Metric

namespace TauCeti

variable {𝕜 E E' F F' : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {f : E →L[𝕜] E'} {g : F →L[𝕜] F'}

/-- If `f` and `g` lift every ball to the ball of the same radius, a pair `(x', y')` lifts to a
pair `(x, y)` with `‖x‖ * ‖y‖` exceeding `‖x'‖ * ‖y'‖` by less than any prescribed `η > 0`. -/
private theorem exists_lift_pair (hf : ∀ r, ball (0 : E') r ⊆ f '' ball 0 r)
    (hg : ∀ r, ball (0 : F') r ⊆ g '' ball 0 r) (x' : E') (y' : F') {η : ℝ} (hη : 0 < η) :
    ∃ x y, f x = x' ∧ g y = y' ∧ ‖x‖ * ‖y‖ < ‖x'‖ * ‖y'‖ + η := by
  have hcont : ContinuousAt (fun δ : ℝ ↦ (‖x'‖ + δ) * (‖y'‖ + δ)) 0 := by fun_prop
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (‖x'‖ + δ) * (‖y'‖ + δ) < ‖x'‖ * ‖y'‖ + η :=
    nhdsWithin_le_nhds <| hcont.eventually (gt_mem_nhds (by simpa using hη))
  obtain ⟨δ, hδ, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  obtain ⟨x, hx, rfl⟩ := hf _ (mem_ball_zero_iff.2 (lt_add_of_pos_right ‖x'‖ hδpos))
  obtain ⟨y, hy, rfl⟩ := hg _ (mem_ball_zero_iff.2 (lt_add_of_pos_right ‖y'‖ hδpos))
  refine ⟨x, y, rfl, rfl, lt_of_le_of_lt ?_ hδ⟩
  exact mul_le_mul (mem_ball_zero_iff.1 hx).le (mem_ball_zero_iff.1 hy).le (norm_nonneg y)
    (by positivity)

/-- A bounded operator mapping each ball `ball 0 r` into the ball of the same radius has norm at
most one. -/
private theorem norm_le_one_of_image_ball_subset {f : E →L[𝕜] E'}
    (hf : ∀ r, f '' ball 0 r ⊆ ball 0 r) : ‖f‖ ≤ 1 :=
  f.opNorm_le_bound zero_le_one fun x ↦ by
    rw [one_mul]
    exact le_of_forall_gt fun c hc ↦ mem_ball_zero_iff.1 (hf c ⟨x, mem_ball_zero_iff.2 hc, rfl⟩)

namespace ProjectiveTensor

/-- **Lifting through projective tensor products.** If `f` and `g` lift every ball to the ball
of the same radius, then so does the induced operator `mapL f g` on projective tensor products:
every tensor of norm less than `r` is the image of a tensor of norm less than `r`. -/
theorem ball_subset_image_mapL_ball (hf : ∀ r, ball (0 : E') r ⊆ f '' ball 0 r)
    (hg : ∀ r, ball (0 : F') r ⊆ g '' ball 0 r) (r : ℝ) :
    ball (0 : ProjectiveTensor 𝕜 E' F') r ⊆ mapL f g '' ball 0 r := by
  intro u' hu'
  rw [mem_ball_zero_iff, norm_def] at hu'
  obtain ⟨n, x', y', hsum, hcost⟩ := TensorProduct.exists_sum_tmul_eq_of_projectiveSeminorm_lt hu'
  set c := ∑ i, ‖x' i‖ * ‖y' i‖
  set η := (r - c) / (n + 1) with hη_def
  have hη : 0 < η := div_pos (sub_pos.2 hcost) (by positivity)
  choose x y hx hy hxy using fun i ↦ exists_lift_pair hf hg (x' i) (y' i) hη
  refine ⟨⟨∑ i, x i ⊗ₜ y i⟩, ?_, ?_⟩
  · have hnη : (n : ℝ) * η < r - c := by
      rw [hη_def, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [sub_pos.2 hcost]
    rw [mem_ball_zero_iff, norm_def]
    calc TensorProduct.projectiveSeminorm 𝕜 E F (∑ i, x i ⊗ₜ y i)
        ≤ ∑ i, ‖x i‖ * ‖y i‖ := TensorProduct.projectiveSeminorm_sum_tmul_le _ _ _
      _ ≤ ∑ i, (‖x' i‖ * ‖y' i‖ + η) := Finset.sum_le_sum fun i _ ↦ (hxy i).le
      _ = c + n * η := by simp [c, Finset.sum_add_distrib]
      _ < r := by linarith
  · ext
    simp [mapL_apply, hx, hy, hsum]

/-- **The projective tensor product preserves metric quotient maps.** If `f` and `g` map every
ball `ball 0 r` onto the ball of the same radius, then so does the induced operator `mapL f g` on
projective tensor products. -/
theorem image_mapL_ball (hf : ∀ r, f '' ball (0 : E) r = ball 0 r)
    (hg : ∀ r, g '' ball (0 : F) r = ball 0 r) (r : ℝ) :
    mapL f g '' ball (0 : ProjectiveTensor 𝕜 E F) r = ball 0 r := by
  refine subset_antisymm ?_
    (ball_subset_image_mapL_ball (fun r ↦ (hf r).ge) (fun r ↦ (hg r).ge) r)
  have hfg : ‖mapL f g‖ ≤ 1 := (norm_mapL_le f g).trans <| by
    simpa using mul_le_mul (norm_le_one_of_image_ball_subset fun r ↦ (hf r).le)
      (norm_le_one_of_image_ball_subset fun r ↦ (hg r).le) (norm_nonneg g) zero_le_one
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_ball_zero_iff] at hu ⊢
  exact ((mapL f g).le_of_opNorm_le hfg u).trans_lt (by rwa [one_mul])

end ProjectiveTensor

namespace CompletedProjectiveTensor

/-- **Lifting through completed projective tensor products.** If `f` and `g` lift every ball to
the ball of the same radius, then so does the induced operator `mapL f g` on completed projective
tensor products: every completed tensor of norm less than `r` is the image of a completed tensor
of norm less than `r`. -/
theorem ball_subset_image_mapL_ball (hf : ∀ r, ball (0 : E') r ⊆ f '' ball 0 r)
    (hg : ∀ r, ball (0 : F') r ⊆ g '' ball 0 r) (r : ℝ) :
    ball (0 : CompletedProjectiveTensor 𝕜 E' F') r ⊆ mapL f g '' ball 0 r := by
  intro u' hu'
  rw [mem_ball_zero_iff] at hu'
  -- Write `u'` as a series of pure tensors of cost `c < r`.
  obtain ⟨x', y', hsum, hs, hc⟩ := exists_hasSum_tmul_of_norm_lt u' hu'
  set c := ∑' n, ‖x' n‖ * ‖y' n‖
  have hpos : 0 < (r - c) / 2 := by linarith
  -- Lift the `n`-th pure tensor with an error of `(r - c) / 2 / 2 / 2 ^ n` in its cost.
  choose x y hx hy hxy using fun n : ℕ ↦
    exists_lift_pair hf hg (x' n) (y' n) (η := (r - c) / 2 / 2 / 2 ^ n) (by positivity)
  have hb : HasSum (fun n ↦ ‖x' n‖ * ‖y' n‖ + (r - c) / 2 / 2 / 2 ^ n) (c + (r - c) / 2) :=
    hs.hasSum.add (hasSum_geometric_two' _)
  have ha : Summable fun n ↦ ‖x n‖ * ‖y n‖ :=
    .of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ (hxy n).le) hb.summable
  -- The lifted series converges absolutely in the complete space `E ⊗̂π F`.
  have hz : Summable fun n ↦
      ((⟨x n ⊗ₜ y n⟩ : ProjectiveTensor 𝕜 E F) : CompletedProjectiveTensor 𝕜 E F) :=
    .of_norm_bounded ha fun n ↦ norm_coe_tmul_le (x n) (y n)
  refine ⟨_, ?_, (hz.hasSum.map (mapL f g) (mapL f g).continuous).unique ?_⟩
  · rw [mem_ball_zero_iff]
    calc _ ≤ ∑' n, ‖x n‖ * ‖y n‖ := norm_le_tsum_of_hasSum_tmul hz.hasSum ha
      _ ≤ c + (r - c) / 2 := hasSum_le (fun n ↦ (hxy n).le) ha.hasSum hb
      _ < r := by linarith
  · simpa [Function.comp_def, hx, hy] using hsum

/-- **The completed projective tensor product preserves metric quotient maps.** If `f` and `g`
map every ball `ball 0 r` onto the ball of the same radius, then so does the induced operator
`mapL f g` on completed projective tensor products. -/
theorem image_mapL_ball (hf : ∀ r, f '' ball (0 : E) r = ball 0 r)
    (hg : ∀ r, g '' ball (0 : F) r = ball 0 r) (r : ℝ) :
    mapL f g '' ball (0 : CompletedProjectiveTensor 𝕜 E F) r = ball 0 r := by
  refine subset_antisymm ?_
    (ball_subset_image_mapL_ball (fun r ↦ (hf r).ge) (fun r ↦ (hg r).ge) r)
  have hfg : ‖mapL f g‖ ≤ 1 := (norm_mapL_le f g).trans <| by
    simpa using mul_le_mul (norm_le_one_of_image_ball_subset fun r ↦ (hf r).le)
      (norm_le_one_of_image_ball_subset fun r ↦ (hg r).le) (norm_nonneg g) zero_le_one
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_ball_zero_iff] at hu ⊢
  exact ((mapL f g).le_of_opNorm_le hfg u).trans_lt (by rwa [one_mul])

end CompletedProjectiveTensor

end TauCeti
