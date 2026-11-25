/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Topology of the annulus

For `0 ≤ r₁ < r₂`, this file describes the open annulus `ball z₀ r₂ \ closedBall z₀ r₁` and the
closed annulus `closedBall z₀ r₂ \ ball z₀ r₁` in `ℂ`. For the centre `z₀ = 0` they are described
through the norm and through polar coordinates `(r, θ) ↦ r e^{iθ}`; the closure and the frontier
are computed for an arbitrary centre.

## Main results

* `TauCeti.Complex.isPreconnected_ball_diff_closedBall`: the open annulus centred at the origin is
  connected.
* `TauCeti.Complex.closure_ball_diff_closedBall`: the closure of the open annulus is the closed
  annulus.
* `TauCeti.Complex.sphere_subset_closure_ball_diff_closedBall`: that closure contains every circle
  with radius in `[r₁, r₂]`.
* `TauCeti.Complex.frontier_ball_diff_closedBall_subset`: the frontier of the open annulus lies on
  the two boundary circles.
-/

public section

open Complex Set Metric

namespace TauCeti.Complex

/-- The open annulus `ball 0 r₂ \ closedBall 0 r₁` is the set of points with norm in
`Ioo r₁ r₂`. -/
theorem ball_diff_closedBall_eq_preimage (r₁ r₂ : ℝ) :
    ball (0 : ℂ) r₂ \ closedBall 0 r₁ = norm ⁻¹' Ioo r₁ r₂ := by
  ext z
  simp only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, mem_preimage,
    mem_Ioo]
  exact and_comm

/-- The closed annulus `closedBall 0 r₂ \ ball 0 r₁` is the set of points with norm in
`Icc r₁ r₂`. -/
theorem closedBall_diff_ball_eq_preimage (r₁ r₂ : ℝ) :
    closedBall (0 : ℂ) r₂ \ ball 0 r₁ = norm ⁻¹' Icc r₁ r₂ := by
  ext z
  simp only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_lt, mem_preimage,
    mem_Icc]
  exact and_comm

/-- Polar coordinates `(r, θ) ↦ r e^{iθ}` map `S × ℝ` onto the set of points with norm in `S`,
for any set `S` of nonnegative radii. -/
theorem image_polar_prod_univ {S : Set ℝ} (hS : S ⊆ Ici 0) :
    (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) '' (S ×ˢ univ) = norm ⁻¹' S := by
  ext z
  constructor
  · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
    rw [mem_preimage, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hS hr)]
    exact hr
  · intro hz
    exact ⟨(‖z‖, arg z), ⟨hz, mem_univ _⟩, norm_mul_exp_arg_mul_I z⟩

/-- The open annulus is connected. -/
theorem isPreconnected_ball_diff_closedBall {r₁ : ℝ} (hr₁ : 0 ≤ r₁) (r₂ : ℝ) :
    IsPreconnected (ball (0 : ℂ) r₂ \ closedBall 0 r₁) := by
  rw [ball_diff_closedBall_eq_preimage,
    ← image_polar_prod_univ (S := Ioo r₁ r₂) fun r hr => hr₁.trans hr.1.le]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ (by fun_prop)

/-- The closure of the open annulus centred at the origin is the closed annulus: the case
`z₀ = 0` of `closure_ball_diff_closedBall`, by polar coordinates. -/
private theorem closure_ball_zero_diff_closedBall_zero {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    closure (ball (0 : ℂ) r₂ \ closedBall 0 r₁) = closedBall 0 r₂ \ ball 0 r₁ := by
  rw [ball_diff_closedBall_eq_preimage, closedBall_diff_ball_eq_preimage]
  refine Subset.antisymm
    (closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage continuous_norm)) ?_
  rw [← image_polar_prod_univ (S := Icc r₁ r₂) fun r hr => hr₁.trans hr.1,
    ← image_polar_prod_univ (S := Ioo r₁ r₂) fun r hr => hr₁.trans hr.1.le]
  have hcl : closure (Ioo r₁ r₂ ×ˢ (univ : Set ℝ)) = Icc r₁ r₂ ×ˢ univ := by
    rw [closure_prod_eq, closure_Ioo h.ne, closure_univ]
  rw [← hcl]
  exact image_closure_subset_closure_image (by fun_prop)

/-- The closure of the open annulus `r₁ < ‖z - z₀‖ < r₂` is the closed annulus
`r₁ ≤ ‖z - z₀‖ ≤ r₂`, for `0 ≤ r₁ < r₂` and any centre `z₀`. -/
theorem closure_ball_diff_closedBall {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    closure (ball z₀ r₂ \ closedBall z₀ r₁) = closedBall z₀ r₂ \ ball z₀ r₁ := by
  have hopen : ball z₀ r₂ \ closedBall z₀ r₁ =
      Homeomorph.subRight z₀ ⁻¹' (ball 0 r₂ \ closedBall 0 r₁) := by
    ext z
    rw [mem_preimage, Homeomorph.coe_subRight, mem_sdiff, mem_sdiff, mem_ball_iff_norm,
      mem_closedBall_iff_norm, mem_ball_zero_iff, mem_closedBall_zero_iff]
  have hclosed : closedBall z₀ r₂ \ ball z₀ r₁ =
      Homeomorph.subRight z₀ ⁻¹' (closedBall 0 r₂ \ ball 0 r₁) := by
    ext z
    rw [mem_preimage, Homeomorph.coe_subRight, mem_sdiff, mem_sdiff, mem_ball_iff_norm,
      mem_closedBall_iff_norm, mem_ball_zero_iff, mem_closedBall_zero_iff]
  rw [hopen, ← Homeomorph.preimage_closure, closure_ball_zero_diff_closedBall_zero hr₁ h, hclosed]

/-- For `0 ≤ r₁ < r₂`, every circle about `z₀` with radius in `[r₁, r₂]` lies in the closure of
the open annulus `r₁ < ‖z - z₀‖ < r₂`. -/
theorem sphere_subset_closure_ball_diff_closedBall {z₀ : ℂ} {r r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (h : r₁ < r₂) (h₁ : r₁ ≤ r) (h₂ : r ≤ r₂) :
    sphere z₀ r ⊆ closure (ball z₀ r₂ \ closedBall z₀ r₁) := by
  intro w hw
  rw [mem_sphere_iff_norm] at hw
  rw [closure_ball_diff_closedBall hr₁ h, mem_sdiff, mem_closedBall_iff_norm, mem_ball_iff_norm,
    not_lt, hw]
  exact ⟨h₂, h₁⟩

/-- The frontier of the open annulus lies on the two boundary circles. -/
theorem frontier_ball_diff_closedBall_subset {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    frontier (ball z₀ r₂ \ closedBall z₀ r₁) ⊆ sphere z₀ r₁ ∪ sphere z₀ r₂ := by
  rw [(isOpen_ball.sdiff isClosed_closedBall).frontier_eq, closure_ball_diff_closedBall hr₁ h]
  intro z hz
  simp only [mem_sdiff, mem_ball_iff_norm, mem_closedBall_iff_norm, not_lt, not_and, not_le]
    at hz
  simp only [mem_union, mem_sphere_iff_norm]
  rcases hz.1.1.lt_or_eq with h₂ | h₂
  · exact Or.inl (le_antisymm (hz.2 h₂) hz.1.2)
  · exact Or.inr h₂

end TauCeti.Complex
