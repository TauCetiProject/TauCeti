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
# Topology of the annulus centred at the origin

For `0 ≤ r₁ < r₂`, this file describes the open annulus `ball 0 r₂ \ closedBall 0 r₁` and the
closed annulus `closedBall 0 r₂ \ ball 0 r₁` in `ℂ` through the norm and through polar
coordinates `(r, θ) ↦ r e^{iθ}`.

## Main results

* `TauCeti.Complex.isPreconnected_ball_diff_closedBall`: the open annulus is connected.
* `TauCeti.Complex.closure_ball_diff_closedBall`: its closure is the closed annulus.
* `TauCeti.Complex.frontier_ball_diff_closedBall_subset`: its frontier lies on the two boundary
  circles.
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

/-- The closure of the open annulus is the closed annulus. -/
theorem closure_ball_diff_closedBall {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
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

/-- The frontier of the open annulus lies on the two boundary circles. -/
theorem frontier_ball_diff_closedBall_subset {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    frontier (ball (0 : ℂ) r₂ \ closedBall 0 r₁) ⊆ sphere 0 r₁ ∪ sphere 0 r₂ := by
  rw [(isOpen_ball.sdiff isClosed_closedBall).frontier_eq, closure_ball_diff_closedBall hr₁ h]
  intro z hz
  simp only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_lt, not_and, not_le]
    at hz
  simp only [mem_union, mem_sphere_zero_iff_norm]
  rcases hz.1.1.lt_or_eq with h₂ | h₂
  · exact Or.inl (le_antisymm (hz.2 h₂) hz.1.2)
  · exact Or.inr h₂

end TauCeti.Complex
