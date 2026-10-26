/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The hemispheres of `S²` as graphs over the unit disc

The closed upper and lower hemispheres of the unit sphere `S² ⊆ ℝ³` are the graphs of
`u ↦ ±√(1 - ‖u‖²)` over the closed unit disc of `ℂ`, identified with the plane `x₂ = 0` by
`u ↦ (Re u, Im u)`. For a sign `c` (that is, `c ^ 2 = 1`), `TauCeti.hemisphereGraph` sends a point
`u` of the disc to `(Re u, Im u, c √(1 - ‖u‖²))`. The two hemispheres cover the sphere, agree on
the equator `‖u‖ = 1`, and meet only there.

This is the coordinate form, over the unit disc of `ℂ`, of the inverse of
`TauCeti.hemisphereHomeomorph`, which parametrizes the closed hemisphere around any unit vector
`p` of a real inner product space by the closed unit ball of `(ℝ ∙ p)ᗮ`. The disc of `ℂ` is the one
used by `D² × S¹` solid tori, so these graphs are the solid tori `S¹ × D²₊` and `S¹ × D²₋` of
`S¹ × S²`.

## Main definitions

* `TauCeti.hemisphereGraphPoint c u`: the point `(Re u, Im u, c √(1 - ‖u‖²))` of `ℝ³`.
* `TauCeti.hemisphereGraph hc`: the hemisphere of sign `c` of `S²`, as a map from the closed unit
  disc of `ℂ`.

## Main results

* `TauCeti.eq_of_hemisphereGraph_eq`: a point of a hemisphere determines the point of the disc.
* `TauCeti.hemisphereGraph_eq_of_norm_eq_one`: the hemispheres agree on the equator.
* `TauCeti.norm_eq_one_of_hemisphereGraph_eq`: hemispheres of opposite signs meet only over the
  boundary of the disc.
* `TauCeti.exists_hemisphereGraph_eq`: every point of `S²` lies on the hemisphere of the sign of
  its last coordinate.
-/

public section

noncomputable section

open Metric

namespace TauCeti

/-- The point `(Re u, Im u, c √(1 - ‖u‖²))` of `ℝ³`; for `c = 1` and `c = -1` and `u` in the
closed unit disc this is the upper and the lower hemisphere of `S²`. -/
def hemisphereGraphPoint (c : ℝ) (u : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[u.re, u.im, c * √(1 - ‖u‖ ^ 2)]

/-- The first coordinate of `TauCeti.hemisphereGraphPoint c u` is the real part of `u`. -/
@[simp]
theorem hemisphereGraphPoint_apply_zero (c : ℝ) (u : ℂ) : hemisphereGraphPoint c u 0 = u.re :=
  (rfl)

/-- The second coordinate of `TauCeti.hemisphereGraphPoint c u` is the imaginary part of `u`. -/
@[simp]
theorem hemisphereGraphPoint_apply_one (c : ℝ) (u : ℂ) : hemisphereGraphPoint c u 1 = u.im :=
  (rfl)

/-- The last coordinate of `TauCeti.hemisphereGraphPoint c u` is `c √(1 - ‖u‖²)`. -/
@[simp]
theorem hemisphereGraphPoint_apply_two (c : ℝ) (u : ℂ) :
    hemisphereGraphPoint c u 2 = c * √(1 - ‖u‖ ^ 2) :=
  (rfl)

/-- For a sign `c`, the points `TauCeti.hemisphereGraphPoint c u` over the closed unit disc lie on
the unit sphere. -/
theorem hemisphereGraphPoint_mem_sphere {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : ℂ) 1) :
    hemisphereGraphPoint c u ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hu : ‖(u : ℂ)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp u.2)
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, hemisphereGraphPoint_apply_zero,
    hemisphereGraphPoint_apply_one, hemisphereGraphPoint_apply_two, mul_pow, hc, one_mul,
    Real.sq_sqrt (sub_nonneg.mpr hu), Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The hemisphere of `S²` of sign `c`, the graph of `u ↦ c √(1 - ‖u‖²)` over the closed unit
disc of `ℂ`. -/
def hemisphereGraph {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : ℂ) 1) :
    sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨hemisphereGraphPoint c u, hemisphereGraphPoint_mem_sphere hc u⟩

/-- `TauCeti.hemisphereGraph hc u` is the point `TauCeti.hemisphereGraphPoint c u`. -/
@[simp]
theorem coe_hemisphereGraph_apply {c : ℝ} (hc : c ^ 2 = 1) (u : closedBall (0 : ℂ) 1) :
    (hemisphereGraph hc u : EuclideanSpace ℝ (Fin 3)) = hemisphereGraphPoint c u :=
  (rfl)

/-- The hemisphere graphs are continuous. -/
@[fun_prop]
theorem continuous_hemisphereGraph {c : ℝ} (hc : c ^ 2 = 1) : Continuous (hemisphereGraph hc) := by
  refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp ?_) _
  fun_prop

/-- The first two coordinates of a point of a hemisphere recover the point of the disc, whatever
the signs of the two hemispheres. -/
theorem eq_of_hemisphereGraph_eq {c c' : ℝ} {hc : c ^ 2 = 1} {hc' : c' ^ 2 = 1}
    {u v : closedBall (0 : ℂ) 1} (h : hemisphereGraph hc u = hemisphereGraph hc' v) : u = v := by
  have hi (i : Fin 3) := congrArg
    (fun x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (x : EuclideanSpace ℝ (Fin 3)) i) h
  refine Subtype.ext (Complex.ext ?_ ?_)
  · simpa using hi 0
  · simpa using hi 1

/-- The hemispheres of any two signs agree on the equator. -/
theorem hemisphereGraph_eq_of_norm_eq_one {c c' : ℝ} (hc : c ^ 2 = 1) (hc' : c' ^ 2 = 1)
    {u : closedBall (0 : ℂ) 1} (hu : ‖(u : ℂ)‖ = 1) :
    hemisphereGraph hc u = hemisphereGraph hc' u := by
  ext i
  fin_cases i <;> simp [hu]

/-- Hemispheres of opposite signs meet only over the boundary of the disc. -/
theorem norm_eq_one_of_hemisphereGraph_eq {c c' : ℝ} {hc : c ^ 2 = 1} {hc' : c' ^ 2 = 1}
    (hcc' : c ≠ c') {u v : closedBall (0 : ℂ) 1}
    (h : hemisphereGraph hc u = hemisphereGraph hc' v) : ‖(v : ℂ)‖ = 1 := by
  have huv := eq_of_hemisphereGraph_eq h
  subst huv
  have h2 :=
    congrArg (fun x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (x : EuclideanSpace ℝ (Fin 3)) 2) h
  simp only [coe_hemisphereGraph_apply, hemisphereGraphPoint_apply_two] at h2
  have hs : √(1 - ‖(u : ℂ)‖ ^ 2) = 0 :=
    (mul_eq_zero.mp (by linarith : (c - c') * √(1 - ‖(u : ℂ)‖ ^ 2) = 0)).resolve_left
      (sub_ne_zero.mpr hcc')
  rw [Real.sqrt_eq_zero', sub_nonpos] at hs
  exact le_antisymm (mem_closedBall_zero_iff.mp u.2) ((one_le_sq_iff₀ (norm_nonneg _)).mp hs)

/-- Every point of `S²` whose last coordinate `x₂` has `0 ≤ c x₂` lies on the hemisphere of sign
`c`, over the point `x₀ + i x₁` of the disc. -/
theorem exists_hemisphereGraph_eq {c : ℝ} (hc : c ^ 2 = 1)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hx : 0 ≤ c * (x : EuclideanSpace ℝ (Fin 3)) 2) : ∃ u, hemisphereGraph hc u = x := by
  have hx2 : (x : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 + (x : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 +
      (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 = 1 := by
    rw [← Fin.sum_univ_three (fun i ↦ (x : EuclideanSpace ℝ (Fin 3)) i ^ 2),
      ← EuclideanSpace.real_norm_sq_eq, norm_eq_of_mem_sphere x, one_pow]
  have hnorm : ‖(⟨(x : EuclideanSpace ℝ (Fin 3)) 0, (x : EuclideanSpace ℝ (Fin 3)) 1⟩ : ℂ)‖ ^ 2 =
      1 - (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]
    linarith
  have hu : ‖(⟨(x : EuclideanSpace ℝ (Fin 3)) 0, (x : EuclideanSpace ℝ (Fin 3)) 1⟩ : ℂ)‖ ≤ 1 :=
    (sq_le_one_iff₀ (norm_nonneg _)).mp (by rw [hnorm]; nlinarith)
  refine ⟨⟨_, mem_closedBall_zero_iff.mpr hu⟩, Subtype.ext ?_⟩
  ext i
  fin_cases i
  · simp
  · simp
  · simp only [Fin.reduceFinMk, coe_hemisphereGraph_apply, hemisphereGraphPoint_apply_two]
    rw [hnorm, sub_sub_cancel, Real.sqrt_sq_eq_abs]
    rcases mul_self_eq_one_iff.mp ((sq c).symm.trans hc) with rfl | rfl
    · rw [one_mul, abs_of_nonneg (by linarith)]
    · rw [neg_one_mul, abs_of_nonpos (by linarith), neg_neg]

end TauCeti
