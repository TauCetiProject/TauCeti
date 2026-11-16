/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Dynamics.Billiard.Inverse
public import TauCeti.Dynamics.Billiard.PeriodicPolygon
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The circular billiard table

The circle of radius `R > 0` about the origin of `ℂ`, parametrized counterclockwise by arclength,
`χ(s) = R e^{i s / R}` with length `L = 2 π R`, is a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable.circle`). Its dynamics is explicit, and this file computes it
as a test of the general billiard API of `TauCeti.Dynamics.Billiard.NextCollision`,
`TauCeti.Dynamics.Billiard.Inverse` and `TauCeti.Dynamics.Billiard.PeriodicPolygon`.

* **The billiard map.** A ball leaving `χ(s)` with tangential component `v = cos α`, `0 < α < π`,
  travels along the chord subtending the arc `2 α` and leaves the next collision point with the same
  tangential component, so the billiard map on `AddCircle L × (-1, 1)` is the rotation
  `β(s, v) = (s + 2 R arccos v mod L, v)`
  (`TauCeti.StrictConvexBilliardTable.billiardMap_circle_coe`).
* **Periodic states.** A state returns after `n` bounces exactly when `n arccos v` is a multiple of
  `π` (`TauCeti.StrictConvexBilliardTable.isPeriodicPt_billiardMap_circle_iff`), so the periodic
  states are those whose angle `arccos v` is a rational multiple of `π`
  (`TauCeti.StrictConvexBilliardTable.exists_isPeriodicPt_billiardMap_circle_iff`).
* **The chord length is a primitive.** The chord of the state `(s, v)` has length
  `ℓ = 2 R √(1 - v ^ 2)`, and on the strip `ℝ × (-1, 1)` the next-collision map `B = (t, w)`
  satisfies `B^* λ - λ = dℓ` for the Liouville form `λ = v ds`, that is `dℓ = w dt - v ds`
  (`TauCeti.StrictConvexBilliardTable.hasFDerivAt_norm_circle_nextParam_sub`).
* **The reflection law.** The unit vector along the chord from `χ(a)` to `χ(b)` makes the same
  angle `(b - a) / 2 R` with the tangents at both ends
  (`TauCeti.StrictConvexBilliardTable.inner_circle_chord_deriv_left`,
  `TauCeti.StrictConvexBilliardTable.inner_circle_chord_deriv_right`). For the equilateral
  triangle both sides of the equal-angle law are `1 / 2` at every vertex
  (`TauCeti.StrictConvexBilliardTable.inner_circle_equilateral`), while for the triangle with
  vertices at the angles `0`, `π / 2` and `π` they are `0` and `1 / √2` at the vertex at angle `0`
  (`TauCeti.StrictConvexBilliardTable.inner_circle_right_triangle`).
* **Maximal inscribed polygons.** An `N`-gon inscribed in a closed ball of radius `R` has
  perimeter at most `2 N R`; in a strictly convex space, one inscribed in the boundary sphere has
  perimeter `2 N R` exactly when each side is a diameter
  (`TauCeti.inscribedPerimeter_eq_iff_of_forall_norm_eq`). So for even `N` the perimeter maximizers
  in the circle, which give periodic billiard trajectories by
  `TauCeti.exists_billiard_periodic_reflection`, are the doubled diameters, of least period two
  (`TauCeti.StrictConvexBilliardTable.isMaxOn_inscribedPerimeter_circle_iff_of_even`); for `N = 4`
  the inscribed square is not one of them
  (`TauCeti.StrictConvexBilliardTable.not_isMaxOn_inscribedPerimeter_circle_square`). A triangle
  inscribed in a closed ball of radius `R` of an inner product space has perimeter at most
  `3 √3 R`; one inscribed in its boundary sphere has perimeter `3 √3 R` exactly when its centroid
  is the centre (`TauCeti.inscribedPerimeter_eq_three_mul_sqrt_three_iff`), so the maximal
  triangles in the circle are the equilateral ones
  (`TauCeti.StrictConvexBilliardTable.isMaxOn_inscribedPerimeter_circle_iff_sum_eq_zero`).

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table and its generating function).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapters 2 and 3 (the circular billiard).
-/

public section

noncomputable section

open Function Set Complex Real
open scoped RealInnerProductSpace

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

/-! ### Polygons inscribed in a sphere -/

section Sphere

variable {α F : Type*} [NormedAddCommGroup F] {χ : α → F} {R : ℝ} {N : ℕ}

/-- An `N`-gon inscribed in the closed ball of radius `R` has perimeter at most `2 N R`. -/
theorem inscribedPerimeter_le_of_forall_norm_le [NeZero N] (h : ∀ t, ‖χ t‖ ≤ R) (s : ZMod N → α) :
    inscribedPerimeter χ s ≤ 2 * N * R := by
  have hle : ∀ k, ‖χ (s (k + 1)) - χ (s k)‖ ≤ 2 * R := fun k ↦ by
    linarith [norm_sub_le (χ (s (k + 1))) (χ (s k)), h (s (k + 1)), h (s k)]
  calc inscribedPerimeter χ s ≤ ∑ _k : ZMod N, 2 * R := by
        rw [inscribedPerimeter_def]; exact Finset.sum_le_sum fun k _ ↦ hle k
    _ = 2 * N * R := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

private theorem inscribedPerimeter_three (χ : α → F) (s : ZMod 3 → α) :
    inscribedPerimeter χ s =
      ‖χ (s 1) - χ (s 0)‖ + ‖χ (s 2) - χ (s 1)‖ + ‖χ (s 0) - χ (s 2)‖ := by
  rw [inscribedPerimeter_def, show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} by decide,
    Finset.sum_insert (by decide), Finset.sum_pair (by decide),
    show (0 : ZMod 3) + 1 = 1 by decide, show (1 : ZMod 3) + 1 = 2 by decide,
    show (2 : ZMod 3) + 1 = 0 by decide, add_assoc]

section StrictConvexSpace

variable [NormedSpace ℝ F] [StrictConvexSpace ℝ F]

/-- In a strictly convex space, an `N`-gon inscribed in the sphere of radius `R` has the largest
possible perimeter `2 N R` exactly when each of its sides is a diameter. -/
theorem inscribedPerimeter_eq_iff_of_forall_norm_eq [NeZero N] (h : ∀ t, ‖χ t‖ = R)
    (s : ZMod N → α) :
    inscribedPerimeter χ s = 2 * N * R ↔ ∀ k, χ (s (k + 1)) = -χ (s k) := by
  have hle : ∀ k ∈ Finset.univ, ‖χ (s (k + 1)) - χ (s k)‖ ≤ 2 * R := fun k _ ↦ by
    linarith [norm_sub_le (χ (s (k + 1))) (χ (s k)), h (s (k + 1)), h (s k)]
  have hsum : ∑ _k : ZMod N, 2 * R = 2 * N * R := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
  rw [inscribedPerimeter_def, ← hsum, Finset.sum_eq_sum_iff_of_le hle]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun k ↦ ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩
  · -- A chord of length `2 R` passes through the centre, by strict convexity.
    refine eq_of_norm_eq_of_norm_add_eq (by rw [norm_neg, h, h]) ?_
    rw [← sub_eq_add_neg, hk, norm_neg, h, h, two_mul]
  · rw [hk, ← neg_add', norm_neg, ← two_smul ℝ, norm_smul, h, Real.norm_two]

end StrictConvexSpace

private theorem sum_three (x : ZMod 3 → F) : ∑ k, x k = x 0 + x 1 + x 2 := by
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} by decide,
    Finset.sum_insert (by decide), Finset.sum_pair (by decide), add_assoc]

variable [InnerProductSpace ℝ F]

/-- The sum of the squared sides of the triangle with vertices `a, b, c` is
`3 (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) - ‖a + b + c‖ ^ 2`. -/
private theorem sq_add_sq_add_sq_norm_sub (a b c : F) :
    ‖b - a‖ ^ 2 + ‖c - b‖ ^ 2 + ‖a - c‖ ^ 2 =
      3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) - ‖a + b + c‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_add_sq_real, norm_add_sq_real,
    inner_add_left, real_inner_comm a b, real_inner_comm b c]
  ring

/-- A triangle inscribed in the closed ball of radius `R` has perimeter at most `3 √3 R`, the
perimeter of an equilateral triangle inscribed in its boundary sphere. -/
theorem inscribedPerimeter_le_three_mul_sqrt_three (h : ∀ t, ‖χ t‖ ≤ R) (s : ZMod 3 → α) :
    inscribedPerimeter χ s ≤ 3 * √3 * R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans (h (s 0))
  have hsq := sq_add_sq_add_sq_norm_sub (χ (s 0)) (χ (s 1)) (χ (s 2))
  have hle (k : ZMod 3) : ‖χ (s k)‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h _) 2
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [inscribedPerimeter_three]
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, h3]
  nlinarith [sq_nonneg (‖χ (s 1) - χ (s 0)‖ - ‖χ (s 2) - χ (s 1)‖),
    sq_nonneg (‖χ (s 2) - χ (s 1)‖ - ‖χ (s 0) - χ (s 2)‖),
    sq_nonneg (‖χ (s 0) - χ (s 2)‖ - ‖χ (s 1) - χ (s 0)‖),
    sq_nonneg ‖χ (s 0) + χ (s 1) + χ (s 2)‖, hle 0, hle 1, hle 2]

/-- Two vertices of a triangle inscribed in the sphere of radius `R`, with centroid at the
centre, are at distance `√3 R`. -/
private theorem norm_sub_of_add_add_eq_zero {a b c : F} (ha : ‖a‖ = R) (hb : ‖b‖ = R)
    (hc : ‖c‖ = R) (habc : a + b + c = 0) : ‖b - a‖ = √3 * R := by
  have hR : 0 ≤ R := ha ▸ norm_nonneg a
  have hab : a + b = -c := eq_neg_of_add_eq_zero_left habc
  have h1 := norm_add_sq_real a b
  rw [hab, norm_neg, ha, hb, hc] at h1
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [norm_sub_sq_real, ha, hb, mul_pow, Real.sq_sqrt (by norm_num), real_inner_comm]
  linarith

/-- A triangle inscribed in the sphere of radius `R` has the largest possible perimeter `3 √3 R`
exactly when the centre of the sphere is its centroid, that is, when it is equilateral. -/
theorem inscribedPerimeter_eq_three_mul_sqrt_three_iff (h : ∀ t, ‖χ t‖ = R) (s : ZMod 3 → α) :
    inscribedPerimeter χ s = 3 * √3 * R ↔ ∑ k, χ (s k) = 0 := by
  rw [sum_three]
  constructor
  · intro hP
    have hsq := sq_add_sq_add_sq_norm_sub (χ (s 0)) (χ (s 1)) (χ (s 2))
    rw [h, h, h] at hsq
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [inscribedPerimeter_three] at hP
    have hP2 : (‖χ (s 1) - χ (s 0)‖ + ‖χ (s 2) - χ (s 1)‖ + ‖χ (s 0) - χ (s 2)‖) ^ 2 =
        27 * R ^ 2 := by rw [hP, mul_pow, mul_pow, h3]; ring
    rw [← norm_eq_zero, ← sq_eq_zero_iff]
    nlinarith [sq_nonneg (‖χ (s 1) - χ (s 0)‖ - ‖χ (s 2) - χ (s 1)‖),
      sq_nonneg (‖χ (s 2) - χ (s 1)‖ - ‖χ (s 0) - χ (s 2)‖),
      sq_nonneg (‖χ (s 0) - χ (s 2)‖ - ‖χ (s 1) - χ (s 0)‖),
      sq_nonneg ‖χ (s 0) + χ (s 1) + χ (s 2)‖]
  · intro h0
    rw [inscribedPerimeter_three,
      norm_sub_of_add_add_eq_zero (h _) (h _) (h _) h0,
      norm_sub_of_add_add_eq_zero (h _) (h _) (h (s 0)) (by rw [← h0]; abel),
      norm_sub_of_add_add_eq_zero (h _) (h _) (h (s 1)) (by rw [← h0]; abel)]
    ring

end Sphere

namespace StrictConvexBilliardTable

variable {R : ℝ} (hR : 0 < R)

private theorem hasDerivAt_circleMap_div (hR : R ≠ 0) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ circleMap 0 R (s / R)) (circleMap 0 1 (s / R) * I) s := by
  have h : HasDerivAt (fun s : ℝ ↦ ((s / R : ℝ) : ℂ) * I) ((1 / R : ℝ) * I) s := by
    simpa using ((hasDerivAt_id s).div_const R).ofReal_comp.mul_const I
  have h2 := (h.cexp).const_mul (R : ℂ)
  convert h2 using 1
  · funext s; simp [circleMap]
  · simp only [circleMap, zero_add, one_mul, ofReal_one, ofReal_div]
    field_simp [ofReal_ne_zero.2 hR]

private theorem inner_circleMap_sub (a b c : ℝ) :
    ⟪circleMap 0 R (b / R) - circleMap 0 R (a / R), circleMap 0 1 (c / R) * I⟫ =
      R * (Real.sin ((b - c) / R) - Real.sin ((a - c) / R)) := by
  simp only [Complex.inner, mul_re, conj_re, conj_im, sub_re, sub_im, circleMap_zero_re,
    circleMap_zero_im, mul_im, I_re, I_im, sub_div, Real.sin_sub]
  ring

private theorem areaForm_circleMap_sub (a b c : ℝ) :
    Complex.orientation.areaForm (circleMap 0 1 (c / R) * I)
        (circleMap 0 R (b / R) - circleMap 0 R (a / R)) =
      R * (Real.cos ((a - c) / R) - Real.cos ((b - c) / R)) := by
  simp only [Complex.areaForm, mul_re, conj_re, conj_im, sub_re, sub_im, circleMap_zero_re,
    circleMap_zero_im, mul_im, I_re, I_im, map_mul, conj_I, neg_re, neg_im, sub_div, Real.cos_sub]
  ring

private theorem norm_circleMap_sub_sq (a b : ℝ) :
    ‖circleMap 0 R (b / R) - circleMap 0 R (a / R)‖ ^ 2 =
      2 * R ^ 2 * (1 - Real.cos ((b - a) / R)) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, sub_im, circleMap_zero_re, circleMap_zero_im, sub_div, Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq (a / R), Real.sin_sq_add_cos_sq (b / R)]

private theorem inner_circleMap_mul_I (a b : ℝ) :
    ⟪circleMap 0 1 (a / R) * I, circleMap 0 1 (b / R) * I⟫ = Real.cos ((b - a) / R) := by
  simp only [Complex.inner, mul_re, conj_re, conj_im, circleMap_zero_re, circleMap_zero_im, mul_im,
    I_re, I_im, map_mul, conj_I, neg_re, neg_im, sub_div, Real.cos_sub]
  ring

private theorem areaForm_circleMap_mul_I (a b : ℝ) :
    Complex.orientation.areaForm (circleMap 0 1 (a / R) * I) (circleMap 0 1 (b / R) * I) =
      Real.sin ((b - a) / R) := by
  simp only [Complex.areaForm, mul_re, conj_re, conj_im, circleMap_zero_re, circleMap_zero_im,
    mul_im, I_re, I_im, map_mul, conj_I, neg_re, neg_im, sub_div, Real.sin_sub]
  ring

/-- The **circle billiard table** of radius `R > 0`: the circle of radius `R` centred at the origin
of `ℂ`, parametrized counterclockwise by arclength, `χ(s) = R e^{i s / R}`, with length
`L = 2 π R`. -/
def circle : StrictConvexBilliardTable Complex.orientation where
  toFun s := circleMap 0 R (s / R)
  period := 2 * π * R
  period_pos := by positivity
  periodic s := by
    simp only
    rw [add_div, mul_div_assoc, div_self hR.ne', mul_one, periodic_circleMap]
  norm_deriv s := by
    rw [(hasDerivAt_circleMap_div hR.ne' s).deriv]
    simp
  injOn s hs t ht h := by
    have := injOn_circleMap_of_abs_sub_le' (c := 0) hR.ne' (a := 0) (b := 2 * π) (by simp)
      ⟨div_nonneg hs.1 hR.le, (div_lt_iff₀ hR).2 (by linarith [hs.2])⟩
      ⟨div_nonneg ht.1 hR.le, (div_lt_iff₀ hR).2 (by linarith [ht.2])⟩ h
    exact (div_left_inj₀ hR.ne').1 this
  areaForm_pos s t h := by
    simp only [(hasDerivAt_circleMap_div hR.ne' s).deriv, areaForm_circleMap_sub, sub_self,
      zero_div, Real.cos_zero]
    have h2 := norm_circleMap_sub_sq (R := R) s t
    have h3 : 0 < ‖circleMap 0 R (t / R) - circleMap 0 R (s / R)‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 h)
    have : 0 < 1 - Real.cos ((t - s) / R) := by nlinarith
    positivity

variable {hR}

@[simp]
theorem circle_apply (s : ℝ) : circle hR s = circleMap 0 R (s / R) :=
  (rfl)

@[simp]
theorem period_circle : (circle hR).period = 2 * π * R :=
  (rfl)

/-- The unit tangent of the circle table at `χ(s)` is `i e^{i s / R}`. -/
@[simp]
theorem deriv_circle (s : ℝ) : deriv (circle hR) s = circleMap 0 1 (s / R) * I :=
  (hasDerivAt_circleMap_div hR.ne' s).deriv

/-- The tangential component of a chord of the circle at a vertex `χ(c)`. -/
theorem inner_circle_sub_deriv (a b c : ℝ) :
    ⟪circle hR b - circle hR a, deriv (circle hR) c⟫ =
      R * (Real.sin ((b - c) / R) - Real.sin ((a - c) / R)) := by
  rw [deriv_circle]
  exact inner_circleMap_sub a b c

/-- The normal component of a chord of the circle at a vertex `χ(c)`. -/
theorem areaForm_deriv_circle_sub (a b c : ℝ) :
    Complex.orientation.areaForm (deriv (circle hR) c) (circle hR b - circle hR a) =
      R * (Real.cos ((a - c) / R) - Real.cos ((b - c) / R)) := by
  rw [deriv_circle]
  exact areaForm_circleMap_sub a b c

/-- The chord of the circle between `χ(a)` and `χ(b)` has length `2 R |sin((b - a) / 2 R)|`. -/
theorem norm_circle_sub (a b : ℝ) :
    ‖circle hR b - circle hR a‖ = 2 * R * |Real.sin ((b - a) / (2 * R))| := by
  have h := norm_circleMap_sub_sq (R := R) a b
  have hc : Real.cos ((b - a) / R) = 1 - 2 * Real.sin ((b - a) / (2 * R)) ^ 2 := by
    rw [show (b - a) / R = 2 * ((b - a) / (2 * R)) by field_simp, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq ((b - a) / (2 * R))]
  rw [hc] at h
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [circle_apply, circle_apply, h, mul_pow, mul_pow, sq_abs]
  ring

/-- The unit tangents at `χ(a)` and `χ(b)` make the angle `(b - a) / R`. -/
theorem inner_deriv_circle (a b : ℝ) :
    ⟪deriv (circle hR) a, deriv (circle hR) b⟫ = Real.cos ((b - a) / R) := by
  rw [deriv_circle, deriv_circle]
  exact inner_circleMap_mul_I a b

/-- The oriented angle from the unit tangent at `χ(a)` to that at `χ(b)` is `(b - a) / R`. -/
theorem areaForm_deriv_circle (a b : ℝ) :
    Complex.orientation.areaForm (deriv (circle hR) a) (deriv (circle hR) b) =
      Real.sin ((b - a) / R) := by
  rw [deriv_circle, deriv_circle]
  exact areaForm_circleMap_mul_I a b

/-- The circle table lies on the circle of radius `R` about the origin. -/
theorem norm_circle (s : ℝ) : ‖circle hR s‖ = R := by
  rw [circle_apply, norm_circleMap_zero, abs_of_pos hR]

/-! ### The billiard map of the circle -/

/-- **The next collision on the circle.** A ball leaving `χ(s)` with tangential component
`v = cos α`, `0 < α < π`, travels along a chord subtending the arc `2 α`, so the next collision
parameter is `s + 2 R arccos v`. -/
theorem nextParam_circle {v : ℝ} (hv : v ∈ Ioo (-1) 1) (s : ℝ) :
    (circle hR).nextParam s v = s + 2 * R * Real.arccos v := by
  set α := Real.arccos v
  have hα : α ∈ Ioo 0 π := ⟨Real.arccos_pos.2 hv.2, Real.arccos_lt_pi.2 hv.1⟩
  have hcos : Real.cos α = v := Real.cos_arccos hv.1.le hv.2.le
  have hsin : Real.sin α = √(1 - v ^ 2) := Real.sin_arccos v
  have harc : (s + 2 * R * α - s) / R = 2 * α := by field_simp; ring
  refine (eq_nextParam_of_areaForm_eq_zero _ hv ⟨by nlinarith [hα.1], ?_⟩ ?_).symm
  · rw [period_circle]; nlinarith [hα.2]
  rw [outgoingDir_def, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, Orientation.areaForm_rightAngleRotation_left, areaForm_deriv_circle_sub,
    real_inner_comm, inner_circle_sub_deriv, sub_self, zero_div, Real.cos_zero, Real.sin_zero,
    harc, ← hsin, ← hcos, Real.cos_two_mul, Real.sin_two_mul, smul_eq_mul, smul_eq_mul]
  linear_combination (-2 * R * Real.cos α) * Real.sin_sq_add_cos_sq α

/-- **The circle billiard preserves the tangential component**: every chord makes the same angle
with the circle at both of its ends. -/
theorem nextTangential_circle {v : ℝ} (hv : v ∈ Ioo (-1) 1) (s : ℝ) :
    (circle hR).nextTangential s v = v := by
  set α := Real.arccos v
  have hcos : Real.cos α = v := Real.cos_arccos hv.1.le hv.2.le
  have hsin : Real.sin α = √(1 - v ^ 2) := Real.sin_arccos v
  have harc : (s + 2 * R * α - s) / R = 2 * α := by field_simp; ring
  rw [nextTangential_def, nextParam_circle hv, outgoingDir_def, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, Orientation.inner_rightAngleRotation_left,
    inner_deriv_circle, areaForm_deriv_circle, harc, ← hsin, ← hcos, Real.cos_two_mul,
    Real.sin_two_mul]
  linear_combination (2 * Real.cos α) * Real.sin_sq_add_cos_sq α

/-- **The billiard map of the circle** is the rotation `β(s, v) = (s + 2 R arccos v mod L, v)` of
each circle of constant tangential component. -/
theorem billiardMap_circle_coe (s : ℝ) (v : Ioo (-1 : ℝ) 1) :
    (circle hR).billiardMap ((s : AddCircle (circle hR).period), v) =
      (((s + 2 * R * Real.arccos v : ℝ) : AddCircle (circle hR).period), v) := by
  rw [billiardMap_coe, Prod.mk.injEq]
  exact ⟨by rw [nextParam_circle v.2], Subtype.ext (nextTangential_circle v.2 s)⟩

/-- The `n`-th iterate of the circle billiard rotates by `n` times the arc `2 R arccos v`. -/
theorem iterate_billiardMap_circle_coe (n : ℕ) (s : ℝ) (v : Ioo (-1 : ℝ) 1) :
    (circle hR).billiardMap^[n] ((s : AddCircle (circle hR).period), v) =
      (((s + n * (2 * R * Real.arccos v) : ℝ) : AddCircle (circle hR).period), v) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply, billiardMap_circle_coe, ih]
    push_cast
    ring_nf

/-- **The periodicity criterion of the circle billiard.** A state `x = (θ, v)` returns after `n`
bounces exactly when `n` times its angle `arccos v` with the boundary is a multiple of `π`, that is
when the `n` chords together wind an integer number of times around the circle. -/
theorem isPeriodicPt_billiardMap_circle_iff {n : ℕ}
    {x : AddCircle (circle hR).period × Ioo (-1 : ℝ) 1} :
    IsPeriodicPt (circle hR).billiardMap n x ↔ ∃ k : ℤ, n * Real.arccos x.2 = k * π := by
  obtain ⟨θ, v⟩ := x
  induction θ using QuotientAddGroup.induction_on with | H s => ?_
  rw [IsPeriodicPt, IsFixedPt, iterate_billiardMap_circle_coe, Prod.mk.injEq, and_iff_left rfl,
    AddCircle.coe_add, add_eq_left, AddCircle.coe_eq_zero_iff, period_circle]
  refine exists_congr fun k ↦ ?_
  rw [zsmul_eq_mul]
  constructor <;> intro h
  · have := hR.ne'
    field_simp at h ⊢
    linarith
  · nlinarith

/-- **Rational rotation numbers.** A state of the circle billiard is periodic exactly when its
angle `arccos v` with the boundary is a rational multiple of `π`. -/
theorem exists_isPeriodicPt_billiardMap_circle_iff
    {x : AddCircle (circle hR).period × Ioo (-1 : ℝ) 1} :
    (∃ n, 0 < n ∧ IsPeriodicPt (circle hR).billiardMap n x) ↔ ∃ q : ℚ, Real.arccos x.2 = q * π := by
  simp only [isPeriodicPt_billiardMap_circle_iff]
  constructor
  · rintro ⟨n, hn, k, hk⟩
    refine ⟨k / n, ?_⟩
    have : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    linarith
  · rintro ⟨q, hq⟩
    refine ⟨q.den, q.den_pos, q.num, ?_⟩
    rw [hq, ← mul_assoc]
    congr 1
    exact_mod_cast q.den_mul_eq_num

/-! ### The chord length as a primitive -/

/-- The chord from `χ(s)` to the next collision point has length `2 R √(1 - v ^ 2)`. -/
theorem norm_circle_nextParam_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) (s : ℝ) :
    ‖circle hR ((circle hR).nextParam s v) - circle hR s‖ = 2 * R * √(1 - v ^ 2) := by
  rw [norm_circle_sub, nextParam_circle hv,
    show (s + 2 * R * Real.arccos v - s) / (2 * R) = Real.arccos v by field_simp; ring,
    Real.sin_arccos, abs_of_nonneg (Real.sqrt_nonneg _)]

private theorem eventuallyEq_strip {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1)
    (h : ∀ y : ℝ × ℝ, y.2 ∈ Ioo (-1) 1 → f y = g y) : f =ᶠ[nhds x] g :=
  Filter.eventuallyEq_of_mem ((isOpen_Ioo.preimage continuous_snd).mem_nhds hx) h

/-- On the strip `ℝ × (-1, 1)`, the next collision parameter `t(s, v) = s + 2 R arccos v` of the
circle has differential `dt = ds - 2 R / √(1 - v ^ 2) dv`. -/
theorem hasFDerivAt_nextParam_circle {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    HasFDerivAt (fun y : ℝ × ℝ ↦ (circle hR).nextParam y.1 y.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ -
        (2 * R / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have h := hasFDerivAt_fst.add
    (((Real.hasDerivAt_arccos (x := x.2) (by linarith [hx.1]) (by linarith [hx.2])).comp_hasFDerivAt
      x (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := x))).const_mul (2 * R))
  refine (h.congr_of_eventuallyEq
    (eventuallyEq_strip hx fun y hy ↦ nextParam_circle hy y.1)).congr_fderiv
    (ContinuousLinearMap.ext fun y ↦ ?_)
  simp only [add_apply, ContinuousLinearMap.coe_fst', smul_apply,
    ContinuousLinearMap.coe_snd', sub_apply, smul_eq_mul]
  ring

/-- **The chord length is a primitive for the circle billiard.** On the strip `ℝ × (-1, 1)` with
the Liouville form `λ = v ds`, the next-collision map `B(s, v) = (t, w)` satisfies
`B^* λ - λ = dℓ`, where `ℓ(s, v) = ‖χ(t) - χ(s)‖` is the length of the chord: here
`B^* λ = w dt`, with `dt` given by `hasFDerivAt_nextParam_circle`, and the identity is
`dℓ = w dt - v ds`. -/
theorem hasFDerivAt_norm_circle_nextParam_sub {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    HasFDerivAt (fun y : ℝ × ℝ ↦ ‖circle hR ((circle hR).nextParam y.1 y.2) - circle hR y.1‖)
      ((circle hR).nextTangential x.1 x.2 •
          (ContinuousLinearMap.fst ℝ ℝ ℝ -
            (2 * R / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) -
        x.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
  have hpos : 0 < 1 - x.2 ^ 2 := by nlinarith [hx.1, hx.2]
  have h := (((hasDerivAt_pow 2 x.2).const_sub 1).sqrt hpos.ne').comp_hasFDerivAt x
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := x)) |>.const_mul (2 * R)
  refine (h.congr_of_eventuallyEq
    (eventuallyEq_strip hx fun y hy ↦ norm_circle_nextParam_sub hy y.1)).congr_fderiv
    (ContinuousLinearMap.ext fun y ↦ ?_)
  have hsqrt : √(1 - x.2 ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  simp only [smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul,
    sub_apply, ContinuousLinearMap.coe_fst', nextTangential_circle hx,
    Nat.cast_ofNat]
  field_simp
  ring

/-! ### The reflection law on the circle -/

/-- On the circle, the unit vector along the chord from `χ(a)` to `χ(b)` makes the angle
`(b - a) / 2 R` with the tangent at `χ(a)`, when this angle lies in `(0, π)` modulo `2 π`. -/
theorem inner_circle_chord_deriv_left {a b : ℝ} (hab : 0 < Real.sin ((b - a) / (2 * R))) :
    ⟪‖circle hR b - circle hR a‖⁻¹ • (circle hR b - circle hR a), deriv (circle hR) a⟫ =
      Real.cos ((b - a) / (2 * R)) := by
  rw [real_inner_smul_left, inner_circle_sub_deriv, norm_circle_sub, abs_of_pos hab, sub_self,
    zero_div, Real.sin_zero, sub_zero, show (b - a) / R = 2 * ((b - a) / (2 * R)) by field_simp,
    Real.sin_two_mul]
  field_simp

/-- On the circle, the unit vector along the chord from `χ(a)` to `χ(b)` makes the same angle
`(b - a) / 2 R` with the tangent at `χ(b)` as with the tangent at `χ(a)`. -/
theorem inner_circle_chord_deriv_right {a b : ℝ} (hab : 0 < Real.sin ((b - a) / (2 * R))) :
    ⟪‖circle hR b - circle hR a‖⁻¹ • (circle hR b - circle hR a), deriv (circle hR) b⟫ =
      Real.cos ((b - a) / (2 * R)) := by
  rw [real_inner_smul_left, inner_circle_sub_deriv, norm_circle_sub, abs_of_pos hab, sub_self,
    zero_div, Real.sin_zero, zero_sub, show (a - b) / R = -(2 * ((b - a) / (2 * R))) by
      field_simp; ring, Real.sin_neg, neg_neg, Real.sin_two_mul]
  field_simp

private theorem circle_two_pi_mul_div_three :
    circle hR (2 * (2 * π * R / 3)) = circle hR (-(2 * π * R / 3)) := by
  rw [← (circle hR).periodic (-(2 * π * R / 3)), period_circle]
  congr 1
  ring

/-- **The equilateral triangle obeys the reflection law**: at each of its vertices, both sides make
the angle `π / 3` with the tangent, so both sides of the equal-angle law are `1 / 2`. -/
theorem inner_circle_equilateral {s : ZMod 3 → ℝ} (hs : ∀ k, s k = k.val * (2 * π * R / 3))
    (k : ZMod 3) :
    ⟪‖circle hR (s k) - circle hR (s (k - 1))‖⁻¹ • (circle hR (s k) - circle hR (s (k - 1))),
        deriv (circle hR) (s k)⟫ = 1 / 2 ∧
      ⟪‖circle hR (s (k + 1)) - circle hR (s k)‖⁻¹ • (circle hR (s (k + 1)) - circle hR (s k)),
        deriv (circle hR) (s k)⟫ = 1 / 2 := by
  have hπ : 0 < Real.sin ((2 * π * R / 3) / (2 * R)) := by
    rw [show (2 * π * R / 3) / (2 * R) = π / 3 by field_simp]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hcos : Real.cos ((2 * π * R / 3) / (2 * R)) = 1 / 2 := by
    rw [show (2 * π * R / 3) / (2 * R) = π / 3 by field_simp, Real.cos_pi_div_three]
  have hl {a b : ℝ} (h : b - a = 2 * π * R / 3) :=
    (inner_circle_chord_deriv_left (hR := hR) (h ▸ hπ)).trans (h ▸ hcos)
  have hr {a b : ℝ} (h : b - a = 2 * π * R / 3) :=
    (inner_circle_chord_deriv_right (hR := hR) (h ▸ hπ)).trans (h ▸ hcos)
  have s0 : s 0 = 0 := by rw [hs, ZMod.val_zero, Nat.cast_zero, zero_mul]
  have s1 : s 1 = 2 * π * R / 3 := by
    rw [hs, show (1 : ZMod 3).val = 1 from rfl, Nat.cast_one, one_mul]
  have s2 : s 2 = 2 * (2 * π * R / 3) := by
    rw [hs, show (2 : ZMod 3).val = 2 from rfl, Nat.cast_ofNat]
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
  · rw [show (0 : ZMod 3) - 1 = 2 by decide, zero_add, s0, s1, s2, circle_two_pi_mul_div_three]
    exact ⟨hr (by ring), hl (by ring)⟩
  · rw [sub_self, show (1 : ZMod 3) + 1 = 2 by decide, s0, s1, s2]
    exact ⟨hr (by ring), hl (by ring)⟩
  · rw [show (2 : ZMod 3) - 1 = 1 by decide, show (2 : ZMod 3) + 1 = 0 by decide, s0, s1, s2]
    refine ⟨hr (by ring), ?_⟩
    rw [← (circle hR).periodic 0, zero_add, period_circle]
    exact hl (by ring)

/-- **A right-angled inscribed triangle violates the reflection law.** For the triangle with
vertices at the angles `0`, `π / 2` and `π`, at the vertex at angle `0` the incoming side, a
diameter, is orthogonal to the tangent, while the outgoing side makes the angle `π / 4` with it:
the two sides of the equal-angle law are `0` and `1 / √2`. -/
theorem inner_circle_right_triangle {s : ZMod 3 → ℝ} (hs : ∀ k, s k = k.val * (π * R / 2)) :
    ⟪‖circle hR (s 0) - circle hR (s (0 - 1))‖⁻¹ • (circle hR (s 0) - circle hR (s (0 - 1))),
        deriv (circle hR) (s 0)⟫ = 0 ∧
      ⟪‖circle hR (s (0 + 1)) - circle hR (s 0)‖⁻¹ • (circle hR (s (0 + 1)) - circle hR (s 0)),
        deriv (circle hR) (s 0)⟫ = 1 / √2 := by
  have s0 : s 0 = 0 := by rw [hs, ZMod.val_zero, Nat.cast_zero, zero_mul]
  have s1 : s 1 = π * R / 2 := by
    rw [hs, show (1 : ZMod 3).val = 1 from rfl, Nat.cast_one, one_mul]
  have s2 : s 2 = π * R := by
    rw [hs, show (2 : ZMod 3).val = 2 from rfl, Nat.cast_ofNat]
    ring
  rw [show (0 : ZMod 3) - 1 = 2 by decide, zero_add, s0, s1, s2,
    show circle hR (π * R) = circle hR (-(π * R)) by
      rw [← (circle hR).periodic (-(π * R)), period_circle]; congr 1; ring]
  have hπ2 : (0 - -(π * R)) / (2 * R) = π / 2 := by rw [zero_sub, neg_neg]; field_simp
  constructor
  · rw [inner_circle_chord_deriv_right (by rw [hπ2, Real.sin_pi_div_two]; norm_num), hπ2,
      Real.cos_pi_div_two]
  · rw [inner_circle_chord_deriv_left (by
      rw [show (π * R / 2 - 0) / (2 * R) = π / 4 by field_simp; ring]
      exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])),
      show (π * R / 2 - 0) / (2 * R) = π / 4 by field_simp; ring, Real.cos_pi_div_four]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]

/-! ### Inscribed polygons of maximal perimeter -/

private theorem circle_mul_pi (x : ℝ) : circle hR (x * (π * R)) = circleMap 0 R (x * π) := by
  rw [circle_apply, ← mul_assoc, mul_div_cancel_right₀ _ hR.ne']

/-- **Maximal inscribed polygons with an even number of vertices.** For even `N`, an inscribed
`N`-gon in the circle has maximal perimeter exactly when each of its sides is a diameter: it is a
diameter traversed back and forth `N / 2` times. -/
theorem isMaxOn_inscribedPerimeter_circle_iff_of_even {N : ℕ} [NeZero N] (hN : Even N)
    {s : ZMod N → ℝ} :
    IsMaxOn (inscribedPerimeter (circle hR)) univ s ↔
      ∀ k, circle hR (s (k + 1)) = -circle hR (s k) := by
  rw [← inscribedPerimeter_eq_iff_of_forall_norm_eq (norm_circle (hR := hR))]
  -- The doubled diameter, alternating between the parameters `0` and `π R`, has perimeter `2 N R`.
  obtain ⟨d, hd⟩ : ∃ d : ZMod N → ℝ, inscribedPerimeter (circle hR) d = 2 * N * R := by
    refine ⟨fun k ↦ ((ZMod.castHom (even_iff_two_dvd.1 hN) (ZMod 2) k).val : ℝ) * (π * R),
      (inscribedPerimeter_eq_iff_of_forall_norm_eq (norm_circle (hR := hR)) _).2 fun k ↦ ?_⟩
    simp only [map_add, map_one, circle_mul_pi]
    generalize ZMod.castHom _ (ZMod 2) k = j
    obtain rfl | rfl : j = 0 ∨ j = 1 := by revert j; decide
    · rw [zero_add, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
        circleMap_zero, circleMap_zero, ofReal_zero, zero_mul, Complex.exp_zero,
        Complex.exp_pi_mul_I]
      ring
    · rw [show (1 + 1 : ZMod 2) = 0 by decide, ZMod.val_zero, ZMod.val_one, Nat.cast_zero,
        Nat.cast_one, zero_mul, one_mul, circleMap_zero, circleMap_zero, ofReal_zero, zero_mul,
        Complex.exp_zero, Complex.exp_pi_mul_I]
      ring
  constructor
  · exact fun hmax ↦ le_antisymm
      (inscribedPerimeter_le_of_forall_norm_le (fun t ↦ (norm_circle t).le) s)
      (hd ▸ hmax (mem_univ d))
  · exact fun hs t _ ↦ hs ▸ inscribedPerimeter_le_of_forall_norm_le (fun t ↦ (norm_circle t).le) t

/-- **A maximal inscribed polygon with an even number of vertices has least period two**: its
vertices alternate between the two ends of a diameter. -/
theorem circle_apply_add_one_add_one_of_isMaxOn {N : ℕ} [NeZero N] (hN : Even N)
    {s : ZMod N → ℝ} (hs : IsMaxOn (inscribedPerimeter (circle hR)) univ s) (k : ZMod N) :
    circle hR (s (k + 1 + 1)) = circle hR (s k) ∧ circle hR (s (k + 1)) ≠ circle hR (s k) := by
  have h := (isMaxOn_inscribedPerimeter_circle_iff_of_even hN).1 hs
  refine ⟨by rw [h, h, neg_neg], fun he ↦ ?_⟩
  rw [h k, neg_eq_self, ← norm_eq_zero, norm_circle] at he
  exact hR.ne' he

/-- **The inscribed square is not a maximal quadrilateral**: the maximal inscribed quadrilaterals
are the doubled diameters. -/
theorem not_isMaxOn_inscribedPerimeter_circle_square :
    ¬ IsMaxOn (inscribedPerimeter (circle hR)) univ
      (fun k : ZMod 4 ↦ (k.val : ℝ) * (π * R / 2)) := by
  rw [isMaxOn_inscribedPerimeter_circle_iff_of_even (by decide)]
  intro h
  have h0 := congrArg Complex.re (h 0)
  rw [show (0 : ZMod 4) + 1 = 1 by decide, show (1 : ZMod 4).val = 1 from rfl, ZMod.val_zero] at h0
  simp only [Nat.cast_one, one_mul, circle_apply, Nat.cast_zero, zero_mul, zero_div,
    circleMap_zero_re, neg_re] at h0
  rw [show π * R / 2 / R = π / 2 by field_simp, Real.cos_pi_div_two, Real.cos_zero] at h0
  linarith

/-- **Maximal inscribed triangles are equilateral.** An inscribed triangle in the circle has
maximal perimeter exactly when its centroid is the centre of the circle. -/
theorem isMaxOn_inscribedPerimeter_circle_iff_sum_eq_zero {s : ZMod 3 → ℝ} :
    IsMaxOn (inscribedPerimeter (circle hR)) univ s ↔ ∑ k, circle hR (s k) = 0 := by
  rw [← inscribedPerimeter_eq_three_mul_sqrt_three_iff (norm_circle (hR := hR))]
  -- The equilateral triangle with vertices at the parameters `0`, `2 π R / 3` and `4 π R / 3`.
  obtain ⟨d, hd⟩ : ∃ d : ZMod 3 → ℝ, inscribedPerimeter (circle hR) d = 3 * √3 * R := by
    refine ⟨fun k ↦ (k.val : ℝ) * (2 * π * R / 3),
      (inscribedPerimeter_eq_three_mul_sqrt_three_iff (norm_circle (hR := hR)) _).2 ?_⟩
    rw [sum_three]
    apply Complex.ext <;>
    · simp only [circle_apply, show (1 : ZMod 3).val = 1 from rfl,
        show (2 : ZMod 3).val = 2 from rfl, ZMod.val_zero, add_re, add_im, circleMap_zero_re,
        circleMap_zero_im, zero_re, zero_im, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
      rw [show 0 * (2 * π * R / 3) / R = 0 by ring, show 1 * (2 * π * R / 3) / R = π - π / 3 by
          field_simp; ring, show 2 * (2 * π * R / 3) / R = π / 3 + π by field_simp; ring]
      simp only [Real.cos_zero, Real.sin_zero, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_add_pi,
        Real.sin_add_pi, Real.cos_pi_div_three]
      ring
  constructor
  · exact fun hmax ↦ le_antisymm
      (inscribedPerimeter_le_three_mul_sqrt_three (fun t ↦ (norm_circle t).le) s)
      (hd ▸ hmax (mem_univ d))
  · exact fun hs t _ ↦ hs ▸
      inscribedPerimeter_le_three_mul_sqrt_three (fun t ↦ (norm_circle t).le) t

end StrictConvexBilliardTable

end TauCeti
