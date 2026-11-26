/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Holder

/-!
# The radial retraction onto a closed ball

In a real normed space, `TauCeti.radialRetraction r` scales a vector `x` by
`min 1 (r / ‖x‖)`. When `0 ≤ r`, it fixes the closed ball of radius `r` and pushes everything
outside it to the sphere of radius `r` along the ray through the origin. It is the standard device
for turning a map that is only Lipschitz near the origin into a globally Lipschitz map agreeing with
it near the origin, and it is used that way to cut off the nonlinearity of a differential equation
outside a small ball around an equilibrium.

Translating gives `TauCeti.centeredRadialRetraction x₀ r`, the retraction onto the closed ball of
radius `r` centred at an arbitrary point `x₀`, with the same API. Precomposing with it also
globalizes Hölder maps: a map that is `α`-Hölder with constant `c` on the closed ball becomes
globally `α`-Hölder with the same exponent and constant `c * 2 ^ α`. This is how variable
coefficients that are only Hölder near a point are extended to the whole space.

For a nonnegative radius, the same formula on a seminormed space retains its norm formula,
distance bounds, Lipschitz estimates and joint continuity. A vector of norm zero is sent to zero,
so the fixed-ball and local identity equalities require a normed space.

For `0 ≤ r`, the map is `2`-Lipschitz in any seminormed space, and `2` is the constant carried
by `TauCeti.lipschitzWith_radialRetraction`; it is not optimal in every space (in a Hilbert space
the retraction is the metric projection onto a convex set, hence `1`-Lipschitz) but the exact
constant never matters for cutting off, where one is free to shrink the radius instead.

## Main declarations

* `TauCeti.radialRetraction`: scaling by `min 1 (r / ‖x‖)`; when `0 ≤ r`, this is the retraction
  onto the closed ball of radius `r` centred at the origin.
* `TauCeti.centeredRadialRetraction`: the corresponding retraction onto a closed ball with an
  arbitrary centre.
* `TauCeti.radialRetractionToClosedBall`: for `0 ≤ r`, the radial retraction as a map into the
  closed ball of radius `r`.
* `TauCeti.norm_radialRetraction`: for `0 ≤ r`, its norm is `min ‖x‖ r`.
* `TauCeti.norm_sub_radialRetraction`: for `0 ≤ r`, it moves `x` by `max (‖x‖ - r) 0`.
* `TauCeti.max_norm_smul_radialRetraction`: scaling the retraction of `x` by `max ‖x‖ r` gives
  `r • x`, so `x` is recovered from its retraction and its norm.
* `TauCeti.radialRetraction_eventuallyEq_id`: inside the open ball, it agrees locally with the
  identity.
* `TauCeti.lipschitzWith_radialRetraction`: for `0 ≤ r`, it is `2`-Lipschitz.
* `TauCeti.norm_radialRetraction_eq_abs_min`, `TauCeti.norm_radialRetraction_le_abs_min`: for
  any radius, its norm is at most `|min ‖x‖ r|`, with equality unless `‖x‖ = 0` and `r < 0`.
* `Filter.Tendsto.radialRetraction`, `ContinuousWithinAt.radialRetraction`,
  `ContinuousAt.radialRetraction`, `ContinuousOn.radialRetraction`,
  `Continuous.radialRetraction`: it depends jointly continuously on the radius and the point,
  provided the radius is nonnegative wherever the point has norm zero.
* `Filter.Tendsto.centeredRadialRetraction`, `ContinuousWithinAt.centeredRadialRetraction`,
  `ContinuousAt.centeredRadialRetraction`, `ContinuousOn.centeredRadialRetraction`,
  `Continuous.centeredRadialRetraction`: the centred retraction depends jointly continuously on
  the centre, the radius and the point, provided the radius is nonnegative wherever the point lies
  at distance zero from the centre.
* `TauCeti.dist_centeredRadialRetraction`: for `0 ≤ r`, the distance from the centre is
  `min (dist x x₀) r`.
* `TauCeti.dist_centeredRadialRetraction_eq_abs_min`,
  `TauCeti.dist_centeredRadialRetraction_le_abs_min`: for any radius, the distance from the centre
  is at most `|min (dist x x₀) r|`, with equality unless `dist x x₀ = 0` and `r < 0`.
* `TauCeti.lipschitzWith_centeredRadialRetraction`: for `0 ≤ r`, the centred retraction is
  `2`-Lipschitz.
* `TauCeti.mapsTo_centeredRadialRetraction_of_convex`: for `0 ≤ r`, the centred retraction maps a
  convex set containing the centre into its intersection with the closed ball.
* `LipschitzOnWith.comp_centeredRadialRetraction`: precomposing with the centred retraction makes a
  map that is Lipschitz on the closed ball globally Lipschitz, with twice the constant.
* `LipschitzOnWith.dist_comp_centeredRadialRetraction_le`: it keeps the Lipschitz bound at the
  centre with the same constant.
* `LipschitzOnWith.comp_radialRetraction`: precomposing with it makes a map that is Lipschitz on
  the closed ball of radius `r` globally Lipschitz, with twice the constant.
* `HolderOnWith.comp_centeredRadialRetraction`: precomposing with the centred retraction makes a
  map that is `α`-Hölder on the closed ball globally `α`-Hölder, with constant multiplied by
  `2 ^ α`.

## References

* D. G. de Figueiredo, L. A. Karlovitz, *On the radial projection in normed spaces*,
  Bull. Amer. Math. Soc. 73 (1967), 364–368.
-/

public section

open Filter Metric Set Topology

open scoped NNReal

namespace TauCeti

variable {E : Type*} {r : ℝ} {x : E}

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scale `x` by `min 1 (r / ‖x‖)`. In a normed space and for `0 ≤ r`, this is the
**radial retraction** onto the closed ball of radius `r` centred at the origin. In a seminormed
space it sends every vector of norm zero to zero. For `0 ≤ r`, vectors of positive norm at most
`r` are fixed, and vectors outside the ball are pulled back along their ray to the sphere of
radius `r`. -/
noncomputable def radialRetraction (r : ℝ) (x : E) : E := min 1 (r / ‖x‖) • x

/-- The defining formula of the radial retraction. -/
theorem radialRetraction_def (r : ℝ) (x : E) : radialRetraction r x = min 1 (r / ‖x‖) • x :=
  (rfl)

/-- Translate `radialRetraction r` to centre `x₀`: `x ↦ x₀ + radialRetraction r (x - x₀)`.
In a normed space and for `0 ≤ r`, this is the radial retraction onto the closed ball of radius
`r` centred at `x₀`. -/
noncomputable def centeredRadialRetraction (x₀ : E) (r : ℝ) (x : E) : E :=
  x₀ + radialRetraction r (x - x₀)

/-- The defining formula of the centred radial retraction, as a translate of the radial
retraction about the origin. -/
theorem centeredRadialRetraction_def (x₀ : E) (r : ℝ) (x : E) :
    centeredRadialRetraction x₀ r x = x₀ + radialRetraction r (x - x₀) := (rfl)

/-- The radial retraction centred at the origin is the original radial retraction. -/
@[simp]
theorem centeredRadialRetraction_zero (r : ℝ) :
    centeredRadialRetraction (0 : E) r = radialRetraction r := by
  funext x
  simp [centeredRadialRetraction]

/-- The radial retraction of radius zero sends every vector to zero. -/
@[simp]
theorem radialRetraction_zero (x : E) : radialRetraction 0 x = 0 := by
  simp [radialRetraction_def]

/-- The centred radial retraction of radius zero sends every point to the centre. -/
@[simp]
theorem centeredRadialRetraction_zero_radius (x₀ x : E) :
    centeredRadialRetraction x₀ 0 x = x₀ := by
  simp [centeredRadialRetraction_def]

/-- The radial retraction sends every vector of norm zero to zero. -/
@[simp]
theorem radialRetraction_of_norm_eq_zero (hx : ‖x‖ = 0) : radialRetraction r x = 0 := by
  simp [radialRetraction_def, hx]

/-- The centred radial retraction sends every point at distance zero from its centre to the
centre. -/
@[simp]
theorem centeredRadialRetraction_of_dist_eq_zero {x₀ : E} (h : dist x x₀ = 0) :
    centeredRadialRetraction x₀ r x = x₀ := by
  rw [dist_eq_norm] at h
  simp [centeredRadialRetraction_def, h]

/-- A vector of positive norm at most `r` is fixed by the radial retraction. -/
@[simp]
theorem radialRetraction_of_norm_pos_of_norm_le (hx : 0 < ‖x‖) (h : ‖x‖ ≤ r) :
    radialRetraction r x = x := by
  rw [radialRetraction_def, min_eq_left ((le_div_iff₀ hx).2 (by simpa using h)), one_smul]

/-- A point of positive distance at most `r` from the centre is fixed by the centred radial
retraction. -/
@[simp]
theorem centeredRadialRetraction_of_dist_pos_of_dist_le {x₀ : E}
    (hx : 0 < dist x x₀) (h : dist x x₀ ≤ r) : centeredRadialRetraction x₀ r x = x := by
  rw [dist_eq_norm] at hx h
  rw [centeredRadialRetraction_def, radialRetraction_of_norm_pos_of_norm_le hx h]
  abel

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction fixes the closed ball of radius `r`. -/
@[simp]
theorem radialRetraction_of_norm_le (h : ‖x‖ ≤ r) : radialRetraction r x = x := by
  by_cases hx : x = 0
  · simp [hx]
  exact radialRetraction_of_norm_pos_of_norm_le (norm_pos_iff.2 hx) h

/-- The centred radial retraction fixes its closed ball. -/
@[simp]
theorem centeredRadialRetraction_of_mem_closedBall {x₀ : E} (hx : x ∈ closedBall x₀ r) :
    centeredRadialRetraction x₀ r x = x := by
  rw [centeredRadialRetraction, radialRetraction_of_norm_le]
  · abel
  · simpa only [mem_closedBall, dist_eq_norm] using hx

/-- The radial retraction agrees with the identity on a neighborhood of every point in the open
ball. -/
theorem radialRetraction_eventuallyEq_id (hx : ‖x‖ < r) :
    radialRetraction r =ᶠ[nhds x] id :=
  eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)) fun _ hy ↦
    radialRetraction_of_norm_le (mem_ball_zero_iff.1 hy).le

/-- The centred radial retraction agrees with the identity on a neighborhood of every point in
the open ball. -/
theorem centeredRadialRetraction_eventuallyEq_id {x₀ : E} (hx : x ∈ ball x₀ r) :
    centeredRadialRetraction x₀ r =ᶠ[nhds x] id :=
  eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) fun _ hy ↦
    centeredRadialRetraction_of_mem_closedBall (mem_ball.1 hy).le

end Normed

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Outside the closed ball of radius `r` the radial retraction scales by `r / ‖x‖`. -/
theorem radialRetraction_of_le_norm (h : r ≤ ‖x‖) :
    radialRetraction r x = (r / ‖x‖) • x := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · rw [radialRetraction, ← hx, div_zero, min_eq_right zero_le_one]
  · rw [radialRetraction, min_eq_right ((div_le_one hx).2 h)]

/-- Outside the closed ball of radius `r` about `x₀`, the centred radial retraction moves `x`
towards `x₀` by the factor `r / dist x x₀`. -/
theorem centeredRadialRetraction_of_le_dist {x₀ : E} (h : r ≤ dist x x₀) :
    centeredRadialRetraction x₀ r x = x₀ + (r / dist x x₀) • (x - x₀) := by
  rw [dist_eq_norm] at h ⊢
  rw [centeredRadialRetraction_def, radialRetraction_of_le_norm h]

/-- The radial retraction has norm `|min ‖x‖ r|`, provided `x` has nonzero norm or the radius is
nonnegative. In the remaining case, `‖x‖ = 0` with `r < 0`, the vector is sent to zero. -/
theorem norm_radialRetraction_eq_abs_min (h : ‖x‖ ≠ 0 ∨ 0 ≤ r) :
    ‖radialRetraction r x‖ = |min ‖x‖ r| := by
  by_cases hx : ‖x‖ = 0
  · simp [hx, min_eq_left (h.resolve_left (not_not.2 hx))]
  have hmin : min ‖x‖ r = min 1 (r / ‖x‖) * ‖x‖ := by
    simp [min_mul_of_nonneg _ _ (norm_nonneg x), hx]
  simp [hmin, radialRetraction_def, norm_smul, abs_mul]

/-- For nonnegative radius, the radial retraction has norm `min ‖x‖ r`. -/
@[simp]
theorem norm_radialRetraction (hr : 0 ≤ r) (x : E) : ‖radialRetraction r x‖ = min ‖x‖ r := by
  rw [norm_radialRetraction_eq_abs_min (.inr hr), abs_of_nonneg (le_min (norm_nonneg x) hr)]

/-- For any radius, the radial retraction has norm at most `|min ‖x‖ r|`, with equality except
at a vector of norm zero with a negative radius (`TauCeti.norm_radialRetraction_eq_abs_min`). -/
theorem norm_radialRetraction_le_abs_min (r : ℝ) (x : E) :
    ‖radialRetraction r x‖ ≤ |min ‖x‖ r| := by
  by_cases h : ‖x‖ ≠ 0 ∨ 0 ≤ r
  · exact (norm_radialRetraction_eq_abs_min h).le
  · rw [radialRetraction_of_norm_eq_zero (not_not.1 (not_or.1 h).1), norm_zero]
    exact abs_nonneg _

/-- For nonnegative radius, the radial retraction moves `x` by `max (‖x‖ - r) 0`. -/
theorem norm_sub_radialRetraction (hr : 0 ≤ r) (x : E) :
    ‖x - radialRetraction r x‖ = max (‖x‖ - r) 0 := by
  by_cases hx : ‖x‖ = 0
  · simp [hx, hr]
  rcases le_total ‖x‖ r with h | h
  · rw [radialRetraction_of_norm_pos_of_norm_le ((norm_nonneg x).lt_of_ne' hx) h, sub_self,
      norm_zero, max_eq_right (sub_nonpos.2 h)]
  · have hsub : x - (r / ‖x‖) • x = (1 - r / ‖x‖) • x := by rw [sub_smul, one_smul]
    rw [radialRetraction_of_le_norm h, max_eq_left (sub_nonneg.2 h), hsub, norm_smul,
      Real.norm_of_nonneg (sub_nonneg.2 ((div_le_one ((norm_nonneg x).lt_of_ne' hx)).2 h)),
      sub_mul, one_mul, div_mul_cancel₀ _ hx]

/-- The centred radial retraction is at distance `|min (dist x x₀) r|` from its centre, provided
`x` is at nonzero distance from the centre or the radius is nonnegative. In the remaining case,
`dist x x₀ = 0` with `r < 0`, the point is sent to the centre. -/
theorem dist_centeredRadialRetraction_eq_abs_min {x₀ : E} (h : dist x x₀ ≠ 0 ∨ 0 ≤ r) :
    dist (centeredRadialRetraction x₀ r x) x₀ = |min (dist x x₀) r| := by
  rw [dist_eq_norm] at h
  simpa [centeredRadialRetraction_def, dist_eq_norm] using norm_radialRetraction_eq_abs_min h

/-- For nonnegative radius, the centred radial retraction is at distance `min (dist x x₀) r`
from its centre. -/
@[simp]
theorem dist_centeredRadialRetraction {x₀ : E} (hr : 0 ≤ r) (x : E) :
    dist (centeredRadialRetraction x₀ r x) x₀ = min (dist x x₀) r := by
  rw [dist_centeredRadialRetraction_eq_abs_min (.inr hr), abs_of_nonneg (le_min dist_nonneg hr)]

/-- For any radius, the centred radial retraction is at distance at most `|min (dist x x₀) r|`
from its centre, with equality except at a point at distance zero from the centre with a negative
radius (`TauCeti.dist_centeredRadialRetraction_eq_abs_min`). -/
theorem dist_centeredRadialRetraction_le_abs_min (x₀ : E) (r : ℝ) (x : E) :
    dist (centeredRadialRetraction x₀ r x) x₀ ≤ |min (dist x x₀) r| := by
  simpa [centeredRadialRetraction_def, dist_eq_norm] using
    norm_radialRetraction_le_abs_min r (x - x₀)

/-- For nonnegative radius, the radial retraction takes values in the closed ball of radius `r`. -/
theorem radialRetraction_mem_closedBall (hr : 0 ≤ r) (x : E) :
    radialRetraction r x ∈ closedBall (0 : E) r := by
  rw [mem_closedBall_zero_iff, norm_radialRetraction hr]
  exact min_le_right _ _

/-- The radial retraction at a nonnegative radius `r` is the radial retraction onto the unit ball
conjugated by the dilation by `r`. For `r = 0` both sides vanish. -/
theorem radialRetraction_eq_smul_radialRetraction_one (hr : 0 ≤ r) (x : E) :
    radialRetraction r x = r • radialRetraction 1 (r⁻¹ • x) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  rw [radialRetraction_def, radialRetraction_def, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hr.le), smul_smul, smul_smul]
  congr 1
  field_simp

/-- Truncating the radius at `‖x‖` does not change the radial retraction of `x`. -/
@[simp]
theorem radialRetraction_min_norm (r : ℝ) (x : E) :
    radialRetraction (min r ‖x‖) x = radialRetraction r x := by
  rcases le_total r ‖x‖ with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    rcases (norm_nonneg x).eq_or_lt with h0 | h0
    · rw [radialRetraction_of_norm_eq_zero h0.symm, radialRetraction_of_norm_eq_zero h0.symm]
    · rw [radialRetraction_of_norm_pos_of_norm_le h0 le_rfl,
        radialRetraction_of_norm_pos_of_norm_le h0 h]

/-- For nonnegative radii `s ≤ r`, the radial retractions of `x` at `r` and at `s` differ by a
vector of norm at most `min ‖x‖ r`: the difference is the part of `x` between the heights `s`
and `r`. -/
theorem norm_radialRetraction_sub_radialRetraction_le {s : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r)
    (x : E) : ‖radialRetraction r x - radialRetraction s x‖ ≤ min ‖x‖ r := by
  have h1 : min 1 (s / ‖x‖) ≤ min 1 (r / ‖x‖) :=
    min_le_min_left _ (div_le_div_of_nonneg_right hsr (norm_nonneg x))
  have h0 : 0 ≤ min 1 (s / ‖x‖) := le_min zero_le_one (div_nonneg hs (norm_nonneg x))
  rw [← norm_radialRetraction (hs.trans hsr) x, radialRetraction_def, radialRetraction_def,
    ← sub_smul, norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h1),
    Real.norm_of_nonneg (h0.trans h1)]
  gcongr
  linarith

/-- The centred radial retraction takes values in its closed ball. -/
theorem centeredRadialRetraction_mem_closedBall {x₀ : E} (hr : 0 ≤ r) (x : E) :
    centeredRadialRetraction x₀ r x ∈ closedBall x₀ r := by
  rw [mem_closedBall, dist_centeredRadialRetraction hr]
  exact min_le_right _ _

/-- The radial retraction is idempotent for nonnegative radius. -/
theorem radialRetraction_radialRetraction (hr : 0 ≤ r) (x : E) :
    radialRetraction r (radialRetraction r x) = radialRetraction r x := by
  by_cases hx : ‖x‖ = 0
  · simp [hx]
  rcases hr.eq_or_lt with rfl | hr
  · simp
  apply radialRetraction_of_norm_pos_of_norm_le
  · rw [norm_radialRetraction hr.le]
    exact lt_min (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)) hr
  · exact mem_closedBall_zero_iff.1 (radialRetraction_mem_closedBall hr.le x)

/-- For nonnegative radius, the radial retraction maps the whole space into the closed ball of
radius `r`. -/
theorem mapsTo_radialRetraction (hr : 0 ≤ r) :
    MapsTo (radialRetraction (E := E) r) univ (closedBall 0 r) :=
  fun x _ ↦ radialRetraction_mem_closedBall hr x

/-- The centred radial retraction maps the whole space into its closed ball. -/
theorem mapsTo_centeredRadialRetraction {x₀ : E} (hr : 0 ≤ r) :
    MapsTo (centeredRadialRetraction x₀ r) univ (closedBall x₀ r) :=
  fun x _ ↦ centeredRadialRetraction_mem_closedBall hr x

/-- The centred radial retraction maps a convex set `s` containing the centre into
`closedBall x₀ r ∩ s`: it moves each point along the segment towards `x₀`. -/
theorem mapsTo_centeredRadialRetraction_of_convex {x₀ : E} {s : Set E} (hr : 0 ≤ r)
    (hs : Convex ℝ s) (hx₀ : x₀ ∈ s) :
    MapsTo (centeredRadialRetraction x₀ r) s (closedBall x₀ r ∩ s) := fun x hx ↦
  ⟨centeredRadialRetraction_mem_closedBall hr x, hs.add_smul_sub_mem hx₀ hx
    ⟨le_min zero_le_one (div_nonneg hr (norm_nonneg _)), min_le_left _ _⟩⟩

/-- For nonnegative radius `r`, the radial retraction as a map into the closed ball of radius
`r`. -/
noncomputable def radialRetractionToClosedBall (hr : 0 ≤ r) (x : E) : closedBall (0 : E) r :=
  ⟨radialRetraction r x, radialRetraction_mem_closedBall hr x⟩

/-- The radial retraction into the closed ball of radius `r` is the radial retraction. -/
@[simp]
theorem coe_radialRetractionToClosedBall (hr : 0 ≤ r) (x : E) :
    (radialRetractionToClosedBall hr x : E) = radialRetraction r x :=
  (rfl)

/-- The norm of the radial retraction into the closed ball of radius `r` is `min ‖x‖ r`. -/
theorem norm_radialRetractionToClosedBall (hr : 0 ≤ r) (x : E) :
    ‖(radialRetractionToClosedBall hr x : E)‖ = min ‖x‖ r :=
  norm_radialRetraction hr x

/-- **The radial retraction onto a closed ball is `2`-Lipschitz.** -/
theorem lipschitzWith_radialRetraction (hr : 0 ≤ r) :
    LipschitzWith 2 (radialRetraction (E := E) r) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
  -- Both sides are symmetric in `x` and `y`, so let `x` be the point of larger norm.
  wlog hyx : ‖y‖ ≤ ‖x‖ generalizing x y
  · simpa only [norm_sub_rev] using this y x (le_of_not_ge hyx)
  by_cases hy0 : ‖y‖ = 0
  · -- A vector of norm zero is sent to zero, even if it is not the zero vector.
    rw [radialRetraction_of_norm_eq_zero hy0, sub_zero, norm_radialRetraction hr]
    exact (min_le_left _ _).trans (by linarith [norm_sub_norm_le x y, norm_nonneg (x - y)])
  have hy0 : 0 < ‖y‖ := (norm_nonneg y).lt_of_ne' hy0
  -- The retracted norms `min ‖y‖ r ≤ min ‖x‖ r` keep the order of the norms.
  have hnorm := min_le_min_right r hyx
  rw [← norm_radialRetraction hr y, ← norm_radialRetraction hr x] at hnorm
  simp only [radialRetraction_def, norm_smul] at hnorm ⊢
  -- The farther point is scaled by the smaller factor: `s ≤ t`.
  set s := min 1 (r / ‖x‖)
  set t := min 1 (r / ‖y‖)
  have hs0 : 0 ≤ s := le_min zero_le_one (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hst : s ≤ t := min_le_min_left _ (div_le_div_of_nonneg_left hr hy0 hyx)
  rw [Real.norm_of_nonneg hs0, Real.norm_of_nonneg (hs0.trans hst)] at hnorm
  -- Split `s • x - t • y` into a scaled difference and a radial correction along `y`.
  calc ‖s • x - t • y‖ = ‖s • (x - y) - (t - s) • y‖ := by
        rw [smul_sub, sub_smul, sub_sub_sub_cancel_right]
    _ ≤ ‖s • (x - y)‖ + ‖(t - s) • y‖ := norm_sub_le _ _
    _ = s * ‖x - y‖ + (t - s) * ‖y‖ := by
        simp only [norm_smul, Real.norm_of_nonneg hs0, Real.norm_of_nonneg (sub_nonneg.2 hst)]
    _ ≤ ‖x - y‖ + (‖x‖ - ‖y‖) := by
        linear_combination mul_le_of_le_one_left (norm_nonneg (x - y)) hs1 + hnorm +
          mul_le_of_le_one_left (sub_nonneg.2 hyx) hs1
    _ ≤ 2 * ‖x - y‖ := by linarith [norm_sub_norm_le x y]

/-- The radial retraction into the closed ball of radius `r` is continuous. -/
theorem continuous_radialRetractionToClosedBall (hr : 0 ≤ r) :
    Continuous (radialRetractionToClosedBall (E := E) hr) :=
  (lipschitzWith_radialRetraction hr).continuous.subtype_mk _

/-- Radial retraction onto a ball with an arbitrary centre is `2`-Lipschitz. -/
theorem lipschitzWith_centeredRadialRetraction {x₀ : E} (hr : 0 ≤ r) :
    LipschitzWith 2 (centeredRadialRetraction x₀ r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [centeredRadialRetraction, dist_eq_norm, add_sub_add_left_eq_sub, NNReal.coe_ofNat,
    sub_sub_sub_cancel_right] using
    (lipschitzWith_radialRetraction hr).dist_le_mul (x - x₀) (y - x₀)

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction into the closed ball of radius `r` fixes the points of that ball. -/
theorem radialRetractionToClosedBall_of_norm_le (hr : 0 ≤ r) (h : ‖x‖ ≤ r) :
    radialRetractionToClosedBall hr x = ⟨x, mem_closedBall_zero_iff.2 h⟩ :=
  Subtype.ext (radialRetraction_of_norm_le h)

/-- Scaling the radial retraction of `x` by `max ‖x‖ r` gives `r • x`: the radial retraction loses
only the radial information `max ‖x‖ r`. -/
theorem max_norm_smul_radialRetraction (r : ℝ) (x : E) :
    max ‖x‖ r • radialRetraction r x = r • x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases le_total ‖x‖ r with h | h
  · rw [max_eq_right h, radialRetraction_of_norm_le h]
  · rw [max_eq_left h, radialRetraction_of_le_norm h, smul_smul,
      mul_div_cancel₀ _ (norm_ne_zero_iff.2 hx)]

/-- A vector is its radial retraction onto the closed unit ball scaled back by `max ‖x‖ 1`. -/
theorem max_norm_one_smul_radialRetraction_one (x : E) :
    max ‖x‖ 1 • radialRetraction 1 x = x := by
  rw [max_norm_smul_radialRetraction, one_smul]

end Normed

end TauCeti

/-- **The radial retraction depends continuously on the radius and the point**: if `r` tends to
`r₀` and `f` tends to `y`, then the radial retraction of `f` by `r` tends to that of `y` by `r₀`,
provided `y` has nonzero norm or `r₀` is nonnegative. This can fail when `‖y‖ = 0` and `r₀ < 0`:
for `r₀ < 0`, `TauCeti.radialRetraction r₀` sends `0` to `0` but every vector of positive norm to
the sphere of radius `-r₀`. -/
theorem Filter.Tendsto.radialRetraction {E α : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {l : Filter α} {r : α → ℝ} {f : α → E} {r₀ : ℝ} {y : E}
    (hr : Tendsto r l (𝓝 r₀)) (h : ‖y‖ ≠ 0 ∨ 0 ≤ r₀) (hf : Tendsto f l (𝓝 y)) :
    Tendsto (fun a ↦ TauCeti.radialRetraction (r a) (f a)) l
      (𝓝 (TauCeti.radialRetraction r₀ y)) := by
  by_cases hy : ‖y‖ = 0
  · -- Near a point of norm zero, the retraction is bounded in norm by `|min ‖f‖ r|`, which
    -- tends to `|min 0 r₀| = 0`.
    rw [TauCeti.radialRetraction_of_norm_eq_zero hy]
    refine squeeze_zero_norm (fun a ↦ TauCeti.norm_radialRetraction_le_abs_min (r a) (f a)) ?_
    simpa [hy, min_eq_left (h.resolve_left (not_not.2 hy))] using (hf.norm.min hr).abs
  · simp only [TauCeti.radialRetraction_def]
    exact (tendsto_const_nhds.min (hr.div hf.norm hy)).smul hf

/-- The radial retraction is jointly continuous within a set in the radius and the point at every
point where the point has nonzero norm or the radius is nonnegative. -/
theorem ContinuousWithinAt.radialRetraction {E X : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] {r : X → ℝ} {f : X → E} {s : Set X} {x : X}
    (hr : ContinuousWithinAt r s x) (h : ‖f x‖ ≠ 0 ∨ 0 ≤ r x) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x ↦ TauCeti.radialRetraction (r x) (f x)) s x :=
  Filter.Tendsto.radialRetraction hr h hf

/-- The radial retraction is jointly continuous in the radius and the point at every point where
the point has nonzero norm or the radius is nonnegative. -/
theorem ContinuousAt.radialRetraction {E X : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {r : X → ℝ} {f : X → E} {x : X} (hr : ContinuousAt r x)
    (h : ‖f x‖ ≠ 0 ∨ 0 ≤ r x) (hf : ContinuousAt f x) :
    ContinuousAt (fun x ↦ TauCeti.radialRetraction (r x) (f x)) x :=
  Filter.Tendsto.radialRetraction hr h hf

/-- The radial retraction is jointly continuous on a set in the radius and the point, as long as
the radius is nonnegative at every point of the set where the point has norm zero. -/
theorem ContinuousOn.radialRetraction {E X : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {r : X → ℝ} {f : X → E} {s : Set X} (hr : ContinuousOn r s)
    (h : ∀ x ∈ s, ‖f x‖ ≠ 0 ∨ 0 ≤ r x) (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ TauCeti.radialRetraction (r x) (f x)) s :=
  fun x hx ↦ (hr x hx).radialRetraction (h x hx) (hf x hx)

/-- **The radial retraction depends continuously on the radius and the point**, as long as the
radius is nonnegative wherever the point has norm zero. -/
theorem Continuous.radialRetraction {E X : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {r : X → ℝ} {f : X → E} (hr : Continuous r)
    (h : ∀ x, ‖f x‖ ≠ 0 ∨ 0 ≤ r x) (hf : Continuous f) :
    Continuous fun x ↦ TauCeti.radialRetraction (r x) (f x) :=
  continuous_iff_continuousAt.2 fun x ↦ hr.continuousAt.radialRetraction (h x) hf.continuousAt

/-- **The centred radial retraction depends continuously on the centre, the radius and the
point**: if `c`, `r` and `f` tend to `x₀`, `r₀` and `y`, then the retraction of `f` by `r` about
`c` tends to that of `y` by `r₀` about `x₀`, provided `dist y x₀ ≠ 0` or `0 ≤ r₀`. -/
theorem Filter.Tendsto.centeredRadialRetraction {E α : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {l : Filter α} {c : α → E} {r : α → ℝ} {f : α → E} {x₀ : E} {r₀ : ℝ}
    {y : E} (hc : Tendsto c l (𝓝 x₀)) (hr : Tendsto r l (𝓝 r₀)) (h : dist y x₀ ≠ 0 ∨ 0 ≤ r₀)
    (hf : Tendsto f l (𝓝 y)) :
    Tendsto (fun a ↦ TauCeti.centeredRadialRetraction (c a) (r a) (f a)) l
      (𝓝 (TauCeti.centeredRadialRetraction x₀ r₀ y)) := by
  rw [dist_eq_norm] at h
  simp only [TauCeti.centeredRadialRetraction_def]
  exact hc.add (hr.radialRetraction h (hf.sub hc))

/-- The centred radial retraction is jointly continuous within a set in the centre, the radius
and the point at every point where the point is at nonzero distance from the centre or the radius
is nonnegative. -/
theorem ContinuousWithinAt.centeredRadialRetraction {E X : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] {c : X → E} {r : X → ℝ} {f : X → E} {s : Set X}
    {x : X} (hc : ContinuousWithinAt c s x) (hr : ContinuousWithinAt r s x)
    (h : dist (f x) (c x) ≠ 0 ∨ 0 ≤ r x) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x ↦ TauCeti.centeredRadialRetraction (c x) (r x) (f x)) s x :=
  Filter.Tendsto.centeredRadialRetraction hc hr h hf

/-- The centred radial retraction is jointly continuous in the centre, the radius and the point at
every point where the point is at nonzero distance from the centre or the radius is
nonnegative. -/
theorem ContinuousAt.centeredRadialRetraction {E X : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] {c : X → E} {r : X → ℝ} {f : X → E} {x : X}
    (hc : ContinuousAt c x) (hr : ContinuousAt r x) (h : dist (f x) (c x) ≠ 0 ∨ 0 ≤ r x)
    (hf : ContinuousAt f x) :
    ContinuousAt (fun x ↦ TauCeti.centeredRadialRetraction (c x) (r x) (f x)) x :=
  Filter.Tendsto.centeredRadialRetraction hc hr h hf

/-- The centred radial retraction is jointly continuous on a set in the centre, the radius and the
point, as long as the radius is nonnegative at every point of the set where the point lies at
distance zero from the centre. -/
theorem ContinuousOn.centeredRadialRetraction {E X : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] {c : X → E} {r : X → ℝ} {f : X → E} {s : Set X}
    (hc : ContinuousOn c s) (hr : ContinuousOn r s) (h : ∀ x ∈ s, dist (f x) (c x) ≠ 0 ∨ 0 ≤ r x)
    (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ TauCeti.centeredRadialRetraction (c x) (r x) (f x)) s :=
  fun x hx ↦ (hc x hx).centeredRadialRetraction (hr x hx) (h x hx) (hf x hx)

/-- **The centred radial retraction depends continuously on the centre, the radius and the
point**, as long as the radius is nonnegative wherever the point lies at distance zero from the
centre. -/
theorem Continuous.centeredRadialRetraction {E X : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] {c : X → E} {r : X → ℝ} {f : X → E}
    (hc : Continuous c) (hr : Continuous r) (h : ∀ x, dist (f x) (c x) ≠ 0 ∨ 0 ≤ r x)
    (hf : Continuous f) :
    Continuous fun x ↦ TauCeti.centeredRadialRetraction (c x) (r x) (f x) :=
  continuous_iff_continuousAt.2 fun x ↦
    hc.continuousAt.centeredRadialRetraction hr.continuousAt (h x) hf.continuousAt

/-- Precomposing with the centred radial retraction turns a map that is Lipschitz on a closed ball
into a globally Lipschitz map, at the cost of doubling the constant. -/
theorem LipschitzOnWith.comp_centeredRadialRetraction {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PseudoEMetricSpace F] {f : E → F} {c : ℝ≥0} {x₀ : E} {r : ℝ}
    (hf : LipschitzOnWith c f (closedBall x₀ r)) (hr : 0 ≤ r) :
    LipschitzWith (c * 2) (f ∘ TauCeti.centeredRadialRetraction x₀ r) :=
  lipschitzOnWith_univ.1 <| hf.comp
    (lipschitzOnWith_univ.2 (TauCeti.lipschitzWith_centeredRadialRetraction hr))
    (TauCeti.mapsTo_centeredRadialRetraction hr)

/-- Precomposing a map that is Lipschitz on a closed ball with the centred radial retraction keeps
the Lipschitz bound at the centre, with the same constant, because the retraction moves no point
farther from the centre. -/
theorem LipschitzOnWith.dist_comp_centeredRadialRetraction_le {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F] {f : E → F} {c : ℝ≥0}
    {x₀ : E} {r : ℝ} (hf : LipschitzOnWith c f (closedBall x₀ r)) (hr : 0 ≤ r) (x : E) :
    dist (f (TauCeti.centeredRadialRetraction x₀ r x)) (f x₀) ≤ c * dist x x₀ := by
  refine (hf.dist_le_mul _ (TauCeti.centeredRadialRetraction_mem_closedBall hr x) _
    (mem_closedBall_self hr)).trans (mul_le_mul_of_nonneg_left ?_ c.coe_nonneg)
  rw [TauCeti.dist_centeredRadialRetraction hr]
  exact min_le_left _ _

/-- Precomposing with the radial retraction turns a map that is Lipschitz on the closed ball of
radius `r` into a globally Lipschitz map, at the cost of doubling the constant. When the domain is
normed, the new map agrees with the old one on that ball, by
`TauCeti.radialRetraction_of_norm_le`. -/
theorem LipschitzOnWith.comp_radialRetraction {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PseudoEMetricSpace F] {f : E → F} {c : ℝ≥0} {r : ℝ}
    (hf : LipschitzOnWith c f (closedBall 0 r)) (hr : 0 ≤ r) :
    LipschitzWith (c * 2) (f ∘ TauCeti.radialRetraction r) := by
  simpa only [TauCeti.centeredRadialRetraction_zero] using
    hf.comp_centeredRadialRetraction hr

/-- Composing a Hölder function on a closed ball with the centred radial retraction gives a global
Hölder function with the same exponent and `2ᵅ` times the Hölder constant. -/
theorem HolderOnWith.comp_centeredRadialRetraction {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PseudoEMetricSpace F] {f : E → F} {c α : ℝ≥0} {x₀ : E} {r : ℝ}
    (hf : HolderOnWith c α f (closedBall x₀ r)) (hr : 0 ≤ r) :
    HolderWith (c * 2 ^ (α : ℝ)) α (f ∘ TauCeti.centeredRadialRetraction x₀ r) := by
  simpa only [mul_one] using hf.comp_holderWith
    (TauCeti.lipschitzWith_centeredRadialRetraction hr).holderWith
    (TauCeti.centeredRadialRetraction_mem_closedBall hr)
