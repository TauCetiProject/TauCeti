/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.norm_radialRetraction`: for `0 ≤ r`, its norm is `min ‖x‖ r`.
* `TauCeti.radialRetraction_eventuallyEq_id`: inside the open ball, it agrees locally with the
  identity.
* `TauCeti.lipschitzWith_radialRetraction`: for `0 ≤ r`, it is `2`-Lipschitz.
* `Continuous.radialRetraction`: it depends jointly continuously on a nonnegative radius and the
  point.
* `TauCeti.dist_centeredRadialRetraction`: for `0 ≤ r`, the distance from the centre is
  `min (dist x x₀) r`.
* `TauCeti.lipschitzWith_centeredRadialRetraction`: for `0 ≤ r`, the centred retraction is
  `2`-Lipschitz.
* `LipschitzOnWith.comp_centeredRadialRetraction`: precomposing with the centred retraction makes a
  map that is Lipschitz on the closed ball globally Lipschitz, with twice the constant.
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

open Filter Metric Set

open scoped NNReal

namespace TauCeti

variable {E : Type*} {r : ℝ} {x y : E}

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

/-- For nonnegative radius, the radial retraction has norm `min ‖x‖ r`. -/
@[simp]
theorem norm_radialRetraction (hr : 0 ≤ r) (x : E) : ‖radialRetraction r x‖ = min ‖x‖ r := by
  by_cases hx : ‖x‖ = 0
  · simp [hx, hr]
  rw [radialRetraction, norm_smul, Real.norm_of_nonneg (by positivity),
    min_mul_of_nonneg _ _ (norm_nonneg x), one_mul, div_mul_cancel₀ _ hx]

/-- For nonnegative radius, the centred radial retraction is at distance `min (dist x x₀) r`
from its centre. -/
@[simp]
theorem dist_centeredRadialRetraction {x₀ : E} (hr : 0 ≤ r) (x : E) :
    dist (centeredRadialRetraction x₀ r x) x₀ = min (dist x x₀) r := by
  rw [centeredRadialRetraction, dist_eq_norm, add_sub_cancel_left, norm_radialRetraction hr,
    dist_eq_norm]

theorem radialRetraction_mem_closedBall (hr : 0 ≤ r) (x : E) :
    radialRetraction r x ∈ closedBall (0 : E) r := by
  rw [mem_closedBall_zero_iff, norm_radialRetraction hr]
  exact min_le_right _ _

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
  · simp [radialRetraction]
  apply radialRetraction_of_norm_pos_of_norm_le
  · rw [norm_radialRetraction hr.le]
    exact lt_min (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)) hr
  · exact mem_closedBall_zero_iff.1 (radialRetraction_mem_closedBall hr.le x)

theorem mapsTo_radialRetraction (hr : 0 ≤ r) :
    MapsTo (radialRetraction (E := E) r) univ (closedBall 0 r) :=
  fun x _ ↦ radialRetraction_mem_closedBall hr x

/-- The centred radial retraction maps the whole space into its closed ball. -/
theorem mapsTo_centeredRadialRetraction {x₀ : E} (hr : 0 ≤ r) :
    MapsTo (centeredRadialRetraction x₀ r) univ (closedBall x₀ r) :=
  fun x _ ↦ centeredRadialRetraction_mem_closedBall hr x

/-- The radial retraction distorts distance by at most a factor of two when the points are
ordered by norm. This is the asymmetric half of `TauCeti.lipschitzWith_radialRetraction`. -/
private theorem norm_radialRetraction_sub_le (hr : 0 ≤ r) (hyx : ‖y‖ ≤ ‖x‖) :
    ‖radialRetraction r x - radialRetraction r y‖ ≤ 2 * ‖x - y‖ := by
  by_cases hy0 : ‖y‖ = 0
  · -- A vector of norm zero is sent to zero, even if it is not the zero vector.
    rw [radialRetraction_of_norm_eq_zero hy0, sub_zero, norm_radialRetraction hr]
    exact (min_le_left _ _).trans (by linarith [norm_sub_norm_le x y, norm_nonneg (x - y)])
  have hy0 : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
  have hx0 : 0 < ‖x‖ := hy0.trans_le hyx
  rcases le_total ‖x‖ r with hxr | hrx
  · rw [radialRetraction_of_norm_pos_of_norm_le hx0 hxr,
      radialRetraction_of_norm_pos_of_norm_le hy0 (hyx.trans hxr)]
    linarith [norm_nonneg (x - y)]
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · -- A ball of radius `0` collapses the whole space to the origin.
    simp [← hr0, radialRetraction, norm_nonneg]
  rw [radialRetraction_of_le_norm hrx]
  have hxy : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
  rcases le_total ‖y‖ r with hyr | hry
  · -- The near point is fixed; the far one moves by `‖x‖ - r`.
    rw [radialRetraction_of_norm_pos_of_norm_le hy0 hyr]
    have hsplit : (r / ‖x‖) • x - y = ((r / ‖x‖) • x - x) + (x - y) := by abel
    have hmove : ‖(r / ‖x‖) • x - x‖ = ‖x‖ - r := by
      calc
        ‖(r / ‖x‖) • x - x‖ = ‖(r / ‖x‖ - 1) • x‖ := by rw [sub_smul, one_smul]
        _ = ‖x‖ - r := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonpos (sub_nonpos.2 ((div_le_one hx0).2 hrx)), neg_sub, sub_mul, one_mul,
            div_mul_cancel₀ _ hx0.ne']
    calc ‖(r / ‖x‖) • x - y‖ ≤ ‖(r / ‖x‖) • x - x‖ + ‖x - y‖ := hsplit ▸ norm_add_le _ _
      _ = (‖x‖ - r) + ‖x - y‖ := by rw [hmove]
      _ ≤ 2 * ‖x - y‖ := by linarith
  · -- Both points are pushed to the sphere; compare them through the ray of the near one.
    rw [radialRetraction_of_le_norm hry]
    have hsplit : (r / ‖x‖) • x - (r / ‖y‖) • y
        = (r / ‖y‖) • (x - y) + (r / ‖x‖ - r / ‖y‖) • x := by
      rw [sub_smul, smul_sub]; abel
    have habs : |r / ‖x‖ - r / ‖y‖| = r / ‖y‖ - r / ‖x‖ := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by gcongr))]
    have hcone : (r / ‖y‖ - r / ‖x‖) * ‖x‖ = r / ‖y‖ * (‖x‖ - ‖y‖) := by
      field_simp
    have hle1 : r / ‖y‖ ≤ 1 := (div_le_one hy0).2 hry
    have hnn : (0 : ℝ) ≤ r / ‖y‖ := by positivity
    calc ‖(r / ‖x‖) • x - (r / ‖y‖) • y‖
        ≤ ‖(r / ‖y‖) • (x - y)‖ + ‖(r / ‖x‖ - r / ‖y‖) • x‖ := hsplit ▸ norm_add_le _ _
      _ = r / ‖y‖ * ‖x - y‖ + r / ‖y‖ * (‖x‖ - ‖y‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, habs, hcone,
            abs_of_nonneg hnn]
      _ ≤ 1 * ‖x - y‖ + 1 * ‖x - y‖ := by gcongr
      _ = 2 * ‖x - y‖ := by ring

/-- **The radial retraction onto a closed ball is `2`-Lipschitz.** -/
theorem lipschitzWith_radialRetraction (hr : 0 ≤ r) :
    LipschitzWith 2 (radialRetraction (E := E) r) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact norm_radialRetraction_sub_le hr h
  · simpa only [norm_sub_rev] using norm_radialRetraction_sub_le hr h

/-- Radial retraction onto a ball with an arbitrary centre is `2`-Lipschitz. -/
theorem lipschitzWith_centeredRadialRetraction {x₀ : E} (hr : 0 ≤ r) :
    LipschitzWith 2 (centeredRadialRetraction x₀ r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [centeredRadialRetraction, dist_eq_norm, add_sub_add_left_eq_sub, NNReal.coe_ofNat,
    sub_sub_sub_cancel_right] using
    (lipschitzWith_radialRetraction hr).dist_le_mul (x - x₀) (y - x₀)

end Seminormed

end TauCeti

/-- **The radial retraction depends continuously on the radius and the point**, as long as the
radius stays nonnegative. For a negative radius it is discontinuous at the origin in a nontrivial
normed space. -/
theorem Continuous.radialRetraction {E X : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {r : X → ℝ} {f : X → E} (hr : Continuous r) (hr0 : ∀ x, 0 ≤ r x)
    (hf : Continuous f) : Continuous fun x ↦ TauCeti.radialRetraction (r x) (f x) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : ‖f x‖ = 0
  · -- Near a point sent to the origin, the retraction is bounded in norm by `‖f‖`.
    rw [ContinuousAt, TauCeti.radialRetraction_of_norm_eq_zero hx]
    exact squeeze_zero_norm (fun y ↦ (TauCeti.norm_radialRetraction (hr0 y) (f y)).trans_le
      (min_le_left _ _)) (by simpa [hx] using (hf.tendsto x).norm)
  · simp only [TauCeti.radialRetraction_def]
    exact (continuousAt_const.min (hr.continuousAt.div hf.continuousAt.norm
      hx)).smul hf.continuousAt

/-- Precomposing with the centred radial retraction turns a map that is Lipschitz on a closed ball
into a globally Lipschitz map, at the cost of doubling the constant. -/
theorem LipschitzOnWith.comp_centeredRadialRetraction {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PseudoEMetricSpace F] {f : E → F} {c : ℝ≥0} {x₀ : E} {r : ℝ}
    (hf : LipschitzOnWith c f (closedBall x₀ r)) (hr : 0 ≤ r) :
    LipschitzWith (c * 2) (f ∘ TauCeti.centeredRadialRetraction x₀ r) :=
  lipschitzOnWith_univ.1 <| hf.comp
    (lipschitzOnWith_univ.2 (TauCeti.lipschitzWith_centeredRadialRetraction hr))
    (TauCeti.mapsTo_centeredRadialRetraction hr)

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
