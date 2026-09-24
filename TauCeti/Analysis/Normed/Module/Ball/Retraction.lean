/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The radial retraction onto a closed ball

In a real normed space, `TauCeti.radialRetraction r` scales a vector `x` by
`min 1 (r / ‖x‖)`. When `0 ≤ r`, it fixes the closed ball of radius `r` and pushes everything
outside it to the sphere of radius `r` along the ray through the origin. It is the standard device
for turning a map that is only Lipschitz near the origin into a globally Lipschitz map agreeing with
it near the origin, and it is used that way to cut off the nonlinearity of a differential equation
outside a small ball around an equilibrium.

For `0 ≤ r`, the retraction is `2`-Lipschitz in any normed space, and `2` is the constant carried
by `TauCeti.lipschitzWith_radialRetraction`; it is not optimal in every space (in a Hilbert space
the retraction is the metric projection onto a convex set, hence `1`-Lipschitz) but the exact
constant never matters for cutting off, where one is free to shrink the radius instead.

## Main declarations

* `TauCeti.radialRetraction`: scaling by `min 1 (r / ‖x‖)`; when `0 ≤ r`, this is the retraction
  onto the closed ball of radius `r` centred at the origin.
* `TauCeti.norm_radialRetraction`: for `0 ≤ r`, its norm is `min ‖x‖ r`.
* `TauCeti.radialRetraction_eventuallyEq_id`: inside the open ball, it agrees locally with the
  identity.
* `TauCeti.lipschitzWith_radialRetraction`: for `0 ≤ r`, it is `2`-Lipschitz.
* `LipschitzOnWith.comp_radialRetraction`: precomposing with it makes a map that is Lipschitz on
  the closed ball of radius `r` globally Lipschitz, with twice the constant.

## References

* D. G. de Figueiredo, L. A. Karlovitz, *On the radial projection in normed spaces*,
  Bull. Amer. Math. Soc. 73 (1967), 364–368.
-/

public section

open Filter Metric Set

open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ} {x y : E}

/-- Scale `x` by `min 1 (r / ‖x‖)`. When `0 ≤ r`, this is the **radial retraction** onto the closed
ball of radius `r` centred at the origin: vectors of norm at most `r` are fixed and the others are
pulled back along their ray to the sphere of radius `r`. -/
noncomputable def radialRetraction (r : ℝ) (x : E) : E := min 1 (r / ‖x‖) • x

@[simp]
theorem radialRetraction_zero (r : ℝ) : radialRetraction r (0 : E) = 0 := by
  simp [radialRetraction]

/-- The radial retraction fixes the closed ball of radius `r`. -/
@[simp]
theorem radialRetraction_of_norm_le (h : ‖x‖ ≤ r) : radialRetraction r x = x := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · rw [radialRetraction, norm_eq_zero.1 hx.symm, smul_zero]
  · rw [radialRetraction, min_eq_left ((le_div_iff₀ hx).2 (by linarith)), one_smul]

/-- The radial retraction agrees with the identity on a neighborhood of every point in the open
ball. -/
theorem radialRetraction_eventuallyEq_id (hx : ‖x‖ < r) :
    radialRetraction r =ᶠ[nhds x] id :=
  eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)) fun _ hy ↦
    radialRetraction_of_norm_le (mem_ball_zero_iff.1 hy).le

/-- Outside the closed ball of radius `r` the radial retraction scales by `r / ‖x‖`. -/
theorem radialRetraction_of_le_norm (h : r ≤ ‖x‖) :
    radialRetraction r x = (r / ‖x‖) • x := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · rw [radialRetraction, ← hx, div_zero, min_eq_right zero_le_one]
  · rw [radialRetraction, min_eq_right ((div_le_one hx).2 h)]

/-- For nonnegative radius, the radial retraction has norm `min ‖x‖ r`. -/
@[simp]
theorem norm_radialRetraction (hr : 0 ≤ r) (x : E) : ‖radialRetraction r x‖ = min ‖x‖ r := by
  rcases le_total ‖x‖ r with h | h
  · rw [radialRetraction_of_norm_le h, min_eq_left h]
  · rw [radialRetraction_of_le_norm h, norm_smul, Real.norm_eq_abs, min_eq_right h]
    rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
    · rw [← hx, mul_zero]
      exact (le_antisymm (h.trans_eq hx.symm) hr).symm
    · rw [abs_of_nonneg (by positivity), div_mul_cancel₀ _ hx.ne']

theorem radialRetraction_mem_closedBall (hr : 0 ≤ r) (x : E) :
    radialRetraction r x ∈ closedBall (0 : E) r := by
  rw [mem_closedBall_zero_iff, norm_radialRetraction hr]
  exact min_le_right _ _

/-- The radial retraction is idempotent for nonnegative radius. -/
theorem radialRetraction_radialRetraction (hr : 0 ≤ r) (x : E) :
    radialRetraction r (radialRetraction r x) = radialRetraction r x :=
  radialRetraction_of_norm_le (mem_closedBall_zero_iff.1 (radialRetraction_mem_closedBall hr x))

theorem mapsTo_radialRetraction (hr : 0 ≤ r) :
    MapsTo (radialRetraction (E := E) r) univ (closedBall 0 r) :=
  fun x _ ↦ radialRetraction_mem_closedBall hr x

/-- The radial retraction moves the point of larger norm by at most twice the distance between the
two points.  This is the asymmetric half of `TauCeti.lipschitzWith_radialRetraction`. -/
private theorem norm_radialRetraction_sub_le (hr : 0 ≤ r) (hyx : ‖y‖ ≤ ‖x‖) :
    ‖radialRetraction r x - radialRetraction r y‖ ≤ 2 * ‖x - y‖ := by
  rcases le_total ‖x‖ r with hxr | hrx
  · rw [radialRetraction_of_norm_le hxr, radialRetraction_of_norm_le (hyx.trans hxr)]
    linarith [norm_nonneg (x - y)]
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · -- A ball of radius `0` collapses the whole space to the origin.
    rw [radialRetraction_of_le_norm (hr0 ▸ norm_nonneg x),
      radialRetraction_of_le_norm (hr0 ▸ norm_nonneg y), ← hr0]
    simp [norm_nonneg]
  have hx0 : 0 < ‖x‖ := hr0.trans_le hrx
  rw [radialRetraction_of_le_norm hrx]
  have hxy : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
  rcases le_total ‖y‖ r with hyr | hry
  · -- The near point is fixed; the far one moves by `‖x‖ - r`.
    rw [radialRetraction_of_norm_le hyr]
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
    have hy0 : 0 < ‖y‖ := hr0.trans_le hry
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
  · rw [← norm_neg, neg_sub, ← norm_neg (x - y), neg_sub]
    exact norm_radialRetraction_sub_le hr h

end TauCeti

/-- Precomposing with the radial retraction turns a map that is Lipschitz on the closed ball of
radius `r` into a globally Lipschitz map, at the cost of doubling the constant.  The new map still
agrees with the old one on that ball, by `TauCeti.radialRetraction_of_norm_le`. -/
theorem LipschitzOnWith.comp_radialRetraction {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [PseudoMetricSpace F] {f : E → F} {c : ℝ≥0} {r : ℝ}
    (hf : LipschitzOnWith c f (closedBall 0 r)) (hr : 0 ≤ r) :
    LipschitzWith (c * 2) (f ∘ TauCeti.radialRetraction r) :=
  lipschitzOnWith_univ.1 <| hf.comp
    (lipschitzOnWith_univ.2 (TauCeti.lipschitzWith_radialRetraction hr))
    (TauCeti.mapsTo_radialRetraction hr)
