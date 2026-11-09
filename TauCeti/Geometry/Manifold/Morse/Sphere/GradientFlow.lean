/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.ExponentialConvergence
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient

/-!
# The negative gradient flow of the height function on the sphere

Let `h` be the height function on the unit sphere `Sⁿ` in the direction of a unit vector `v`
(`TauCeti.sphereHeight`), with the north pole `v` as its maximum and the south pole `-v` as its
minimum. This file follows the negative gradient trajectories `γ` of `h` and tests on them the
convergence theorems for negative gradient flows of Morse functions.

* **Convergence to the south pole, for every metric.** For any `C¹` Riemannian metric on `Sⁿ`, the
  trajectory of `-grad h` through a point `x ≠ v` converges to the south pole
  (`TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_sphereHeight`). The general theorem
  `TauCeti.IsMorse.exists_tendsto_maximalIntegralCurve_neg_mgradient` makes it converge to one of
  the two poles, and it cannot converge to the north pole because `h` decreases along it from the
  value `h x < 1`. So the north pole, although critical, is the limit of no trajectory starting
  elsewhere (`TauCeti.not_tendsto_maximalIntegralCurve_neg_mgradient_sphereHeight_self`).
* **The exact energy law for the round metric.** For the round metric the gradient of `h`
  has squared length `1 - h²` (`TauCeti.norm_mgradient_sphereHeight_sq`), so along `γ` the height
  satisfies `h' = -(1 - h²)`. Hence `(1 + h) / (1 - h)` decays exactly like `exp (-2 t)`
  (`TauCeti.one_add_sphereHeight_div_one_sub_maximalIntegralCurve_neg_mgradient`). If `u` is the
  angle of `γ t` from the south pole, then `h = -cos u` and `(1 + h) / (1 - h) = tan² (u / 2)`:
  this is the solution `tan (u / 2) = tan (u₀ / 2) exp (-t)` of the meridian equation
  `u' = -sin u`.
* **The rate `exp (-t)` is exact.** The Riemannian distance from `γ t` to the south pole is at most
  a constant times `exp (-t)` for large `t`
  (`TauCeti.exists_riemannianEDist_le_mul_exp_neg_maximalIntegralCurve_neg_mgradient_sphereHeight`),
  and, when `x` is not a pole, at least a positive constant times `exp (-t)` for all `t ≥ 0`
  (`TauCeti.exists_mul_exp_neg_le_riemannianEDist_maximalIntegralCurve_neg_mgradient_sphereHeight`).
  So no rate `exp (-μ t)` with `μ > 1` holds
  (`TauCeti.not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sphereHeight`).
  The optimal rate `1` matches the eigenvalue `1` of the Hessian of `h` at the south pole for the
  round metric, in whose normal coordinates `h = -1 + |y|² / 2 + O(|y|⁴)`.

The upper bound is the general estimate
`TauCeti.exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient`, which bounds the
distance by a multiple of `sqrt (h (γ t) + 1)`, combined with the energy law. The lower bound uses
that the chord in `E` is at most the round distance (`TauCeti.edist_le_riemannianEDist_sphere`),
and that the squared chord from `γ t` to the south pole is `2 (1 + h (γ t))`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2 and §3, for the height function on the sphere and its gradient flow.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2, for the convergence of gradient trajectories.
-/

public section

open Bundle Filter Metric Module Set Topology TauCeti.Manifold
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {v x : sphere (0 : E) 1}

/-! ### Convergence for an arbitrary metric -/

section AnyMetric

variable [RiemannianBundle (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y)]
  [IsContMDiffRiemannianBundle (𝓡 n) 1 (EuclideanSpace ℝ (Fin n))
    (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y)]

/-- Every negative gradient trajectory of the height function exists for all positive time. -/
private theorem Ici_subset_maximalIntegralCurveInterval_neg_mgradient_sphereHeight :
    Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient (𝓡 n) (sphereHeight v)) x := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  exact Ici_subset_maximalIntegralCurveInterval_neg_mgradient isCompact_univ (mapsTo_univ _ _)
    (contMDiff_sphereHeight (n := n) v)

/-- Forward in time, the height along a negative gradient trajectory stays at most its initial
value. -/
private theorem sphereHeight_maximalIntegralCurve_neg_mgradient_le {t : ℝ} (ht : 0 ≤ t) :
    sphereHeight v (maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x t) ≤
      sphereHeight v x :=
  mapsTo_maximalIntegralCurve_neg_mgradient_preimage_Iic (contMDiff_sphereHeight (n := n) v)
    ⟨Ici_subset_maximalIntegralCurveInterval_neg_mgradient_sphereHeight ht, ht⟩

/-- **Negative gradient trajectories of the height function converge to the south pole.** For any
`C¹` Riemannian metric on the sphere, the trajectory of `-grad h` through any point other than the
north pole converges to the south pole. -/
theorem tendsto_maximalIntegralCurve_neg_mgradient_sphereHeight (hx : x ≠ v) :
    Tendsto (maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x) atTop (𝓝 (-v)) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hcont := (contMDiff_sphereHeight (n := n) (m := 0) v).continuous
  obtain ⟨p, hp, hconv⟩ :=
    (isMorse_sphereHeight (n := n) v).exists_tendsto_maximalIntegralCurve_neg_mgradient
      hcont.isProperMap (isCompact_range hcont).bddBelow x
  rw [criticalPoints_sphereHeight] at hp
  rcases hp with rfl | rfl
  · -- The height decreases along the forward trajectory, so it stays at most `h x < h v`.
    have hle : ∀ᶠ t in atTop, sphereHeight p (maximalIntegralCurve
        (-mgradient (𝓡 n) (sphereHeight p)) x t) ≤ sphereHeight p x := by
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact sphereHeight_maximalIntegralCurve_neg_mgradient_le (n := n) ht
    exact absurd (le_of_tendsto ((hcont.tendsto p).comp hconv) hle)
      (sphereHeight_lt_self hx).not_ge
  · exact hconv

/-- **The north pole attracts no other trajectory.** For any `C¹` Riemannian metric on the sphere,
the trajectory of `-grad h` through a point other than the north pole does not converge to the
north pole, although the north pole is a critical point of `h`. -/
theorem not_tendsto_maximalIntegralCurve_neg_mgradient_sphereHeight_self (hx : x ≠ v) :
    ¬Tendsto (maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x) atTop (𝓝 v) :=
  fun h ↦ ne_neg_of_mem_unit_sphere ℝ v
    (tendsto_nhds_unique h (tendsto_maximalIntegralCurve_neg_mgradient_sphereHeight hx))

end AnyMetric

/-! ### The round metric -/

section Round

/-- The round metric is in particular `C¹`. -/
private theorem isContMDiffRiemannianBundle_one_sphere :
    IsContMDiffRiemannianBundle (𝓡 n) 1 (EuclideanSpace ℝ (Fin n))
      (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y) :=
  IsContMDiffRiemannianBundle.of_le le_top

attribute [local instance] isContMDiffRiemannianBundle_one_sphere

/-- For the round metric, the gradient of the height function has squared length `1 - h²`. -/
theorem norm_mgradient_sphereHeight_sq (v y : sphere (0 : E) 1) :
    ‖mgradient (𝓡 n) (sphereHeight v) y‖ ^ 2 = 1 - sphereHeight v y ^ 2 := by
  have h : sphereHeight v = fun q : sphere (0 : E) 1 ↦ inner ℝ (v : E) (q : E) :=
    funext fun q ↦ by rw [sphereHeight_apply, real_inner_comm]
  rw [h, norm_mgradient_inner_coe_sphere_sq, norm_eq_of_mem_sphere v, one_pow]

/-- Along a negative gradient trajectory for the round metric, the height satisfies
`h' = -(1 - h²)`. -/
private theorem hasDerivAt_sphereHeight_maximalIntegralCurve {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s ↦ sphereHeight v (maximalIntegralCurve
        (-mgradient (𝓡 n) (sphereHeight v)) x s))
      (-(1 - sphereHeight v (maximalIntegralCurve
        (-mgradient (𝓡 n) (sphereHeight v)) x t) ^ 2)) t := by
  rw [← norm_mgradient_sphereHeight_sq (n := n)]
  exact hasDerivAt_comp_maximalIntegralCurve_neg_mgradient (contMDiff_sphereHeight (n := n) v)
    (Ici_subset_maximalIntegralCurveInterval_neg_mgradient_sphereHeight ht)

/-- **The energy law of the height function for the round metric.** Along the trajectory `γ` of
`-grad h` through a point `x` other than the north pole, `(1 + h (γ t)) / (1 - h (γ t))` is
`(1 + h x) / (1 - h x)` times `exp (-2 t)` for every `t ≥ 0`. With `u` the angle from the south
pole, the left side is `tan² (u / 2)`. -/
theorem one_add_sphereHeight_div_one_sub_maximalIntegralCurve_neg_mgradient (hx : x ≠ v) {t : ℝ}
    (ht : 0 ≤ t) :
    (1 + sphereHeight v (maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x t)) /
        (1 - sphereHeight v (maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x t)) =
      (1 + sphereHeight v x) / (1 - sphereHeight v x) * Real.exp (-(2 * t)) := by
  set h : ℝ → ℝ := fun s ↦ sphereHeight v (maximalIntegralCurve
    (-mgradient (𝓡 n) (sphereHeight v)) x s) with h_def
  have hint :=
    Ici_subset_maximalIntegralCurveInterval_neg_mgradient_sphereHeight (n := n) (v := v) (x := x)
  have h0 : h 0 = sphereHeight v x := by
    simp only [h_def, maximalIntegralCurve_zero (hint self_mem_Ici)]
  -- Forward in time the height stays at most `h x < 1`.
  have hlt : ∀ s, 0 ≤ s → h s < 1 := fun s hs ↦
    (sphereHeight_maximalIntegralCurve_neg_mgradient_le hs).trans_lt
      ((sphereHeight_lt_self hx).trans_eq (sphereHeight_self v))
  -- `g = (1 + h) / (1 - h) * exp (2 s)` has derivative zero on `[0, ∞)`.
  set g : ℝ → ℝ := fun s ↦ (1 + h s) / (1 - h s) * Real.exp (2 * s) with g_def
  have hg : ∀ s, 0 ≤ s → HasDerivAt g 0 s := by
    intro s hs
    have hd : HasDerivAt h (-(1 - h s ^ 2)) s :=
      hasDerivAt_sphereHeight_maximalIntegralCurve (n := n) (v := v) (x := x) hs
    have hne : 1 - h s ≠ 0 := (sub_pos.2 (hlt s hs)).ne'
    refine (((hd.const_add 1).div (hd.const_sub 1) hne).mul
      ((hasDerivAt_id' s).const_mul 2).exp).congr_deriv ?_
    simp only [Pi.div_apply]
    field_simp
    ring
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := t)
    (fun s hs ↦ (hg s hs.1).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hg s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  simp only [g_def, h0, mul_zero, Real.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- **The distance to the south pole decays like `exp (-t)`.** For the round metric, the
Riemannian distance from the trajectory of `-grad h` through a point other than the north pole to
the south pole is at most a constant times `exp (-t)` for all large `t`. -/
theorem exists_riemannianEDist_le_mul_exp_neg_maximalIntegralCurve_neg_mgradient_sphereHeight
    (hx : x ≠ v) :
    ∃ C, ∀ᶠ t in atTop,
      Manifold.riemannianEDist (𝓡 n) (maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x t)
        (-v) ≤ ENNReal.ofReal (C * Real.exp (-t)) := by
  set γ := maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x
  set R := (1 + sphereHeight v x) / (1 - sphereHeight v x)
  obtain ⟨K, hK0, hK⟩ := exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    (isManifoldNondegenerateCriticalPoint_sphereHeight_neg v)
    Ici_subset_maximalIntegralCurveInterval_neg_mgradient_sphereHeight
    (tendsto_maximalIntegralCurve_neg_mgradient_sphereHeight hx)
    (contMDiff_sphereHeight (n := n) v)
  refine ⟨K * √(2 * R), ?_⟩
  filter_upwards [hK, eventually_ge_atTop 0] with t hKt ht
  refine hKt.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [sphereHeight_neg_self, sub_neg_eq_add, add_comm, mul_assoc]
  gcongr
  -- `1 + h = R exp (-2 t) (1 - h) ≤ 2 R exp (-2 t)`, whose square root is `√(2 R) exp (-t)`.
  have hlaw := one_add_sphereHeight_div_one_sub_maximalIntegralCurve_neg_mgradient (n := n) hx ht
  have hlt : sphereHeight v (γ t) < 1 :=
    (sphereHeight_maximalIntegralCurve_neg_mgradient_le ht).trans_lt
      ((sphereHeight_lt_self hx).trans_eq (sphereHeight_self v))
  have hge := neg_one_le_sphereHeight v (γ t)
  have hR : 0 ≤ R :=
    div_nonneg (by linarith [neg_one_le_sphereHeight v x]) (by linarith [sphereHeight_le_one v x])
  have heq : 1 + sphereHeight v (γ t) = R * Real.exp (-(2 * t)) * (1 - sphereHeight v (γ t)) := by
    rw [← hlaw, div_mul_cancel₀ _ (sub_pos.2 hlt).ne']
  have hexp : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [show √(2 * R) * Real.exp (-t) = √(2 * R * Real.exp (-t) ^ 2) by
    rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]]
  refine Real.sqrt_le_sqrt ?_
  rw [heq, ← hexp]
  have : 0 ≤ R * Real.exp (-(2 * t)) := by positivity
  nlinarith

/-- **The distance to the south pole decays no faster than `exp (-t)`.** For the round metric, if
`x` is neither pole, the Riemannian distance from the trajectory of `-grad h` through `x` to the
south pole is at least a positive constant times `exp (-t)` for every `t ≥ 0`. -/
theorem exists_mul_exp_neg_le_riemannianEDist_maximalIntegralCurve_neg_mgradient_sphereHeight
    (hx : x ≠ v) (hx' : x ≠ -v) :
    ∃ c > 0, ∀ t, 0 ≤ t → ENNReal.ofReal (c * Real.exp (-t)) ≤
      Manifold.riemannianEDist (𝓡 n) (maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x t)
        (-v) := by
  set γ := maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x
  have h₀lt : sphereHeight v x < 1 := (sphereHeight_lt_self hx).trans_eq (sphereHeight_self v)
  have h₀gt : -1 < sphereHeight v x := (sphereHeight_neg_self v).symm.trans_lt
    (sphereHeight_neg_lt hx')
  set R := (1 + sphereHeight v x) / (1 - sphereHeight v x)
  have hR : 0 < R := div_pos (by linarith) (by linarith)
  have hc : 0 < 2 * R * (1 - sphereHeight v x) := by
    have : 0 < 1 - sphereHeight v x := by linarith
    positivity
  refine ⟨√(2 * R * (1 - sphereHeight v x)), Real.sqrt_pos.2 hc, fun t ht ↦ ?_⟩
  -- The round distance is at least the chord, whose square is `2 (1 + h (γ t))`.
  refine le_trans ?_ (edist_le_riemannianEDist_sphere (γ t) (-v))
  rw [Subtype.edist_eq, edist_dist, coe_neg_sphere, dist_eq_norm, sub_neg_eq_add]
  refine ENNReal.ofReal_le_ofReal (le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_)
  have hlaw := one_add_sphereHeight_div_one_sub_maximalIntegralCurve_neg_mgradient (n := n) hx ht
  have hle : sphereHeight v (γ t) ≤ sphereHeight v x :=
    sphereHeight_maximalIntegralCurve_neg_mgradient_le (n := n) ht
  have heq : 1 + sphereHeight v (γ t) = R * Real.exp (-(2 * t)) * (1 - sphereHeight v (γ t)) := by
    rw [← hlaw, div_mul_cancel₀ _ (sub_pos.2 (hle.trans_lt h₀lt)).ne']
  have hnorm : ‖((γ t : sphere (0 : E) 1) : E) + v‖ ^ 2 = 2 * (1 + sphereHeight v (γ t)) := by
    rw [norm_add_sq_real, norm_eq_of_mem_sphere, norm_eq_of_mem_sphere v, sphereHeight_apply]
    ring
  have hexp : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hnorm, heq, mul_pow, Real.sq_sqrt hc.le, ← hexp]
  have : 0 ≤ R * Real.exp (-(2 * t)) := by positivity
  nlinarith

/-- **No exponential rate faster than `exp (-t)`.** For the round metric, if `x` is neither pole,
then for every `μ > 1` the Riemannian distance from the trajectory of `-grad h` through `x` to the
south pole is not eventually bounded by any multiple of `exp (-μ t)`. Thus the exponent `1` in
`exists_riemannianEDist_le_mul_exp_neg_maximalIntegralCurve_neg_mgradient_sphereHeight` is
optimal. -/
theorem not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sphereHeight
    (hx : x ≠ v) (hx' : x ≠ -v) {μ : ℝ} (hμ : 1 < μ) :
    ¬∃ C, ∀ᶠ t in atTop,
      Manifold.riemannianEDist (𝓡 n) (maximalIntegralCurve (-mgradient (𝓡 n) (sphereHeight v)) x t)
        (-v) ≤ ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  rintro ⟨C, hC⟩
  obtain ⟨c, hc, hlow⟩ :=
    exists_mul_exp_neg_le_riemannianEDist_maximalIntegralCurve_neg_mgradient_sphereHeight
      (n := n) hx hx'
  -- `C exp (-(μ - 1) t)` tends to `0`, so it eventually drops below `c`.
  have hlim : Tendsto (fun t ↦ C * Real.exp (-((μ - 1) * t))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (sub_pos.2 hμ))).const_mul C
  obtain ⟨t, hCt, ht0, hsmall⟩ :=
    (hC.and ((eventually_ge_atTop 0).and (hlim.eventually (gt_mem_nhds hc)))).exists
  rcases (ENNReal.ofReal_le_ofReal_iff'.1 ((hlow t ht0).trans hCt)) with h | h
  · have hct : c ≤ C * Real.exp (-((μ - 1) * t)) :=
      calc c = c * Real.exp (-t) * Real.exp t := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ C * Real.exp (-(μ * t)) * Real.exp t :=
            mul_le_mul_of_nonneg_right h (Real.exp_pos t).le
        _ = C * Real.exp (-((μ - 1) * t)) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
    exact hsmall.not_ge hct
  · exact h.not_gt (by positivity)

end Round

end TauCeti
